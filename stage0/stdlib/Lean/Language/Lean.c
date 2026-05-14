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
extern lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
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
lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotLeaf;
lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_parseHeader(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object*);
lean_object* l_Lean_Elab_processHeaderCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_trace_profiler_serve;
extern lean_object* l_Lean_instInhabitedTraceState_default;
lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "experimental"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 138, 38, 81, 136, 39, 83, 32)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(93, 242, 21, 84, 145, 94, 84, 207)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "no-op, deprecated"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__3_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 222, 85, 59, 197, 113, 89, 237)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__0_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(24, 94, 31, 95, 17, 215, 109, 107)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__1_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 160, 244, 111, 154, 6, 107, 146)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_443_, lean_object* v_decl_444_, lean_object* v_ref_445_){
_start:
{
lean_object* v_defValue_447_; lean_object* v_descr_448_; lean_object* v_deprecation_x3f_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_defValue_447_ = lean_ctor_get(v_decl_444_, 0);
v_descr_448_ = lean_ctor_get(v_decl_444_, 1);
v_deprecation_x3f_449_ = lean_ctor_get(v_decl_444_, 2);
v___x_450_ = lean_alloc_ctor(1, 0, 1);
v___x_451_ = lean_unbox(v_defValue_447_);
lean_ctor_set_uint8(v___x_450_, 0, v___x_451_);
lean_inc(v_deprecation_x3f_449_);
lean_inc_ref(v_descr_448_);
lean_inc_n(v_name_443_, 2);
v___x_452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_452_, 0, v_name_443_);
lean_ctor_set(v___x_452_, 1, v_ref_445_);
lean_ctor_set(v___x_452_, 2, v___x_450_);
lean_ctor_set(v___x_452_, 3, v_descr_448_);
lean_ctor_set(v___x_452_, 4, v_deprecation_x3f_449_);
v___x_453_ = lean_register_option(v_name_443_, v___x_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_453_, 0);
lean_dec(v_unused_462_);
v___x_455_ = v___x_453_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_dec(v___x_453_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_inc(v_defValue_447_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_name_443_);
lean_ctor_set(v___x_457_, 1, v_defValue_447_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_name_443_);
v_a_463_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_453_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_453_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_471_, lean_object* v_decl_472_, lean_object* v_ref_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_471_, v_decl_472_, v_ref_473_);
lean_dec_ref(v_decl_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_494_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_495_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_496_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_493_, v___x_494_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_498_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_unsigned_to_nat(32u);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_502_ = ((size_t)5ULL);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_unsigned_to_nat(32u);
v___x_505_ = lean_mk_empty_array_with_capacity(v___x_504_);
v___x_506_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_507_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_503_);
lean_ctor_set(v___x_507_, 3, v___x_503_);
lean_ctor_set_usize(v___x_507_, 4, v___x_502_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; lean_object* v_infoState_511_; lean_object* v_trees_512_; lean_object* v___x_513_; lean_object* v_infoState_514_; lean_object* v_env_515_; lean_object* v_messages_516_; lean_object* v_scopes_517_; lean_object* v_usedQuotCtxts_518_; lean_object* v_nextMacroScope_519_; lean_object* v_maxRecDepth_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_traceState_523_; lean_object* v_snapshotTasks_524_; lean_object* v_newDecls_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_546_; 
v___x_510_ = lean_st_ref_get(v___y_508_);
v_infoState_511_ = lean_ctor_get(v___x_510_, 8);
lean_inc_ref(v_infoState_511_);
lean_dec(v___x_510_);
v_trees_512_ = lean_ctor_get(v_infoState_511_, 2);
lean_inc_ref(v_trees_512_);
lean_dec_ref(v_infoState_511_);
v___x_513_ = lean_st_ref_take(v___y_508_);
v_infoState_514_ = lean_ctor_get(v___x_513_, 8);
v_env_515_ = lean_ctor_get(v___x_513_, 0);
v_messages_516_ = lean_ctor_get(v___x_513_, 1);
v_scopes_517_ = lean_ctor_get(v___x_513_, 2);
v_usedQuotCtxts_518_ = lean_ctor_get(v___x_513_, 3);
v_nextMacroScope_519_ = lean_ctor_get(v___x_513_, 4);
v_maxRecDepth_520_ = lean_ctor_get(v___x_513_, 5);
v_ngen_521_ = lean_ctor_get(v___x_513_, 6);
v_auxDeclNGen_522_ = lean_ctor_get(v___x_513_, 7);
v_traceState_523_ = lean_ctor_get(v___x_513_, 9);
v_snapshotTasks_524_ = lean_ctor_get(v___x_513_, 10);
v_newDecls_525_ = lean_ctor_get(v___x_513_, 11);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_546_ == 0)
{
v___x_527_ = v___x_513_;
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_newDecls_525_);
lean_inc(v_snapshotTasks_524_);
lean_inc(v_traceState_523_);
lean_inc(v_infoState_514_);
lean_inc(v_auxDeclNGen_522_);
lean_inc(v_ngen_521_);
lean_inc(v_maxRecDepth_520_);
lean_inc(v_nextMacroScope_519_);
lean_inc(v_usedQuotCtxts_518_);
lean_inc(v_scopes_517_);
lean_inc(v_messages_516_);
lean_inc(v_env_515_);
lean_dec(v___x_513_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v_enabled_529_; lean_object* v_assignment_530_; lean_object* v_lazyAssignment_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_544_; 
v_enabled_529_ = lean_ctor_get_uint8(v_infoState_514_, sizeof(void*)*3);
v_assignment_530_ = lean_ctor_get(v_infoState_514_, 0);
v_lazyAssignment_531_ = lean_ctor_get(v_infoState_514_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_infoState_514_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_infoState_514_, 2);
lean_dec(v_unused_545_);
v___x_533_ = v_infoState_514_;
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_lazyAssignment_531_);
lean_inc(v_assignment_530_);
lean_dec(v_infoState_514_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_assignment_530_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_lazyAssignment_531_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v___x_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_543_, sizeof(void*)*3, v_enabled_529_);
v___x_537_ = v_reuseFailAlloc_543_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 8, v___x_537_);
v___x_539_ = v___x_527_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_env_515_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_messages_516_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_scopes_517_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_usedQuotCtxts_518_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_maxRecDepth_520_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_542_, 9, v_traceState_523_);
lean_ctor_set(v_reuseFailAlloc_542_, 10, v_snapshotTasks_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 11, v_newDecls_525_);
v___x_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_st_ref_set(v___y_508_, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_trees_512_);
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_547_);
lean_dec(v___y_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_557_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_558_, lean_object* v_opt_559_){
_start:
{
lean_object* v_name_560_; lean_object* v_defValue_561_; lean_object* v_map_562_; lean_object* v___x_563_; 
v_name_560_ = lean_ctor_get(v_opt_559_, 0);
v_defValue_561_ = lean_ctor_get(v_opt_559_, 1);
v_map_562_ = lean_ctor_get(v_opts_558_, 0);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_562_, v_name_560_);
if (lean_obj_tag(v___x_563_) == 0)
{
uint8_t v___x_564_; 
v___x_564_ = lean_unbox(v_defValue_561_);
return v___x_564_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_565_);
lean_dec_ref(v___x_563_);
if (lean_obj_tag(v_val_565_) == 1)
{
uint8_t v_v_566_; 
v_v_566_ = lean_ctor_get_uint8(v_val_565_, 0);
lean_dec_ref(v_val_565_);
return v_v_566_;
}
else
{
uint8_t v___x_567_; 
lean_dec(v_val_565_);
v___x_567_ = lean_unbox(v_defValue_561_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_568_, lean_object* v_opt_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_568_, v_opt_569_);
lean_dec_ref(v_opt_569_);
lean_dec_ref(v_opts_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_574_, lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_val_574_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_578_, lean_object* v_val_579_){
_start:
{
lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc_ref(v_val_579_);
v___f_580_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_580_, 0, v_val_579_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_inst_578_);
lean_ctor_set(v___x_581_, 1, v_val_579_);
v___x_582_ = lean_mk_thunk(v___f_580_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_586_);
lean_dec_ref(v___x_588_);
v___x_589_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_584_, v___y_585_, v___y_586_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
lean_ctor_set(v___x_600_, 2, v___x_599_);
lean_ctor_set(v___x_600_, 3, v___x_599_);
lean_ctor_set(v___x_600_, 4, v___x_598_);
lean_ctor_set(v___x_600_, 5, v___x_598_);
lean_ctor_set(v___x_600_, 6, v___x_598_);
lean_ctor_set(v___x_600_, 7, v___x_598_);
lean_ctor_set(v___x_600_, 8, v___x_598_);
lean_ctor_set(v___x_600_, 9, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(32u);
v___x_602_ = lean_mk_empty_array_with_capacity(v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_604_ = ((size_t)5ULL);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_unsigned_to_nat(32u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_609_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_605_);
lean_ctor_set(v___x_609_, 3, v___x_605_);
lean_ctor_set_usize(v___x_609_, 4, v___x_604_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_610_ = lean_box(1);
v___x_611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___x_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; lean_object* v_env_618_; lean_object* v___x_619_; lean_object* v_scopes_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_opts_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_617_ = lean_st_ref_get(v___y_615_);
v_env_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_ref(v_env_618_);
lean_dec(v___x_617_);
v___x_619_ = lean_st_ref_get(v___y_615_);
v_scopes_620_ = lean_ctor_get(v___x_619_, 2);
lean_inc(v_scopes_620_);
lean_dec(v___x_619_);
v___x_621_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_622_ = l_List_head_x21___redArg(v___x_621_, v_scopes_620_);
lean_dec(v_scopes_620_);
v_opts_623_ = lean_ctor_get(v___x_622_, 1);
lean_inc_ref(v_opts_623_);
lean_dec(v___x_622_);
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_626_, 0, v_env_618_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_ctor_set(v___x_626_, 3, v_opts_623_);
v___x_627_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_msgData_614_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_629_, v___y_630_);
lean_dec(v___y_630_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_633_, uint8_t v_suppressElabErrors_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 1)
{
lean_object* v_pre_636_; 
v_pre_636_ = lean_ctor_get(v_x_635_, 0);
if (lean_obj_tag(v_pre_636_) == 0)
{
lean_object* v_str_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_str_637_ = lean_ctor_get(v_x_635_, 1);
v___x_638_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_639_ = lean_string_dec_eq(v_str_637_, v___x_638_);
if (v___x_639_ == 0)
{
return v___y_633_;
}
else
{
return v_suppressElabErrors_634_;
}
}
else
{
return v___y_633_;
}
}
else
{
return v___y_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_640_, lean_object* v_suppressElabErrors_641_, lean_object* v_x_642_){
_start:
{
uint8_t v___y_9224__boxed_643_; uint8_t v_suppressElabErrors_boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v___y_9224__boxed_643_ = lean_unbox(v___y_640_);
v_suppressElabErrors_boxed_644_ = lean_unbox(v_suppressElabErrors_641_);
v_res_645_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9224__boxed_643_, v_suppressElabErrors_boxed_644_, v_x_642_);
lean_dec(v_x_642_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_648_, lean_object* v_msgData_649_, uint8_t v_severity_650_, uint8_t v_isSilent_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
uint8_t v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; uint8_t v___y_720_; uint8_t v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; uint8_t v___y_751_; lean_object* v___y_752_; uint8_t v___y_756_; uint8_t v___y_757_; uint8_t v___y_758_; uint8_t v___x_773_; uint8_t v___y_775_; uint8_t v___y_776_; uint8_t v___y_777_; uint8_t v___y_779_; uint8_t v___x_791_; 
v___x_773_ = 2;
v___x_791_ = l_Lean_instBEqMessageSeverity_beq(v_severity_650_, v___x_773_);
if (v___x_791_ == 0)
{
v___y_779_ = v___x_791_;
goto v___jp_778_;
}
else
{
uint8_t v___x_792_; 
lean_inc_ref(v_msgData_649_);
v___x_792_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_649_);
v___y_779_ = v___x_792_;
goto v___jp_778_;
}
v___jp_655_:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Elab_Command_getScope___redArg(v___y_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_666_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = l_Lean_Elab_Command_getScope___redArg(v___y_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_702_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_702_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_702_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_702_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v_currNamespace_672_; lean_object* v_openDecls_673_; lean_object* v_env_674_; lean_object* v_messages_675_; lean_object* v_scopes_676_; lean_object* v_usedQuotCtxts_677_; lean_object* v_nextMacroScope_678_; lean_object* v_maxRecDepth_679_; lean_object* v_ngen_680_; lean_object* v_auxDeclNGen_681_; lean_object* v_infoState_682_; lean_object* v_traceState_683_; lean_object* v_snapshotTasks_684_; lean_object* v_newDecls_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_701_; 
v___x_671_ = lean_st_ref_take(v___y_663_);
v_currNamespace_672_ = lean_ctor_get(v_a_665_, 2);
lean_inc(v_currNamespace_672_);
lean_dec(v_a_665_);
v_openDecls_673_ = lean_ctor_get(v_a_667_, 3);
lean_inc(v_openDecls_673_);
lean_dec(v_a_667_);
v_env_674_ = lean_ctor_get(v___x_671_, 0);
v_messages_675_ = lean_ctor_get(v___x_671_, 1);
v_scopes_676_ = lean_ctor_get(v___x_671_, 2);
v_usedQuotCtxts_677_ = lean_ctor_get(v___x_671_, 3);
v_nextMacroScope_678_ = lean_ctor_get(v___x_671_, 4);
v_maxRecDepth_679_ = lean_ctor_get(v___x_671_, 5);
v_ngen_680_ = lean_ctor_get(v___x_671_, 6);
v_auxDeclNGen_681_ = lean_ctor_get(v___x_671_, 7);
v_infoState_682_ = lean_ctor_get(v___x_671_, 8);
v_traceState_683_ = lean_ctor_get(v___x_671_, 9);
v_snapshotTasks_684_ = lean_ctor_get(v___x_671_, 10);
v_newDecls_685_ = lean_ctor_get(v___x_671_, 11);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_701_ == 0)
{
v___x_687_ = v___x_671_;
v_isShared_688_ = v_isSharedCheck_701_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_newDecls_685_);
lean_inc(v_snapshotTasks_684_);
lean_inc(v_traceState_683_);
lean_inc(v_infoState_682_);
lean_inc(v_auxDeclNGen_681_);
lean_inc(v_ngen_680_);
lean_inc(v_maxRecDepth_679_);
lean_inc(v_nextMacroScope_678_);
lean_inc(v_usedQuotCtxts_677_);
lean_inc(v_scopes_676_);
lean_inc(v_messages_675_);
lean_inc(v_env_674_);
lean_dec(v___x_671_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_701_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_currNamespace_672_);
lean_ctor_set(v___x_689_, 1, v_openDecls_673_);
v___x_690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc_ref(v___y_659_);
v___x_691_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_691_, 0, v___y_659_);
lean_ctor_set(v___x_691_, 1, v___y_661_);
lean_ctor_set(v___x_691_, 2, v___y_660_);
lean_ctor_set(v___x_691_, 3, v___y_657_);
lean_ctor_set(v___x_691_, 4, v___x_690_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5, v___y_656_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5 + 1, v___y_662_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5 + 2, v_isSilent_651_);
v___x_692_ = l_Lean_MessageLog_add(v___x_691_, v_messages_675_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_692_);
v___x_694_ = v___x_687_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_env_674_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_scopes_676_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_usedQuotCtxts_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_nextMacroScope_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_maxRecDepth_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_ngen_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_auxDeclNGen_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_infoState_682_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_traceState_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 10, v_snapshotTasks_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 11, v_newDecls_685_);
v___x_694_ = v_reuseFailAlloc_700_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = lean_st_ref_set(v___y_663_, v___x_694_);
v___x_696_ = lean_box(0);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_696_);
v___x_698_ = v___x_669_;
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
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_a_665_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_658_);
v_a_703_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_666_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_666_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_658_);
v_a_711_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_664_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_664_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
v___jp_719_:
{
lean_object* v_fileName_725_; lean_object* v_fileMap_726_; uint8_t v_suppressElabErrors_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_746_; 
v_fileName_725_ = lean_ctor_get(v___y_652_, 0);
v_fileMap_726_ = lean_ctor_get(v___y_652_, 1);
v_suppressElabErrors_727_ = lean_ctor_get_uint8(v___y_652_, sizeof(void*)*10);
v___x_728_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_649_);
v___x_729_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_728_, v___y_653_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_746_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_746_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_746_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_inc_ref_n(v_fileMap_726_, 2);
v___x_734_ = l_Lean_FileMap_toPosition(v_fileMap_726_, v___y_723_);
lean_dec(v___y_723_);
v___x_735_ = l_Lean_FileMap_toPosition(v_fileMap_726_, v___y_724_);
lean_dec(v___y_724_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_727_ == 0)
{
lean_del_object(v___x_732_);
v___y_656_ = v___y_721_;
v___y_657_ = v___x_737_;
v___y_658_ = v_a_730_;
v___y_659_ = v_fileName_725_;
v___y_660_ = v___x_736_;
v___y_661_ = v___x_734_;
v___y_662_ = v___y_722_;
v___y_663_ = v___y_653_;
goto v___jp_655_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___f_740_; uint8_t v___x_741_; 
v___x_738_ = lean_box(v___y_720_);
v___x_739_ = lean_box(v_suppressElabErrors_727_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_740_, 0, v___x_738_);
lean_closure_set(v___f_740_, 1, v___x_739_);
lean_inc(v_a_730_);
v___x_741_ = l_Lean_MessageData_hasTag(v___f_740_, v_a_730_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_dec_ref(v___x_736_);
lean_dec_ref(v___x_734_);
lean_dec(v_a_730_);
v___x_742_ = lean_box(0);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_742_);
v___x_744_ = v___x_732_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_del_object(v___x_732_);
v___y_656_ = v___y_721_;
v___y_657_ = v___x_737_;
v___y_658_ = v_a_730_;
v___y_659_ = v_fileName_725_;
v___y_660_ = v___x_736_;
v___y_661_ = v___x_734_;
v___y_662_ = v___y_722_;
v___y_663_ = v___y_653_;
goto v___jp_655_;
}
}
}
}
v___jp_747_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Syntax_getTailPos_x3f(v___y_750_, v___y_749_);
lean_dec(v___y_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_inc(v___y_752_);
v___y_720_ = v___y_748_;
v___y_721_ = v___y_749_;
v___y_722_ = v___y_751_;
v___y_723_ = v___y_752_;
v___y_724_ = v___y_752_;
goto v___jp_719_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref(v___x_753_);
v___y_720_ = v___y_748_;
v___y_721_ = v___y_749_;
v___y_722_ = v___y_751_;
v___y_723_ = v___y_752_;
v___y_724_ = v_val_754_;
goto v___jp_719_;
}
}
v___jp_755_:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Elab_Command_getRef___redArg(v___y_652_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_ref_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v_ref_761_ = l_Lean_replaceRef(v_ref_648_, v_a_760_);
lean_dec(v_a_760_);
v___x_762_ = l_Lean_Syntax_getPos_x3f(v_ref_761_, v___y_757_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___y_748_ = v___y_756_;
v___y_749_ = v___y_757_;
v___y_750_ = v_ref_761_;
v___y_751_ = v___y_758_;
v___y_752_ = v___x_763_;
goto v___jp_747_;
}
else
{
lean_object* v_val_764_; 
v_val_764_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_764_);
lean_dec_ref(v___x_762_);
v___y_748_ = v___y_756_;
v___y_749_ = v___y_757_;
v___y_750_ = v_ref_761_;
v___y_751_ = v___y_758_;
v___y_752_ = v_val_764_;
goto v___jp_747_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_msgData_649_);
v_a_765_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_759_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
v___jp_774_:
{
if (v___y_777_ == 0)
{
v___y_756_ = v___y_775_;
v___y_757_ = v___y_776_;
v___y_758_ = v_severity_650_;
goto v___jp_755_;
}
else
{
v___y_756_ = v___y_775_;
v___y_757_ = v___y_776_;
v___y_758_ = v___x_773_;
goto v___jp_755_;
}
}
v___jp_778_:
{
if (v___y_779_ == 0)
{
lean_object* v___x_780_; lean_object* v_scopes_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_opts_784_; uint8_t v___x_785_; uint8_t v___x_786_; 
v___x_780_ = lean_st_ref_get(v___y_653_);
v_scopes_781_ = lean_ctor_get(v___x_780_, 2);
lean_inc(v_scopes_781_);
lean_dec(v___x_780_);
v___x_782_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_783_ = l_List_head_x21___redArg(v___x_782_, v_scopes_781_);
lean_dec(v_scopes_781_);
v_opts_784_ = lean_ctor_get(v___x_783_, 1);
lean_inc_ref(v_opts_784_);
lean_dec(v___x_783_);
v___x_785_ = 1;
v___x_786_ = l_Lean_instBEqMessageSeverity_beq(v_severity_650_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v_opts_784_);
v___y_775_ = v___y_779_;
v___y_776_ = v___y_779_;
v___y_777_ = v___x_786_;
goto v___jp_774_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = l_Lean_warningAsError;
v___x_788_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_784_, v___x_787_);
lean_dec_ref(v_opts_784_);
v___y_775_ = v___y_779_;
v___y_776_ = v___y_779_;
v___y_777_ = v___x_788_;
goto v___jp_774_;
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_msgData_649_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_793_, lean_object* v_msgData_794_, lean_object* v_severity_795_, lean_object* v_isSilent_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
uint8_t v_severity_boxed_800_; uint8_t v_isSilent_boxed_801_; lean_object* v_res_802_; 
v_severity_boxed_800_ = lean_unbox(v_severity_795_);
v_isSilent_boxed_801_ = lean_unbox(v_isSilent_796_);
v_res_802_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_793_, v_msgData_794_, v_severity_boxed_800_, v_isSilent_boxed_801_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v_ref_793_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_803_, uint8_t v_severity_804_, uint8_t v_isSilent_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Elab_Command_getRef___redArg(v___y_806_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref(v___x_809_);
v___x_811_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_810_, v_msgData_803_, v_severity_804_, v_isSilent_805_, v___y_806_, v___y_807_);
lean_dec(v_a_810_);
return v___x_811_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_msgData_803_);
v_a_812_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_809_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_809_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_820_, lean_object* v_severity_821_, lean_object* v_isSilent_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_severity_boxed_826_; uint8_t v_isSilent_boxed_827_; lean_object* v_res_828_; 
v_severity_boxed_826_ = lean_unbox(v_severity_821_);
v_isSilent_boxed_827_ = lean_unbox(v_isSilent_822_);
v_res_828_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_820_, v_severity_boxed_826_, v_isSilent_boxed_827_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = 2;
v___x_834_ = 0;
v___x_835_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_829_, v___x_833_, v___x_834_, v___y_830_, v___y_831_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_841_, lean_object* v_msgData_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = 2;
v___x_847_ = 0;
v___x_848_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_841_, v_msgData_842_, v___x_846_, v___x_847_, v___y_843_, v___y_844_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_849_, lean_object* v_msgData_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_849_, v_msgData_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v_ref_849_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
if (lean_obj_tag(v_ex_858_) == 0)
{
lean_object* v_ref_862_; lean_object* v_msg_863_; lean_object* v___x_864_; 
v_ref_862_ = lean_ctor_get(v_ex_858_, 0);
lean_inc(v_ref_862_);
v_msg_863_ = lean_ctor_get(v_ex_858_, 1);
lean_inc_ref(v_msg_863_);
lean_dec_ref(v_ex_858_);
v___x_864_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_862_, v_msg_863_, v___y_859_, v___y_860_);
lean_dec(v_ref_862_);
return v___x_864_;
}
else
{
lean_object* v_id_865_; uint8_t v___y_867_; uint8_t v___x_889_; 
v_id_865_ = lean_ctor_get(v_ex_858_, 0);
lean_inc(v_id_865_);
v___x_889_ = l_Lean_Elab_isAbortExceptionId(v_id_865_);
if (v___x_889_ == 0)
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_Exception_isInterrupt(v_ex_858_);
lean_dec_ref(v_ex_858_);
v___y_867_ = v___x_890_;
goto v___jp_866_;
}
else
{
lean_dec_ref(v_ex_858_);
v___y_867_ = v___x_889_;
goto v___jp_866_;
}
v___jp_866_:
{
if (v___y_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_InternalExceptionId_getName(v_id_865_);
lean_dec(v_id_865_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref(v___x_868_);
v___x_870_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_871_ = l_Lean_MessageData_ofName(v_a_869_);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_872_, v___y_859_, v___y_860_);
return v___x_873_;
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_886_; 
v_a_874_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_886_ == 0)
{
v___x_876_ = v___x_868_;
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_868_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_ref_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v_ref_878_ = lean_ctor_get(v___y_859_, 7);
v___x_879_ = lean_io_error_to_string(v_a_874_);
v___x_880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
v___x_881_ = l_Lean_MessageData_ofFormat(v___x_880_);
lean_inc(v_ref_878_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_ref_878_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_882_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v_id_865_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
v___x_900_ = lean_apply_3(v_x_896_, v___y_897_, v___y_898_, lean_box(0));
if (lean_obj_tag(v___x_900_) == 0)
{
return v___x_900_;
}
else
{
lean_object* v_a_901_; uint8_t v___x_902_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
v___x_902_ = l_Lean_Exception_isInterrupt(v_a_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec_ref(v___x_900_);
v___x_903_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_901_, v___y_897_, v___y_898_);
return v___x_903_;
}
else
{
lean_dec(v_a_901_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_909_, lean_object* v___x_910_, lean_object* v_val_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_a_915_; lean_object* v___x_917_; 
v___x_917_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_909_, v___x_910_, v_val_911_);
if (lean_obj_tag(v___x_917_) == 0)
{
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref(v___x_917_);
v_a_915_ = v_a_918_;
goto v___jp_914_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_917_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v___x_917_);
v___x_927_ = lean_box(0);
v_a_915_ = v___x_927_;
goto v___jp_914_;
}
v___jp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_a_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_928_, lean_object* v___x_929_, lean_object* v_val_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_928_, v___x_929_, v_val_930_, v___y_931_);
lean_dec_ref(v___y_931_);
lean_dec(v_val_930_);
lean_dec_ref(v___x_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_934_, lean_object* v_x_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_get_set_stderr(v_h_934_);
lean_inc_ref(v___y_936_);
v___x_939_ = lean_apply_2(v_x_935_, v___y_936_, lean_box(0));
v___x_940_ = lean_get_set_stderr(v___x_938_);
lean_dec_ref(v___x_940_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_941_, v_x_942_, v___y_943_);
lean_dec_ref(v___y_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_946_, lean_object* v_h_947_, lean_object* v_x_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_947_, v_x_948_, v___y_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_952_, lean_object* v_h_953_, lean_object* v_x_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_952_, v_h_953_, v_x_954_, v___y_955_);
lean_dec_ref(v___y_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_958_, lean_object* v_x_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_get_set_stdin(v_h_958_);
lean_inc_ref(v___y_960_);
v___x_963_ = lean_apply_2(v_x_959_, v___y_960_, lean_box(0));
v___x_964_ = lean_get_set_stdin(v___x_962_);
lean_dec_ref(v___x_964_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_965_, lean_object* v_x_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_965_, v_x_966_, v___y_967_);
lean_dec_ref(v___y_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_972_ = lean_panic_fn_borrowed(v___x_971_, v_msg_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_973_, lean_object* v_x_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_get_set_stdout(v_h_973_);
lean_inc_ref(v___y_975_);
v___x_978_ = lean_apply_2(v_x_974_, v___y_975_, lean_box(0));
v___x_979_ = lean_get_set_stdout(v___x_977_);
lean_dec_ref(v___x_979_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_980_, v_x_981_, v___y_982_);
lean_dec_ref(v___y_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_985_, lean_object* v_h_986_, lean_object* v_x_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_986_, v_x_987_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_991_, lean_object* v_h_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_991_, v_h_992_, v_x_993_, v___y_994_);
lean_dec_ref(v___y_994_);
return v_res_996_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = l_ByteArray_empty;
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1004_ = lean_unsigned_to_nat(46u);
v___x_1005_ = lean_unsigned_to_nat(193u);
v___x_1006_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1007_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1008_ = l_mkPanicMessageWithDecl(v___x_1007_, v___x_1006_, v___x_1005_, v___x_1004_, v___x_1003_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1009_, uint8_t v_isolateStderr_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___y_1023_; 
v___x_1017_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1018_ = lean_st_mk_ref(v___x_1017_);
v___x_1019_ = lean_st_mk_ref(v___x_1017_);
v___x_1020_ = l_IO_FS_Stream_ofBuffer(v___x_1018_);
lean_inc(v___x_1019_);
v___x_1021_ = l_IO_FS_Stream_ofBuffer(v___x_1019_);
if (v_isolateStderr_1010_ == 0)
{
v___y_1023_ = v_x_1009_;
goto v___jp_1022_;
}
else
{
lean_object* v___x_1032_; 
lean_inc_ref(v___x_1021_);
v___x_1032_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1032_, 0, lean_box(0));
lean_closure_set(v___x_1032_, 1, v___x_1021_);
lean_closure_set(v___x_1032_, 2, v_x_1009_);
v___y_1023_ = v___x_1032_;
goto v___jp_1022_;
}
v___jp_1013_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___y_1015_);
lean_ctor_set(v___x_1016_, 1, v___y_1014_);
return v___x_1016_;
}
v___jp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_data_1027_; uint8_t v___x_1028_; 
v___x_1024_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1024_, 0, lean_box(0));
lean_closure_set(v___x_1024_, 1, v___x_1021_);
lean_closure_set(v___x_1024_, 2, v___y_1023_);
v___x_1025_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1020_, v___x_1024_, v___y_1011_);
v___x_1026_ = lean_st_ref_get(v___x_1019_);
lean_dec(v___x_1019_);
v_data_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc_ref(v_data_1027_);
lean_dec(v___x_1026_);
v___x_1028_ = lean_string_validate_utf8(v_data_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_data_1027_);
v___x_1029_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1030_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1029_);
v___y_1014_ = v___x_1025_;
v___y_1015_ = v___x_1030_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_string_from_utf8_unchecked(v_data_1027_);
v___y_1014_ = v___x_1025_;
v___y_1015_ = v___x_1031_;
goto v___jp_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1033_, lean_object* v_isolateStderr_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v_isolateStderr_boxed_1037_; lean_object* v_res_1038_; 
v_isolateStderr_boxed_1037_ = lean_unbox(v_isolateStderr_1034_);
v_res_1038_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1033_, v_isolateStderr_boxed_1037_, v___y_1035_);
lean_dec_ref(v___y_1035_);
return v_res_1038_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = 1;
v___x_1048_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1049_ = l_Lean_Name_toString(v___x_1048_, v___x_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1050_, lean_object* v_cmdState_1051_, lean_object* v_beginPos_1052_, lean_object* v_snap_1053_, lean_object* v_cancelTk_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_env_1057_; lean_object* v_scopes_1058_; lean_object* v_usedQuotCtxts_1059_; lean_object* v_nextMacroScope_1060_; lean_object* v_maxRecDepth_1061_; lean_object* v_ngen_1062_; lean_object* v_auxDeclNGen_1063_; lean_object* v_infoState_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1141_; 
v_env_1057_ = lean_ctor_get(v_cmdState_1051_, 0);
v_scopes_1058_ = lean_ctor_get(v_cmdState_1051_, 2);
v_usedQuotCtxts_1059_ = lean_ctor_get(v_cmdState_1051_, 3);
v_nextMacroScope_1060_ = lean_ctor_get(v_cmdState_1051_, 4);
v_maxRecDepth_1061_ = lean_ctor_get(v_cmdState_1051_, 5);
v_ngen_1062_ = lean_ctor_get(v_cmdState_1051_, 6);
v_auxDeclNGen_1063_ = lean_ctor_get(v_cmdState_1051_, 7);
v_infoState_1064_ = lean_ctor_get(v_cmdState_1051_, 8);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_cmdState_1051_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1142_ = lean_ctor_get(v_cmdState_1051_, 11);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_cmdState_1051_, 10);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_cmdState_1051_, 9);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_cmdState_1051_, 1);
lean_dec(v_unused_1145_);
v___x_1066_ = v_cmdState_1051_;
v_isShared_1067_ = v_isSharedCheck_1141_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_infoState_1064_);
lean_inc(v_auxDeclNGen_1063_);
lean_inc(v_ngen_1062_);
lean_inc(v_maxRecDepth_1061_);
lean_inc(v_nextMacroScope_1060_);
lean_inc(v_usedQuotCtxts_1059_);
lean_inc(v_scopes_1058_);
lean_inc(v_env_1057_);
lean_dec(v_cmdState_1051_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1141_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1068_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1069_ = l_List_head_x21___redArg(v___x_1068_, v_scopes_1058_);
v___x_1070_ = l_Lean_MessageLog_empty;
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1073_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 11, v___x_1073_);
lean_ctor_set(v___x_1066_, 10, v___x_1073_);
lean_ctor_set(v___x_1066_, 9, v___x_1072_);
lean_ctor_set(v___x_1066_, 1, v___x_1070_);
v___x_1075_ = v___x_1066_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_env_1057_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_scopes_1058_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_usedQuotCtxts_1059_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_nextMacroScope_1060_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_maxRecDepth_1061_);
lean_ctor_set(v_reuseFailAlloc_1140_, 6, v_ngen_1062_);
lean_ctor_set(v_reuseFailAlloc_1140_, 7, v_auxDeclNGen_1063_);
lean_ctor_set(v_reuseFailAlloc_1140_, 8, v_infoState_1064_);
lean_ctor_set(v_reuseFailAlloc_1140_, 9, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1140_, 10, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1140_, 11, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v_toProcessingContext_1077_; lean_object* v_fileName_1078_; lean_object* v_fileMap_1079_; lean_object* v_opts_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___y_1090_; uint8_t v___y_1091_; lean_object* v_messages_1092_; lean_object* v___y_1119_; 
v___x_1076_ = lean_st_mk_ref(v___x_1075_);
v_toProcessingContext_1077_ = lean_ctor_get(v_a_1055_, 0);
v_fileName_1078_ = lean_ctor_get(v_toProcessingContext_1077_, 1);
v_fileMap_1079_ = lean_ctor_get(v_toProcessingContext_1077_, 2);
v_opts_1080_ = lean_ctor_get(v___x_1069_, 1);
lean_inc_ref(v_opts_1080_);
lean_dec(v___x_1069_);
v___f_1081_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1081_, 0, v_stx_1050_);
v___x_1082_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_firstFrontendMacroScope;
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Lean_internal_cmdlineSnapshots;
v___x_1088_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1080_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1139_; 
lean_inc_ref(v_snap_1053_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_snap_1053_);
v___y_1119_ = v___x_1139_;
goto v___jp_1118_;
}
else
{
v___y_1119_ = v___x_1084_;
goto v___jp_1118_;
}
v___jp_1089_:
{
lean_object* v_new_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_env_1099_; lean_object* v_scopes_1100_; lean_object* v_usedQuotCtxts_1101_; lean_object* v_nextMacroScope_1102_; lean_object* v_maxRecDepth_1103_; lean_object* v_ngen_1104_; lean_object* v_auxDeclNGen_1105_; lean_object* v_infoState_1106_; lean_object* v_traceState_1107_; lean_object* v_snapshotTasks_1108_; lean_object* v_newDecls_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_new_1093_ = lean_ctor_get(v_snap_1053_, 1);
lean_inc(v_new_1093_);
lean_dec_ref(v_snap_1053_);
v___x_1094_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1095_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1096_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_ctor_set(v___x_1096_, 2, v___x_1084_);
lean_ctor_set(v___x_1096_, 3, v___x_1072_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*4, v___y_1091_);
v___x_1097_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1082_, v___x_1096_);
v___x_1098_ = lean_io_promise_resolve(v___x_1097_, v_new_1093_);
lean_dec(v_new_1093_);
v_env_1099_ = lean_ctor_get(v___y_1090_, 0);
v_scopes_1100_ = lean_ctor_get(v___y_1090_, 2);
v_usedQuotCtxts_1101_ = lean_ctor_get(v___y_1090_, 3);
v_nextMacroScope_1102_ = lean_ctor_get(v___y_1090_, 4);
v_maxRecDepth_1103_ = lean_ctor_get(v___y_1090_, 5);
v_ngen_1104_ = lean_ctor_get(v___y_1090_, 6);
v_auxDeclNGen_1105_ = lean_ctor_get(v___y_1090_, 7);
v_infoState_1106_ = lean_ctor_get(v___y_1090_, 8);
v_traceState_1107_ = lean_ctor_get(v___y_1090_, 9);
v_snapshotTasks_1108_ = lean_ctor_get(v___y_1090_, 10);
v_newDecls_1109_ = lean_ctor_get(v___y_1090_, 11);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___y_1090_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___y_1090_, 1);
lean_dec(v_unused_1117_);
v___x_1111_ = v___y_1090_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_newDecls_1109_);
lean_inc(v_snapshotTasks_1108_);
lean_inc(v_traceState_1107_);
lean_inc(v_infoState_1106_);
lean_inc(v_auxDeclNGen_1105_);
lean_inc(v_ngen_1104_);
lean_inc(v_maxRecDepth_1103_);
lean_inc(v_nextMacroScope_1102_);
lean_inc(v_usedQuotCtxts_1101_);
lean_inc(v_scopes_1100_);
lean_inc(v_env_1099_);
lean_dec(v___y_1090_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_messages_1092_);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_env_1099_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_messages_1092_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_scopes_1100_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_usedQuotCtxts_1101_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_nextMacroScope_1102_);
lean_ctor_set(v_reuseFailAlloc_1115_, 5, v_maxRecDepth_1103_);
lean_ctor_set(v_reuseFailAlloc_1115_, 6, v_ngen_1104_);
lean_ctor_set(v_reuseFailAlloc_1115_, 7, v_auxDeclNGen_1105_);
lean_ctor_set(v_reuseFailAlloc_1115_, 8, v_infoState_1106_);
lean_ctor_set(v_reuseFailAlloc_1115_, 9, v_traceState_1107_);
lean_ctor_set(v_reuseFailAlloc_1115_, 10, v_snapshotTasks_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 11, v_newDecls_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
v___jp_1118_:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v_fst_1127_; lean_object* v___x_1128_; lean_object* v_messages_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_cancelTk_1054_);
v___x_1121_ = 0;
lean_inc(v_beginPos_1052_);
lean_inc_ref(v_fileMap_1079_);
lean_inc_ref(v_fileName_1078_);
v___x_1122_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1122_, 0, v_fileName_1078_);
lean_ctor_set(v___x_1122_, 1, v_fileMap_1079_);
lean_ctor_set(v___x_1122_, 2, v___x_1071_);
lean_ctor_set(v___x_1122_, 3, v_beginPos_1052_);
lean_ctor_set(v___x_1122_, 4, v___x_1083_);
lean_ctor_set(v___x_1122_, 5, v___x_1084_);
lean_ctor_set(v___x_1122_, 6, v___x_1085_);
lean_ctor_set(v___x_1122_, 7, v___x_1086_);
lean_ctor_set(v___x_1122_, 8, v___y_1119_);
lean_ctor_set(v___x_1122_, 9, v___x_1120_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*10, v___x_1121_);
lean_inc(v___x_1076_);
v___f_1123_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1123_, 0, v___f_1081_);
lean_closure_set(v___f_1123_, 1, v___x_1122_);
lean_closure_set(v___f_1123_, 2, v___x_1076_);
v___x_1124_ = l_Lean_Core_stderrAsMessages;
v___x_1125_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1080_, v___x_1124_);
lean_dec_ref(v_opts_1080_);
v___x_1126_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1123_, v___x_1125_, v_a_1055_);
v_fst_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_fst_1127_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = lean_st_ref_get(v___x_1076_);
lean_dec(v___x_1076_);
v_messages_1129_ = lean_ctor_get(v___x_1128_, 1);
lean_inc_ref(v_messages_1129_);
v___x_1130_ = lean_string_utf8_byte_size(v_fst_1127_);
v___x_1131_ = lean_nat_dec_eq(v___x_1130_, v___x_1071_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_inc_ref(v_fileMap_1079_);
v___x_1132_ = l_Lean_FileMap_toPosition(v_fileMap_1079_, v_beginPos_1052_);
lean_dec(v_beginPos_1052_);
v___x_1133_ = 0;
v___x_1134_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_fst_1127_);
v___x_1136_ = l_Lean_MessageData_ofFormat(v___x_1135_);
lean_inc_ref(v_fileName_1078_);
v___x_1137_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1137_, 0, v_fileName_1078_);
lean_ctor_set(v___x_1137_, 1, v___x_1132_);
lean_ctor_set(v___x_1137_, 2, v___x_1084_);
lean_ctor_set(v___x_1137_, 3, v___x_1134_);
lean_ctor_set(v___x_1137_, 4, v___x_1136_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*5, v___x_1121_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*5 + 1, v___x_1133_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*5 + 2, v___x_1121_);
v___x_1138_ = l_Lean_MessageLog_add(v___x_1137_, v_messages_1129_);
v___y_1090_ = v___x_1128_;
v___y_1091_ = v___x_1121_;
v_messages_1092_ = v___x_1138_;
goto v___jp_1089_;
}
else
{
lean_dec(v_fst_1127_);
lean_dec(v_beginPos_1052_);
v___y_1090_ = v___x_1128_;
v___y_1091_ = v___x_1121_;
v_messages_1092_ = v_messages_1129_;
goto v___jp_1089_;
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
uint8_t v_val_44781__boxed_1270_; size_t v_sz_boxed_1271_; size_t v_i_boxed_1272_; lean_object* v_res_1273_; 
v_val_44781__boxed_1270_ = lean_unbox(v_val_1264_);
v_sz_boxed_1271_ = lean_unbox_usize(v_sz_1266_);
lean_dec(v_sz_1266_);
v_i_boxed_1272_ = lean_unbox_usize(v_i_1267_);
lean_dec(v_i_1267_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1261_, v___x_1262_, v___x_1263_, v_val_44781__boxed_1270_, v_as_1265_, v_sz_boxed_1271_, v_i_boxed_1272_, v_b_1268_);
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
uint8_t v_val_44833__boxed_1313_; size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_val_44833__boxed_1313_ = lean_unbox(v_val_1307_);
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1304_, v___x_1305_, v___x_1306_, v_val_44833__boxed_1313_, v_as_1308_, v_sz_boxed_1314_, v_i_boxed_1315_, v_b_1311_);
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
lean_object* v_cs_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; size_t v_sz_1328_; size_t v___x_1329_; lean_object* v___x_1330_; lean_object* v_fst_1331_; 
v_cs_1325_ = lean_ctor_get(v_n_1322_, 0);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v_b_1323_);
v_sz_1328_ = lean_array_size(v_cs_1325_);
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1317_, v___x_1318_, v___x_1319_, v___x_1320_, v_val_1321_, v_cs_1325_, v_sz_1328_, v___x_1329_, v___x_1327_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_fst_1331_);
if (lean_obj_tag(v_fst_1331_) == 0)
{
lean_object* v_snd_1332_; lean_object* v___x_1333_; 
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v___x_1330_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_snd_1332_);
return v___x_1333_;
}
else
{
lean_object* v_val_1334_; 
lean_dec_ref(v___x_1330_);
v_val_1334_ = lean_ctor_get(v_fst_1331_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v_fst_1331_);
return v_val_1334_;
}
}
else
{
lean_object* v_vs_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; size_t v_sz_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v_fst_1341_; 
v_vs_1335_ = lean_ctor_get(v_n_1322_, 0);
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v_b_1323_);
v_sz_1338_ = lean_array_size(v_vs_1335_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1318_, v___x_1319_, v___x_1320_, v_val_1321_, v_vs_1335_, v_sz_1338_, v___x_1339_, v___x_1337_);
v_fst_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_fst_1341_);
if (lean_obj_tag(v_fst_1341_) == 0)
{
lean_object* v_snd_1342_; lean_object* v___x_1343_; 
v_snd_1342_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_snd_1342_);
lean_dec_ref(v___x_1340_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_snd_1342_);
return v___x_1343_;
}
else
{
lean_object* v_val_1344_; 
lean_dec_ref(v___x_1340_);
v_val_1344_ = lean_ctor_get(v_fst_1341_, 0);
lean_inc(v_val_1344_);
lean_dec_ref(v_fst_1341_);
return v_val_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object* v_init_1345_, lean_object* v___x_1346_, lean_object* v___x_1347_, lean_object* v___x_1348_, uint8_t v_val_1349_, lean_object* v_as_1350_, size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_b_1353_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v___x_1348_);
lean_dec_ref(v___x_1346_);
return v_b_1353_;
}
else
{
lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1374_; 
v_snd_1356_ = lean_ctor_get(v_b_1353_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_b_1353_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_b_1353_, 0);
lean_dec(v_unused_1375_);
v___x_1358_ = v_b_1353_;
v_isShared_1359_ = v_isSharedCheck_1374_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_dec(v_b_1353_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1374_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_array_uget_borrowed(v_as_1350_, v_i_1352_);
lean_inc(v_snd_1356_);
lean_inc_ref(v___x_1348_);
lean_inc_ref(v___x_1346_);
v___x_1361_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1345_, v___x_1346_, v___x_1347_, v___x_1348_, v_val_1349_, v_a_1360_, v_snd_1356_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
lean_dec_ref(v___x_1348_);
lean_dec_ref(v___x_1346_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1362_);
v___x_1364_ = v___x_1358_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1356_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec(v_snd_1356_);
v_a_1366_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1361_);
v___x_1367_ = lean_box(0);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_a_1366_);
lean_ctor_set(v___x_1358_, 0, v___x_1367_);
v___x_1369_ = v___x_1358_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1366_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
size_t v___x_1370_; size_t v___x_1371_; 
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_add(v_i_1352_, v___x_1370_);
v_i_1352_ = v___x_1371_;
v_b_1353_ = v___x_1369_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1376_, lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v___x_1379_, lean_object* v_val_1380_, lean_object* v_as_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_val_44884__boxed_1386_; size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_val_44884__boxed_1386_ = lean_unbox(v_val_1380_);
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1376_, v___x_1377_, v___x_1378_, v___x_1379_, v_val_44884__boxed_1386_, v_as_1381_, v_sz_boxed_1387_, v_i_boxed_1388_, v_b_1384_);
lean_dec_ref(v_as_1381_);
lean_dec(v___x_1378_);
lean_dec_ref(v_init_1376_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v_init_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v_val_1394_, lean_object* v_n_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_val_44900__boxed_1398_; lean_object* v_res_1399_; 
v_val_44900__boxed_1398_ = lean_unbox(v_val_1394_);
v_res_1399_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v_val_44900__boxed_1398_, v_n_1395_, v_b_1396_);
lean_dec_ref(v_n_1395_);
lean_dec(v___x_1392_);
lean_dec_ref(v_init_1390_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___x_1402_, uint8_t v_val_1403_, lean_object* v_as_1404_, size_t v_sz_1405_, size_t v_i_1406_, lean_object* v_b_1407_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_lt(v_i_1406_, v_sz_1405_);
if (v___x_1409_ == 0)
{
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1400_);
return v_b_1407_;
}
else
{
lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1428_; 
v_snd_1410_ = lean_ctor_get(v_b_1407_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_b_1407_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_b_1407_, 0);
lean_dec(v_unused_1429_);
v___x_1412_ = v_b_1407_;
v_isShared_1413_ = v_isSharedCheck_1428_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_dec(v_b_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1428_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_a_1414_; lean_object* v_msg_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v_a_1414_ = lean_array_uget_borrowed(v_as_1404_, v_i_1406_);
v_msg_1415_ = lean_ctor_get(v_a_1414_, 1);
v___x_1416_ = lean_box(0);
lean_inc_ref(v___x_1400_);
v___x_1417_ = l_Lean_FileMap_toPosition(v___x_1400_, v___x_1401_);
v___x_1418_ = 0;
v___x_1419_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1415_);
lean_inc_ref(v___x_1402_);
v___x_1420_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1420_, 0, v___x_1402_);
lean_ctor_set(v___x_1420_, 1, v___x_1417_);
lean_ctor_set(v___x_1420_, 2, v___x_1416_);
lean_ctor_set(v___x_1420_, 3, v___x_1419_);
lean_ctor_set(v___x_1420_, 4, v_msg_1415_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*5, v_val_1403_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*5 + 1, v___x_1418_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*5 + 2, v_val_1403_);
v___x_1421_ = l_Lean_MessageLog_add(v___x_1420_, v_snd_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___x_1421_);
lean_ctor_set(v___x_1412_, 0, v___x_1416_);
v___x_1423_ = v___x_1412_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
size_t v___x_1424_; size_t v___x_1425_; 
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1406_, v___x_1424_);
v_i_1406_ = v___x_1425_;
v_b_1407_ = v___x_1423_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1430_, lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v_val_1433_, lean_object* v_as_1434_, lean_object* v_sz_1435_, lean_object* v_i_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v_val_44982__boxed_1439_; size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v_val_44982__boxed_1439_ = lean_unbox(v_val_1433_);
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1435_);
lean_dec(v_sz_1435_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1430_, v___x_1431_, v___x_1432_, v_val_44982__boxed_1439_, v_as_1434_, v_sz_boxed_1440_, v_i_boxed_1441_, v_b_1437_);
lean_dec_ref(v_as_1434_);
lean_dec(v___x_1431_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v___x_1445_, uint8_t v_val_1446_, lean_object* v_as_1447_, size_t v_sz_1448_, size_t v_i_1449_, lean_object* v_b_1450_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_usize_dec_lt(v_i_1449_, v_sz_1448_);
if (v___x_1452_ == 0)
{
lean_dec_ref(v___x_1445_);
lean_dec_ref(v___x_1443_);
return v_b_1450_;
}
else
{
lean_object* v_snd_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1471_; 
v_snd_1453_ = lean_ctor_get(v_b_1450_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_b_1450_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_b_1450_, 0);
lean_dec(v_unused_1472_);
v___x_1455_ = v_b_1450_;
v_isShared_1456_ = v_isSharedCheck_1471_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_snd_1453_);
lean_dec(v_b_1450_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1471_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_a_1457_; lean_object* v_msg_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v_a_1457_ = lean_array_uget_borrowed(v_as_1447_, v_i_1449_);
v_msg_1458_ = lean_ctor_get(v_a_1457_, 1);
v___x_1459_ = lean_box(0);
lean_inc_ref(v___x_1443_);
v___x_1460_ = l_Lean_FileMap_toPosition(v___x_1443_, v___x_1444_);
v___x_1461_ = 0;
v___x_1462_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1458_);
lean_inc_ref(v___x_1445_);
v___x_1463_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1463_, 0, v___x_1445_);
lean_ctor_set(v___x_1463_, 1, v___x_1460_);
lean_ctor_set(v___x_1463_, 2, v___x_1459_);
lean_ctor_set(v___x_1463_, 3, v___x_1462_);
lean_ctor_set(v___x_1463_, 4, v_msg_1458_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*5, v_val_1446_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*5 + 1, v___x_1461_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*5 + 2, v_val_1446_);
v___x_1464_ = l_Lean_MessageLog_add(v___x_1463_, v_snd_1453_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___x_1464_);
lean_ctor_set(v___x_1455_, 0, v___x_1459_);
v___x_1466_ = v___x_1455_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1449_, v___x_1467_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1443_, v___x_1444_, v___x_1445_, v_val_1446_, v_as_1447_, v_sz_1448_, v___x_1468_, v___x_1466_);
return v___x_1469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v_val_1476_, lean_object* v_as_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_val_45034__boxed_1482_; size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_val_45034__boxed_1482_ = lean_unbox(v_val_1476_);
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1473_, v___x_1474_, v___x_1475_, v_val_45034__boxed_1482_, v_as_1477_, v_sz_boxed_1483_, v_i_boxed_1484_, v_b_1480_);
lean_dec_ref(v_as_1477_);
lean_dec(v___x_1474_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v___x_1486_, lean_object* v___x_1487_, lean_object* v___x_1488_, uint8_t v_val_1489_, lean_object* v_t_1490_, lean_object* v_init_1491_){
_start:
{
lean_object* v_root_1493_; lean_object* v_tail_1494_; lean_object* v___x_1495_; 
v_root_1493_ = lean_ctor_get(v_t_1490_, 0);
v_tail_1494_ = lean_ctor_get(v_t_1490_, 1);
lean_inc_ref(v___x_1488_);
lean_inc_ref(v___x_1486_);
lean_inc_ref(v_init_1491_);
v___x_1495_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1491_, v___x_1486_, v___x_1487_, v___x_1488_, v_val_1489_, v_root_1493_, v_init_1491_);
lean_dec_ref(v_init_1491_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; 
lean_dec_ref(v___x_1488_);
lean_dec_ref(v___x_1486_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
return v_a_1496_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_1502_; lean_object* v_fst_1503_; 
v_a_1497_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1495_);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_a_1497_);
v_sz_1500_ = lean_array_size(v_tail_1494_);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1486_, v___x_1487_, v___x_1488_, v_val_1489_, v_tail_1494_, v_sz_1500_, v___x_1501_, v___x_1499_);
v_fst_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_fst_1503_);
if (lean_obj_tag(v_fst_1503_) == 0)
{
lean_object* v_snd_1504_; 
v_snd_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_snd_1504_);
lean_dec_ref(v___x_1502_);
return v_snd_1504_;
}
else
{
lean_object* v_val_1505_; 
lean_dec_ref(v___x_1502_);
v_val_1505_ = lean_ctor_get(v_fst_1503_, 0);
lean_inc(v_val_1505_);
lean_dec_ref(v_fst_1503_);
return v_val_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v___x_1508_, lean_object* v_val_1509_, lean_object* v_t_1510_, lean_object* v_init_1511_, lean_object* v___y_1512_){
_start:
{
uint8_t v_val_45085__boxed_1513_; lean_object* v_res_1514_; 
v_val_45085__boxed_1513_ = lean_unbox(v_val_1509_);
v_res_1514_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1506_, v___x_1507_, v___x_1508_, v_val_45085__boxed_1513_, v_t_1510_, v_init_1511_);
lean_dec_ref(v_t_1510_);
lean_dec(v___x_1507_);
return v_res_1514_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = l_Lean_firstFrontendMacroScope;
v___x_1517_ = lean_nat_add(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1524_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1529_, lean_object* v___x_1530_, lean_object* v___x_1531_, size_t v___x_1532_, uint8_t v___x_1533_, lean_object* v_env_1534_, lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_a_1537_, lean_object* v_opts_1538_, lean_object* v___x_1539_, lean_object* v_pos_1540_, uint8_t v_val_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, uint8_t v___x_1546_, lean_object* v_x_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_toProcessingContext_1568_; lean_object* v_fileName_1569_; lean_object* v_fileMap_1570_; lean_object* v_env_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v_fileName_1577_; lean_object* v_fileMap_1578_; lean_object* v_currRecDepth_1579_; lean_object* v_ref_1580_; lean_object* v_currNamespace_1581_; lean_object* v_openDecls_1582_; lean_object* v_initHeartbeats_1583_; lean_object* v_maxHeartbeats_1584_; lean_object* v_quotContext_1585_; lean_object* v_currMacroScope_1586_; lean_object* v_cancelTk_x3f_1587_; uint8_t v_suppressElabErrors_1588_; lean_object* v_inheritedTraceOptions_1589_; lean_object* v___y_1590_; uint8_t v___y_1607_; uint8_t v___x_1628_; 
v___x_1549_ = l_Lean_firstFrontendMacroScope;
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_1552_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_1553_ = lean_box(0);
lean_inc(v___x_1529_);
v___x_1554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1529_);
lean_ctor_set(v___x_1554_, 1, v___x_1550_);
lean_ctor_set(v___x_1554_, 2, v___x_1553_);
v___x_1555_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1556_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
v___x_1557_ = lean_mk_empty_array_with_capacity(v___x_1530_);
lean_inc_ref(v___x_1557_);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_inc_n(v___x_1531_, 2);
v___x_1559_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1557_);
lean_ctor_set(v___x_1559_, 2, v___x_1531_);
lean_ctor_set(v___x_1559_, 3, v___x_1531_);
lean_ctor_set_usize(v___x_1559_, 4, v___x_1532_);
v___x_1560_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1559_, 2);
v___x_1561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1559_);
lean_ctor_set(v___x_1561_, 2, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1562_, 0, v___x_1555_);
lean_ctor_set(v___x_1562_, 1, v___x_1555_);
lean_ctor_set(v___x_1562_, 2, v___x_1559_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*3, v___x_1533_);
v___x_1563_ = lean_mk_empty_array_with_capacity(v___x_1531_);
lean_inc_ref_n(v___x_1563_, 2);
lean_inc_ref(v___x_1535_);
v___x_1564_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1564_, 0, v_env_1534_);
lean_ctor_set(v___x_1564_, 1, v___x_1551_);
lean_ctor_set(v___x_1564_, 2, v___x_1552_);
lean_ctor_set(v___x_1564_, 3, v___x_1554_);
lean_ctor_set(v___x_1564_, 4, v___x_1535_);
lean_ctor_set(v___x_1564_, 5, v___x_1556_);
lean_ctor_set(v___x_1564_, 6, v___x_1561_);
lean_ctor_set(v___x_1564_, 7, v___x_1562_);
lean_ctor_set(v___x_1564_, 8, v___x_1563_);
lean_ctor_set(v___x_1564_, 9, v___x_1563_);
v___x_1565_ = lean_st_mk_ref(v___x_1564_);
v___x_1566_ = lean_st_ref_get(v___x_1536_);
v___x_1567_ = lean_st_ref_get(v___x_1565_);
v_toProcessingContext_1568_ = lean_ctor_get(v_a_1537_, 0);
v_fileName_1569_ = lean_ctor_get(v_toProcessingContext_1568_, 1);
v_fileMap_1570_ = lean_ctor_get(v_toProcessingContext_1568_, 2);
v_env_1571_ = lean_ctor_get(v___x_1567_, 0);
lean_inc_ref(v_env_1571_);
lean_dec(v___x_1567_);
v___x_1572_ = lean_box(0);
v___x_1573_ = l_Lean_Core_getMaxHeartbeats(v_opts_1538_);
v___x_1574_ = l_Lean_diagnostics;
v___x_1575_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1538_, v___x_1574_);
v___x_1628_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1571_);
lean_dec_ref(v_env_1571_);
if (v___x_1628_ == 0)
{
if (v___x_1575_ == 0)
{
v___y_1607_ = v___x_1546_;
goto v___jp_1606_;
}
else
{
v___y_1607_ = v___x_1628_;
goto v___jp_1606_;
}
}
else
{
v___y_1607_ = v___x_1575_;
goto v___jp_1606_;
}
v___jp_1576_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = l_Lean_maxRecDepth;
v___x_1592_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1538_, v___x_1591_);
lean_inc(v_currMacroScope_1586_);
lean_inc(v_openDecls_1582_);
lean_inc(v_ref_1580_);
v___x_1593_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1593_, 0, v_fileName_1577_);
lean_ctor_set(v___x_1593_, 1, v_fileMap_1578_);
lean_ctor_set(v___x_1593_, 2, v_opts_1538_);
lean_ctor_set(v___x_1593_, 3, v_currRecDepth_1579_);
lean_ctor_set(v___x_1593_, 4, v___x_1592_);
lean_ctor_set(v___x_1593_, 5, v_ref_1580_);
lean_ctor_set(v___x_1593_, 6, v_currNamespace_1581_);
lean_ctor_set(v___x_1593_, 7, v_openDecls_1582_);
lean_ctor_set(v___x_1593_, 8, v_initHeartbeats_1583_);
lean_ctor_set(v___x_1593_, 9, v_maxHeartbeats_1584_);
lean_ctor_set(v___x_1593_, 10, v_quotContext_1585_);
lean_ctor_set(v___x_1593_, 11, v_currMacroScope_1586_);
lean_ctor_set(v___x_1593_, 12, v_cancelTk_x3f_1587_);
lean_ctor_set(v___x_1593_, 13, v_inheritedTraceOptions_1589_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14, v___x_1575_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*14 + 1, v_suppressElabErrors_1588_);
v___x_1594_ = l_Lean_Language_SnapshotTree_trace(v___x_1539_, v___x_1593_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; lean_object* v_traceState_1596_; lean_object* v_traces_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1544_);
v___x_1595_ = lean_st_ref_get(v___x_1565_);
lean_dec(v___x_1565_);
v_traceState_1596_ = lean_ctor_get(v___x_1595_, 4);
lean_inc_ref(v_traceState_1596_);
lean_dec(v___x_1595_);
v_traces_1597_ = lean_ctor_get(v_traceState_1596_, 0);
lean_inc_ref(v_traces_1597_);
lean_dec_ref(v_traceState_1596_);
v___x_1598_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1569_);
lean_inc_ref(v_fileMap_1570_);
v___x_1599_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_1570_, v_pos_1540_, v_fileName_1569_, v_val_1541_, v_traces_1597_, v___x_1598_);
lean_dec_ref(v_traces_1597_);
v___x_1600_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1601_, 0, v___x_1542_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
lean_ctor_set(v___x_1601_, 2, v___x_1543_);
lean_ctor_set(v___x_1601_, 3, v___x_1535_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*4, v_val_1541_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1563_);
v___x_1603_ = lean_task_pure(v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec_ref(v___x_1594_);
lean_dec(v___x_1565_);
lean_dec(v___x_1543_);
lean_dec_ref(v___x_1542_);
lean_dec_ref(v___x_1535_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1544_);
lean_ctor_set(v___x_1604_, 1, v___x_1563_);
v___x_1605_ = lean_task_pure(v___x_1604_);
return v___x_1605_;
}
}
v___jp_1606_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v_nextMacroScope_1610_; lean_object* v_ngen_1611_; lean_object* v_auxDeclNGen_1612_; lean_object* v_traceState_1613_; lean_object* v_messages_1614_; lean_object* v_infoState_1615_; lean_object* v_snapshotTasks_1616_; lean_object* v_newDecls_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1626_; 
v___x_1608_ = lean_st_ref_take(v___x_1565_);
v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
v_nextMacroScope_1610_ = lean_ctor_get(v___x_1608_, 1);
v_ngen_1611_ = lean_ctor_get(v___x_1608_, 2);
v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1608_, 3);
v_traceState_1613_ = lean_ctor_get(v___x_1608_, 4);
v_messages_1614_ = lean_ctor_get(v___x_1608_, 6);
v_infoState_1615_ = lean_ctor_get(v___x_1608_, 7);
v_snapshotTasks_1616_ = lean_ctor_get(v___x_1608_, 8);
v_newDecls_1617_ = lean_ctor_get(v___x_1608_, 9);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1608_, 5);
lean_dec(v_unused_1627_);
v___x_1619_ = v___x_1608_;
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_newDecls_1617_);
lean_inc(v_snapshotTasks_1616_);
lean_inc(v_infoState_1615_);
lean_inc(v_messages_1614_);
lean_inc(v_traceState_1613_);
lean_inc(v_auxDeclNGen_1612_);
lean_inc(v_ngen_1611_);
lean_inc(v_nextMacroScope_1610_);
lean_inc(v_env_1609_);
lean_dec(v___x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = l_Lean_Kernel_enableDiag(v_env_1609_, v___x_1575_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 5, v___x_1556_);
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_nextMacroScope_1610_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_ngen_1611_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_auxDeclNGen_1612_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_traceState_1613_);
lean_ctor_set(v_reuseFailAlloc_1625_, 5, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1625_, 6, v_messages_1614_);
lean_ctor_set(v_reuseFailAlloc_1625_, 7, v_infoState_1615_);
lean_ctor_set(v_reuseFailAlloc_1625_, 8, v_snapshotTasks_1616_);
lean_ctor_set(v_reuseFailAlloc_1625_, 9, v_newDecls_1617_);
v___x_1623_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_st_ref_set(v___x_1565_, v___x_1623_);
lean_inc(v___x_1565_);
lean_inc(v___x_1529_);
lean_inc(v___x_1531_);
lean_inc_ref(v_fileMap_1570_);
lean_inc_ref(v_fileName_1569_);
v_fileName_1577_ = v_fileName_1569_;
v_fileMap_1578_ = v_fileMap_1570_;
v_currRecDepth_1579_ = v___x_1531_;
v_ref_1580_ = v___x_1572_;
v_currNamespace_1581_ = v___x_1529_;
v_openDecls_1582_ = v___x_1553_;
v_initHeartbeats_1583_ = v___x_1531_;
v_maxHeartbeats_1584_ = v___x_1573_;
v_quotContext_1585_ = v___x_1529_;
v_currMacroScope_1586_ = v___x_1549_;
v_cancelTk_x3f_1587_ = v___x_1545_;
v_suppressElabErrors_1588_ = v_val_1541_;
v_inheritedTraceOptions_1589_ = v___x_1566_;
v___y_1590_ = v___x_1565_;
goto v___jp_1576_;
}
}
}
else
{
lean_inc(v___x_1565_);
lean_inc(v___x_1529_);
lean_inc(v___x_1531_);
lean_inc_ref(v_fileMap_1570_);
lean_inc_ref(v_fileName_1569_);
v_fileName_1577_ = v_fileName_1569_;
v_fileMap_1578_ = v_fileMap_1570_;
v_currRecDepth_1579_ = v___x_1531_;
v_ref_1580_ = v___x_1572_;
v_currNamespace_1581_ = v___x_1529_;
v_openDecls_1582_ = v___x_1553_;
v_initHeartbeats_1583_ = v___x_1531_;
v_maxHeartbeats_1584_ = v___x_1573_;
v_quotContext_1585_ = v___x_1529_;
v_currMacroScope_1586_ = v___x_1549_;
v_cancelTk_x3f_1587_ = v___x_1545_;
v_suppressElabErrors_1588_ = v_val_1541_;
v_inheritedTraceOptions_1589_ = v___x_1566_;
v___y_1590_ = v___x_1565_;
goto v___jp_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_1629_ = _args[0];
lean_object* v___x_1630_ = _args[1];
lean_object* v___x_1631_ = _args[2];
lean_object* v___x_1632_ = _args[3];
lean_object* v___x_1633_ = _args[4];
lean_object* v_env_1634_ = _args[5];
lean_object* v___x_1635_ = _args[6];
lean_object* v___x_1636_ = _args[7];
lean_object* v_a_1637_ = _args[8];
lean_object* v_opts_1638_ = _args[9];
lean_object* v___x_1639_ = _args[10];
lean_object* v_pos_1640_ = _args[11];
lean_object* v_val_1641_ = _args[12];
lean_object* v___x_1642_ = _args[13];
lean_object* v___x_1643_ = _args[14];
lean_object* v___x_1644_ = _args[15];
lean_object* v___x_1645_ = _args[16];
lean_object* v___x_1646_ = _args[17];
lean_object* v_x_1647_ = _args[18];
lean_object* v___y_1648_ = _args[19];
_start:
{
size_t v___x_45146__boxed_1649_; uint8_t v___x_45147__boxed_1650_; uint8_t v_val_45151__boxed_1651_; uint8_t v___x_45156__boxed_1652_; lean_object* v_res_1653_; 
v___x_45146__boxed_1649_ = lean_unbox_usize(v___x_1632_);
lean_dec(v___x_1632_);
v___x_45147__boxed_1650_ = lean_unbox(v___x_1633_);
v_val_45151__boxed_1651_ = lean_unbox(v_val_1641_);
v___x_45156__boxed_1652_ = lean_unbox(v___x_1646_);
v_res_1653_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1629_, v___x_1630_, v___x_1631_, v___x_45146__boxed_1649_, v___x_45147__boxed_1650_, v_env_1634_, v___x_1635_, v___x_1636_, v_a_1637_, v_opts_1638_, v___x_1639_, v_pos_1640_, v_val_45151__boxed_1651_, v___x_1642_, v___x_1643_, v___x_1644_, v___x_1645_, v___x_45156__boxed_1652_, v_x_1647_);
lean_dec(v_pos_1640_);
lean_dec_ref(v_a_1637_);
lean_dec(v___x_1636_);
lean_dec(v___x_1630_);
return v_res_1653_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1660_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1661_ = l_Lean_Name_append(v___x_1660_, v___x_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1662_, lean_object* v___x_1663_, uint8_t v_val_1664_, lean_object* v_val_1665_, lean_object* v_val_1666_, lean_object* v___x_1667_, lean_object* v___x_1668_, uint8_t v___x_1669_, lean_object* v_a_1670_, lean_object* v_pos_1671_, lean_object* v_infoSt_1672_){
_start:
{
lean_object* v___y_1675_; lean_object* v_msgLog_1676_; lean_object* v___y_1682_; lean_object* v_trees_1714_; lean_object* v_size_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_trees_1714_ = lean_ctor_get(v_infoSt_1672_, 2);
v_size_1715_ = lean_ctor_get(v_trees_1714_, 2);
v___x_1716_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1717_ = lean_nat_dec_lt(v___x_1668_, v_size_1715_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = l_outOfBounds___redArg(v___x_1716_);
v___y_1682_ = v___x_1718_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1716_, v_trees_1714_, v___x_1668_);
v___y_1682_ = v___x_1719_;
goto v___jp_1681_;
}
v___jp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1676_);
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___y_1675_);
v___x_1679_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1679_, 0, v___x_1662_);
lean_ctor_set(v___x_1679_, 1, v___x_1677_);
lean_ctor_set(v___x_1679_, 2, v___x_1678_);
lean_ctor_set(v___x_1679_, 3, v___x_1663_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*4, v_val_1664_);
v___x_1680_ = lean_io_promise_resolve(v___x_1679_, v_val_1665_);
return v___x_1680_;
}
v___jp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_scopes_1685_; lean_object* v___x_1686_; lean_object* v_opts_1687_; uint8_t v_hasTrace_1688_; lean_object* v___x_1689_; 
v___x_1683_ = l_Lean_inheritedTraceOptions;
v___x_1684_ = lean_st_ref_get(v___x_1683_);
v_scopes_1685_ = lean_ctor_get(v_val_1666_, 2);
v___x_1686_ = l_List_head_x21___redArg(v___x_1667_, v_scopes_1685_);
v_opts_1687_ = lean_ctor_get(v___x_1686_, 1);
lean_inc_ref(v_opts_1687_);
lean_dec(v___x_1686_);
v_hasTrace_1688_ = lean_ctor_get_uint8(v_opts_1687_, sizeof(void*)*1);
v___x_1689_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1688_ == 0)
{
lean_dec_ref(v_opts_1687_);
lean_dec(v___x_1684_);
lean_dec(v___x_1668_);
v___y_1675_ = v___y_1682_;
v_msgLog_1676_ = v___x_1689_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1691_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1692_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1684_, v_opts_1687_, v___x_1692_);
lean_dec_ref(v_opts_1687_);
lean_dec(v___x_1684_);
if (v___x_1693_ == 0)
{
lean_dec(v___x_1668_);
v___y_1675_ = v___y_1682_;
v_msgLog_1676_ = v___x_1689_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_box(0);
lean_inc_ref(v___y_1682_);
v___x_1695_ = l_Lean_Elab_InfoTree_format(v___y_1682_, v___x_1694_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; double v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_toProcessingContext_1700_; lean_object* v_fileName_1701_; lean_object* v_fileMap_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_float_of_nat(v___x_1668_);
v___x_1698_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1699_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1699_, 0, v___x_1690_);
lean_ctor_set(v___x_1699_, 1, v___x_1694_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
lean_ctor_set_float(v___x_1699_, sizeof(void*)*3, v___x_1697_);
lean_ctor_set_float(v___x_1699_, sizeof(void*)*3 + 8, v___x_1697_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*3 + 16, v___x_1669_);
v_toProcessingContext_1700_ = lean_ctor_get(v_a_1670_, 0);
v_fileName_1701_ = lean_ctor_get(v_toProcessingContext_1700_, 1);
v_fileMap_1702_ = lean_ctor_get(v_toProcessingContext_1700_, 2);
v___x_1703_ = l_Lean_MessageData_nil;
v___x_1704_ = l_Lean_MessageData_ofFormat(v_a_1696_);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = lean_mk_empty_array_with_capacity(v___x_1705_);
v___x_1707_ = lean_array_push(v___x_1706_, v___x_1704_);
v___x_1708_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1699_);
lean_ctor_set(v___x_1708_, 1, v___x_1703_);
lean_ctor_set(v___x_1708_, 2, v___x_1707_);
v___x_1709_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1691_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
lean_inc_ref(v_fileMap_1702_);
v___x_1710_ = l_Lean_FileMap_toPosition(v_fileMap_1702_, v_pos_1671_);
v___x_1711_ = 0;
lean_inc_ref(v_fileName_1701_);
v___x_1712_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1712_, 0, v_fileName_1701_);
lean_ctor_set(v___x_1712_, 1, v___x_1710_);
lean_ctor_set(v___x_1712_, 2, v___x_1694_);
lean_ctor_set(v___x_1712_, 3, v___x_1698_);
lean_ctor_set(v___x_1712_, 4, v___x_1709_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*5, v_val_1664_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*5 + 1, v___x_1711_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*5 + 2, v_val_1664_);
v___x_1713_ = l_Lean_MessageLog_add(v___x_1712_, v___x_1689_);
v___y_1675_ = v___y_1682_;
v_msgLog_1676_ = v___x_1713_;
goto v___jp_1674_;
}
else
{
lean_dec_ref(v___x_1695_);
lean_dec(v___x_1668_);
v___y_1675_ = v___y_1682_;
v_msgLog_1676_ = v___x_1689_;
goto v___jp_1674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v_val_1722_, lean_object* v_val_1723_, lean_object* v_val_1724_, lean_object* v___x_1725_, lean_object* v___x_1726_, lean_object* v___x_1727_, lean_object* v_a_1728_, lean_object* v_pos_1729_, lean_object* v_infoSt_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v_val_45333__boxed_1732_; uint8_t v___x_45338__boxed_1733_; lean_object* v_res_1734_; 
v_val_45333__boxed_1732_ = lean_unbox(v_val_1722_);
v___x_45338__boxed_1733_ = lean_unbox(v___x_1727_);
v_res_1734_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1720_, v___x_1721_, v_val_45333__boxed_1732_, v_val_1723_, v_val_1724_, v___x_1725_, v___x_1726_, v___x_45338__boxed_1733_, v_a_1728_, v_pos_1729_, v_infoSt_1730_);
lean_dec_ref(v_infoSt_1730_);
lean_dec(v_pos_1729_);
lean_dec_ref(v_a_1728_);
lean_dec_ref(v___x_1725_);
lean_dec_ref(v_val_1724_);
lean_dec(v_val_1723_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1736_, size_t v_i_1737_, size_t v_stop_1738_, lean_object* v_b_1739_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_eq(v_i_1737_, v_stop_1738_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; 
v___x_1742_ = lean_array_uget_borrowed(v_as_1736_, v_i_1737_);
v___f_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1742_);
v___x_1744_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1743_, v___x_1742_);
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1737_, v___x_1745_);
v_i_1737_ = v___x_1746_;
v_b_1739_ = v___x_1744_;
goto _start;
}
else
{
return v_b_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1748_, lean_object* v_i_1749_, lean_object* v_stop_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_){
_start:
{
size_t v_i_boxed_1753_; size_t v_stop_boxed_1754_; lean_object* v_res_1755_; 
v_i_boxed_1753_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_stop_boxed_1754_ = lean_unbox_usize(v_stop_1750_);
lean_dec(v_stop_1750_);
v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1748_, v_i_boxed_1753_, v_stop_boxed_1754_, v_b_1751_);
lean_dec_ref(v_as_1748_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1756_, lean_object* v_newParserState_1757_, lean_object* v_val_1758_, lean_object* v_sync_1759_, lean_object* v_val_1760_, lean_object* v_a_1761_, lean_object* v_oldNext_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v_sync_boxed_1764_; lean_object* v_res_1765_; 
v_sync_boxed_1764_ = lean_unbox(v_sync_1759_);
v_res_1765_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1756_, v_newParserState_1757_, v_val_1758_, v_sync_boxed_1764_, v_val_1760_, v_a_1761_, v_oldNext_1762_);
lean_dec_ref(v_a_1761_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1766_, lean_object* v_newParserState_1767_, lean_object* v_val_1768_, uint8_t v_sync_1769_, lean_object* v_val_1770_, lean_object* v_a_1771_, lean_object* v_oldResult_1772_){
_start:
{
lean_object* v_task_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; 
v_task_1774_ = lean_ctor_get(v_val_1766_, 3);
lean_inc_ref(v_task_1774_);
lean_dec_ref(v_val_1766_);
v___x_1775_ = lean_box(v_sync_1769_);
lean_inc_ref(v_a_1771_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 8, 6);
lean_closure_set(v___f_1776_, 0, v_oldResult_1772_);
lean_closure_set(v___f_1776_, 1, v_newParserState_1767_);
lean_closure_set(v___f_1776_, 2, v_val_1768_);
lean_closure_set(v___f_1776_, 3, v___x_1775_);
lean_closure_set(v___f_1776_, 4, v_val_1770_);
lean_closure_set(v___f_1776_, 5, v_a_1771_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = 1;
v___x_1779_ = l_BaseIO_chainTask___redArg(v_task_1774_, v___f_1776_, v___x_1777_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1780_, lean_object* v_newParserState_1781_, lean_object* v_val_1782_, lean_object* v_sync_1783_, lean_object* v_val_1784_, lean_object* v_a_1785_, lean_object* v_oldResult_1786_, lean_object* v___y_1787_){
_start:
{
uint8_t v_sync_boxed_1788_; lean_object* v_res_1789_; 
v_sync_boxed_1788_ = lean_unbox(v_sync_1783_);
v_res_1789_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1780_, v_newParserState_1781_, v_val_1782_, v_sync_boxed_1788_, v_val_1784_, v_a_1785_, v_oldResult_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1789_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1792_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1794_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1803_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1804_ = l_Lean_Name_append(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1808_, lean_object* v_val_1809_, lean_object* v_fst_1810_, uint8_t v_val_1811_, lean_object* v_a_1812_, lean_object* v_snd_1813_, lean_object* v___x_1814_, uint8_t v___x_1815_, lean_object* v_fst_1816_, lean_object* v_val_1817_, lean_object* v_val_1818_, lean_object* v_val_1819_, lean_object* v_snd_1820_, lean_object* v_prom_1821_, lean_object* v___x_1822_, lean_object* v___f_1823_, lean_object* v___f_1824_, lean_object* v___f_1825_, lean_object* v_pos_1826_, lean_object* v_fst_1827_, lean_object* v_cmdState_1828_, lean_object* v_opts_1829_, lean_object* v___x_1830_, lean_object* v_old_x3f_1831_, lean_object* v_parseCancelTk_1832_, lean_object* v_next_x3f_1833_){
_start:
{
lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v_snapshotTasks_1840_; lean_object* v___y_1841_; lean_object* v_traceTask_1842_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; size_t v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v_env_1885_; lean_object* v_messages_1886_; lean_object* v_scopes_1887_; lean_object* v_infoState_1888_; lean_object* v_traceState_1889_; lean_object* v_snapshotTasks_1890_; lean_object* v_reportedCmdState_1891_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; size_t v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v_reportedCmdState_1948_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; size_t v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; size_t v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_2011_; 
if (lean_obj_tag(v_next_x3f_1833_) == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v_parseCancelTk_1832_);
v___x_2064_ = lean_box(0);
v___y_2011_ = v___x_2064_;
goto v___jp_2010_;
}
else
{
lean_object* v_toProcessingContext_2065_; lean_object* v_val_2066_; lean_object* v_pos_2067_; lean_object* v_endPos_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_toProcessingContext_2065_ = lean_ctor_get(v_a_1812_, 0);
v_val_2066_ = lean_ctor_get(v_next_x3f_1833_, 0);
v_pos_2067_ = lean_ctor_get(v_fst_1810_, 0);
v_endPos_2068_ = lean_ctor_get(v_toProcessingContext_2065_, 3);
v___x_2069_ = lean_box(0);
lean_inc(v_endPos_2068_);
lean_inc(v_pos_2067_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_pos_2067_);
lean_ctor_set(v___x_2070_, 1, v_endPos_2068_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_parseCancelTk_1832_);
v___x_2073_ = l_IO_Promise_result_x21___redArg(v_val_2066_);
v___x_2074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2069_);
lean_ctor_set(v___x_2074_, 1, v___x_2071_);
lean_ctor_set(v___x_2074_, 2, v___x_2072_);
lean_ctor_set(v___x_2074_, 3, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
v___y_2011_ = v___x_2075_;
goto v___jp_2010_;
}
v___jp_1835_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1843_, 0, v___y_1837_);
lean_ctor_set(v___x_1843_, 1, v___x_1808_);
lean_ctor_set(v___x_1843_, 2, v___y_1838_);
lean_ctor_set(v___x_1843_, 3, v_traceTask_1842_);
v___x_1844_ = lean_array_push(v_snapshotTasks_1840_, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___y_1841_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_io_promise_resolve(v___x_1845_, v_val_1809_);
if (lean_obj_tag(v_next_x3f_1833_) == 1)
{
lean_object* v_val_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_val_1847_ = lean_ctor_get(v_next_x3f_1833_, 0);
lean_inc(v_val_1847_);
lean_dec_ref(v_next_x3f_1833_);
v___x_1848_ = lean_box(0);
v___x_1849_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1848_, v_fst_1810_, v___y_1839_, v_val_1847_, v_val_1811_, v___y_1836_, v_a_1812_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; 
lean_dec_ref(v___y_1839_);
lean_dec_ref(v___y_1836_);
lean_dec(v_next_x3f_1833_);
lean_dec_ref(v_fst_1810_);
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
}
v___jp_1851_:
{
lean_object* v_snapshotTasks_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_snapshotTasks_1858_ = lean_ctor_get(v___y_1855_, 10);
lean_inc_ref(v_snapshotTasks_1858_);
v___x_1859_ = lean_mk_empty_array_with_capacity(v___y_1857_);
lean_dec(v___y_1857_);
lean_inc_ref(v___y_1856_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1856_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_task_pure(v___x_1860_);
v___y_1836_ = v___y_1853_;
v___y_1837_ = v___y_1852_;
v___y_1838_ = v___y_1854_;
v___y_1839_ = v___y_1855_;
v_snapshotTasks_1840_ = v_snapshotTasks_1858_;
v___y_1841_ = v___y_1856_;
v_traceTask_1842_ = v___x_1861_;
goto v___jp_1835_;
}
v___jp_1862_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_opts_1901_; uint8_t v_hasTrace_1902_; 
v___x_1892_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1886_);
v___x_1893_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1893_, 0, v___y_1875_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
lean_ctor_set(v___x_1893_, 2, v___y_1872_);
lean_ctor_set(v___x_1893_, 3, v_traceState_1889_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*4, v_val_1811_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v_reportedCmdState_1891_);
v___x_1895_ = lean_io_promise_resolve(v___x_1894_, v_val_1818_);
v___x_1896_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1888_);
lean_inc(v___y_1876_);
v___x_1897_ = l_BaseIO_chainTask___redArg(v___x_1896_, v___y_1882_, v___y_1876_, v___x_1815_);
v___x_1898_ = l_Lean_inheritedTraceOptions;
v___x_1899_ = lean_st_ref_get(v___x_1898_);
v___x_1900_ = l_List_head_x21___redArg(v___x_1822_, v_scopes_1887_);
lean_dec(v_scopes_1887_);
lean_dec_ref(v___x_1822_);
v_opts_1901_ = lean_ctor_get(v___x_1900_, 1);
lean_inc_ref(v_opts_1901_);
lean_dec(v___x_1900_);
v_hasTrace_1902_ = lean_ctor_get_uint8(v_opts_1901_, sizeof(void*)*1);
if (v_hasTrace_1902_ == 0)
{
lean_dec_ref(v_opts_1901_);
lean_dec(v___x_1899_);
lean_dec_ref(v_snapshotTasks_1890_);
lean_dec_ref(v_env_1885_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1877_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1863_);
lean_dec(v_pos_1826_);
lean_dec_ref(v___f_1825_);
lean_dec_ref(v___f_1824_);
lean_dec_ref(v___f_1823_);
lean_dec(v___x_1814_);
v___y_1852_ = v___y_1878_;
v___y_1853_ = v___y_1879_;
v___y_1854_ = v___y_1883_;
v___y_1855_ = v___y_1884_;
v___y_1856_ = v___y_1874_;
v___y_1857_ = v___y_1876_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_1904_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1899_, v_opts_1901_, v___x_1903_);
lean_dec(v___x_1899_);
if (v___x_1904_ == 0)
{
lean_dec_ref(v_opts_1901_);
lean_dec_ref(v_snapshotTasks_1890_);
lean_dec_ref(v_env_1885_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1877_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1863_);
lean_dec(v_pos_1826_);
lean_dec_ref(v___f_1825_);
lean_dec_ref(v___f_1824_);
lean_dec_ref(v___f_1823_);
lean_dec(v___x_1814_);
v___y_1852_ = v___y_1878_;
v___y_1853_ = v___y_1879_;
v___y_1854_ = v___y_1883_;
v___y_1855_ = v___y_1884_;
v___y_1856_ = v___y_1874_;
v___y_1857_ = v___y_1876_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; 
lean_inc_n(v___y_1876_, 3);
v___x_1905_ = lean_task_map(v___f_1823_, v___y_1871_, v___y_1876_, v___x_1815_);
lean_inc_n(v___y_1883_, 3);
lean_inc_n(v___y_1873_, 2);
lean_inc_n(v___y_1877_, 2);
v___x_1906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1906_, 0, v___y_1877_);
lean_ctor_set(v___x_1906_, 1, v___y_1873_);
lean_ctor_set(v___x_1906_, 2, v___y_1883_);
lean_ctor_set(v___x_1906_, 3, v___x_1905_);
v___x_1907_ = lean_task_map(v___f_1824_, v___y_1880_, v___y_1876_, v___x_1815_);
v___x_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1908_, 0, v___y_1877_);
lean_ctor_set(v___x_1908_, 1, v___y_1873_);
lean_ctor_set(v___x_1908_, 2, v___y_1883_);
lean_ctor_set(v___x_1908_, 3, v___x_1907_);
v___x_1909_ = lean_task_map(v___f_1825_, v___y_1881_, v___y_1876_, v___x_1815_);
v___x_1910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1910_, 0, v___y_1877_);
lean_ctor_set(v___x_1910_, 1, v___y_1873_);
lean_ctor_set(v___x_1910_, 2, v___y_1883_);
lean_ctor_set(v___x_1910_, 3, v___x_1909_);
v___x_1911_ = lean_unsigned_to_nat(3u);
v___x_1912_ = lean_mk_empty_array_with_capacity(v___x_1911_);
v___x_1913_ = lean_array_push(v___x_1912_, v___x_1906_);
v___x_1914_ = lean_array_push(v___x_1913_, v___x_1908_);
v___x_1915_ = lean_array_push(v___x_1914_, v___x_1910_);
v___x_1916_ = l_Array_append___redArg(v___x_1915_, v_snapshotTasks_1890_);
lean_inc_ref(v___y_1874_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___y_1874_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
lean_inc_ref(v___x_1917_);
v___x_1918_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1917_);
v___x_1919_ = lean_box_usize(v___y_1867_);
v___x_1920_ = lean_box(v___x_1815_);
v___x_1921_ = lean_box(v_val_1811_);
v___x_1922_ = lean_box(v___x_1904_);
lean_inc_ref(v_a_1812_);
lean_inc_ref(v___y_1864_);
v___f_1923_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_1923_, 0, v___x_1814_);
lean_closure_set(v___f_1923_, 1, v___y_1868_);
lean_closure_set(v___f_1923_, 2, v___y_1869_);
lean_closure_set(v___f_1923_, 3, v___x_1919_);
lean_closure_set(v___f_1923_, 4, v___x_1920_);
lean_closure_set(v___f_1923_, 5, v_env_1885_);
lean_closure_set(v___f_1923_, 6, v___y_1864_);
lean_closure_set(v___f_1923_, 7, v___x_1898_);
lean_closure_set(v___f_1923_, 8, v_a_1812_);
lean_closure_set(v___f_1923_, 9, v_opts_1901_);
lean_closure_set(v___f_1923_, 10, v___x_1917_);
lean_closure_set(v___f_1923_, 11, v_pos_1826_);
lean_closure_set(v___f_1923_, 12, v___x_1921_);
lean_closure_set(v___f_1923_, 13, v___y_1863_);
lean_closure_set(v___f_1923_, 14, v___y_1865_);
lean_closure_set(v___f_1923_, 15, v___y_1870_);
lean_closure_set(v___f_1923_, 16, v___y_1866_);
lean_closure_set(v___f_1923_, 17, v___x_1922_);
v___x_1924_ = lean_io_bind_task(v___x_1918_, v___f_1923_, v___y_1876_, v_val_1811_);
v___y_1836_ = v___y_1879_;
v___y_1837_ = v___y_1878_;
v___y_1838_ = v___y_1883_;
v___y_1839_ = v___y_1884_;
v_snapshotTasks_1840_ = v_snapshotTasks_1890_;
v___y_1841_ = v___y_1874_;
v_traceTask_1842_ = v___x_1924_;
goto v___jp_1835_;
}
}
}
v___jp_1925_:
{
lean_object* v_env_1949_; lean_object* v_messages_1950_; lean_object* v_scopes_1951_; lean_object* v_infoState_1952_; lean_object* v_traceState_1953_; lean_object* v_snapshotTasks_1954_; 
v_env_1949_ = lean_ctor_get(v___y_1947_, 0);
lean_inc_ref(v_env_1949_);
v_messages_1950_ = lean_ctor_get(v___y_1947_, 1);
lean_inc_ref(v_messages_1950_);
v_scopes_1951_ = lean_ctor_get(v___y_1947_, 2);
lean_inc(v_scopes_1951_);
v_infoState_1952_ = lean_ctor_get(v___y_1947_, 8);
lean_inc_ref(v_infoState_1952_);
v_traceState_1953_ = lean_ctor_get(v___y_1947_, 9);
lean_inc_ref(v_traceState_1953_);
v_snapshotTasks_1954_ = lean_ctor_get(v___y_1947_, 10);
lean_inc_ref(v_snapshotTasks_1954_);
v___y_1863_ = v___y_1926_;
v___y_1864_ = v___y_1927_;
v___y_1865_ = v___y_1928_;
v___y_1866_ = v___y_1929_;
v___y_1867_ = v___y_1930_;
v___y_1868_ = v___y_1931_;
v___y_1869_ = v___y_1932_;
v___y_1870_ = v___y_1933_;
v___y_1871_ = v___y_1934_;
v___y_1872_ = v___y_1935_;
v___y_1873_ = v___y_1936_;
v___y_1874_ = v___y_1937_;
v___y_1875_ = v___y_1938_;
v___y_1876_ = v___y_1939_;
v___y_1877_ = v___y_1940_;
v___y_1878_ = v___y_1941_;
v___y_1879_ = v___y_1942_;
v___y_1880_ = v___y_1943_;
v___y_1881_ = v___y_1944_;
v___y_1882_ = v___y_1945_;
v___y_1883_ = v___y_1946_;
v___y_1884_ = v___y_1947_;
v_env_1885_ = v_env_1949_;
v_messages_1886_ = v_messages_1950_;
v_scopes_1887_ = v_scopes_1951_;
v_infoState_1888_ = v_infoState_1952_;
v_traceState_1889_ = v_traceState_1953_;
v_snapshotTasks_1890_ = v_snapshotTasks_1954_;
v_reportedCmdState_1891_ = v_reportedCmdState_1948_;
goto v___jp_1862_;
}
v___jp_1955_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; uint8_t v___x_1985_; 
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___y_1979_);
lean_ctor_set(v___x_1980_, 1, v_val_1817_);
lean_inc_ref(v___y_1973_);
lean_inc_n(v_pos_1826_, 2);
lean_inc(v_fst_1827_);
v___x_1981_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1827_, v_cmdState_1828_, v_pos_1826_, v___x_1980_, v___y_1973_, v_a_1812_);
v___x_1982_ = lean_box(v_val_1811_);
v___x_1983_ = lean_box(v___x_1815_);
lean_inc_ref(v_a_1812_);
lean_inc(v___y_1962_);
lean_inc_ref(v___x_1822_);
lean_inc_ref(v___x_1981_);
lean_inc_ref(v___y_1957_);
lean_inc_ref(v___y_1956_);
v___f_1984_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1984_, 0, v___y_1956_);
lean_closure_set(v___f_1984_, 1, v___y_1957_);
lean_closure_set(v___f_1984_, 2, v___x_1982_);
lean_closure_set(v___f_1984_, 3, v_val_1819_);
lean_closure_set(v___f_1984_, 4, v___x_1981_);
lean_closure_set(v___f_1984_, 5, v___x_1822_);
lean_closure_set(v___f_1984_, 6, v___y_1962_);
lean_closure_set(v___f_1984_, 7, v___x_1983_);
lean_closure_set(v___f_1984_, 8, v_a_1812_);
lean_closure_set(v___f_1984_, 9, v_pos_1826_);
v___x_1985_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1829_, v___x_1830_);
if (v___x_1985_ == 0)
{
lean_dec(v___y_1972_);
lean_dec(v_fst_1827_);
lean_inc_ref(v___x_1981_);
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1957_;
v___y_1928_ = v___y_1958_;
v___y_1929_ = v___y_1959_;
v___y_1930_ = v___y_1960_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1965_;
v___y_1935_ = v___y_1966_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1969_;
v___y_1939_ = v___y_1970_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___y_1974_;
v___y_1942_ = v___y_1973_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1978_;
v___y_1945_ = v___f_1984_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___x_1981_;
v_reportedCmdState_1948_ = v___x_1981_;
goto v___jp_1925_;
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Parser_isTerminalCommand(v_fst_1827_);
if (v___x_1986_ == 0)
{
if (v___x_1985_ == 0)
{
lean_dec(v___y_1972_);
lean_inc_ref(v___x_1981_);
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1957_;
v___y_1928_ = v___y_1958_;
v___y_1929_ = v___y_1959_;
v___y_1930_ = v___y_1960_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1965_;
v___y_1935_ = v___y_1966_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1969_;
v___y_1939_ = v___y_1970_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___y_1974_;
v___y_1942_ = v___y_1973_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1978_;
v___y_1945_ = v___f_1984_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___x_1981_;
v_reportedCmdState_1948_ = v___x_1981_;
goto v___jp_1925_;
}
else
{
lean_object* v_env_1987_; lean_object* v_messages_1988_; lean_object* v_scopes_1989_; lean_object* v_infoState_1990_; lean_object* v_traceState_1991_; lean_object* v_snapshotTasks_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_env_1987_ = lean_ctor_get(v___x_1981_, 0);
lean_inc_ref_n(v_env_1987_, 2);
v_messages_1988_ = lean_ctor_get(v___x_1981_, 1);
lean_inc_ref(v_messages_1988_);
v_scopes_1989_ = lean_ctor_get(v___x_1981_, 2);
lean_inc(v_scopes_1989_);
v_infoState_1990_ = lean_ctor_get(v___x_1981_, 8);
lean_inc_ref(v_infoState_1990_);
v_traceState_1991_ = lean_ctor_get(v___x_1981_, 9);
lean_inc_ref(v_traceState_1991_);
v_snapshotTasks_1992_ = lean_ctor_get(v___x_1981_, 10);
lean_inc_ref(v_snapshotTasks_1992_);
v___x_1993_ = lean_mk_empty_array_with_capacity(v___y_1972_);
lean_dec(v___y_1972_);
lean_inc_ref(v___x_1993_);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_inc_n(v___y_1970_, 3);
v___x_1995_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v___x_1993_);
lean_ctor_set(v___x_1995_, 2, v___y_1970_);
lean_ctor_set(v___x_1995_, 3, v___y_1970_);
lean_ctor_set_usize(v___x_1995_, 4, v___y_1975_);
v___x_1996_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1995_, 2);
v___x_1997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1995_);
lean_ctor_set(v___x_1997_, 2, v___x_1996_);
v___x_1998_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1999_ = l_Lean_Options_empty;
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_mk_empty_array_with_capacity(v___y_1970_);
lean_inc_ref_n(v___x_2001_, 3);
lean_inc_n(v___x_1814_, 2);
v___x_2002_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2002_, 0, v___x_1998_);
lean_ctor_set(v___x_2002_, 1, v___x_1999_);
lean_ctor_set(v___x_2002_, 2, v___x_1814_);
lean_ctor_set(v___x_2002_, 3, v___x_2000_);
lean_ctor_set(v___x_2002_, 4, v___x_2000_);
lean_ctor_set(v___x_2002_, 5, v___x_2001_);
lean_ctor_set(v___x_2002_, 6, v___x_2001_);
lean_ctor_set(v___x_2002_, 7, v___x_2000_);
lean_ctor_set(v___x_2002_, 8, v___x_2000_);
lean_ctor_set(v___x_2002_, 9, v___x_2000_);
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*10, v_val_1811_);
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*10 + 1, v_val_1811_);
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*10 + 2, v_val_1811_);
v___x_2003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_2000_);
v___x_2004_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2005_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2006_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1814_);
v___x_2007_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
lean_ctor_set(v___x_2008_, 2, v___x_1995_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*3, v___x_1815_);
lean_inc_ref(v___y_1964_);
v___x_2009_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2009_, 0, v_env_1987_);
lean_ctor_set(v___x_2009_, 1, v___x_1997_);
lean_ctor_set(v___x_2009_, 2, v___x_2003_);
lean_ctor_set(v___x_2009_, 3, v___x_1996_);
lean_ctor_set(v___x_2009_, 4, v___x_2004_);
lean_ctor_set(v___x_2009_, 5, v___y_1970_);
lean_ctor_set(v___x_2009_, 6, v___x_2005_);
lean_ctor_set(v___x_2009_, 7, v___x_2006_);
lean_ctor_set(v___x_2009_, 8, v___x_2008_);
lean_ctor_set(v___x_2009_, 9, v___y_1964_);
lean_ctor_set(v___x_2009_, 10, v___x_2001_);
lean_ctor_set(v___x_2009_, 11, v___x_2001_);
v___y_1863_ = v___y_1956_;
v___y_1864_ = v___y_1957_;
v___y_1865_ = v___y_1958_;
v___y_1866_ = v___y_1959_;
v___y_1867_ = v___y_1960_;
v___y_1868_ = v___y_1961_;
v___y_1869_ = v___y_1962_;
v___y_1870_ = v___y_1963_;
v___y_1871_ = v___y_1965_;
v___y_1872_ = v___y_1966_;
v___y_1873_ = v___y_1967_;
v___y_1874_ = v___y_1968_;
v___y_1875_ = v___y_1969_;
v___y_1876_ = v___y_1970_;
v___y_1877_ = v___y_1971_;
v___y_1878_ = v___y_1974_;
v___y_1879_ = v___y_1973_;
v___y_1880_ = v___y_1976_;
v___y_1881_ = v___y_1978_;
v___y_1882_ = v___f_1984_;
v___y_1883_ = v___y_1977_;
v___y_1884_ = v___x_1981_;
v_env_1885_ = v_env_1987_;
v_messages_1886_ = v_messages_1988_;
v_scopes_1887_ = v_scopes_1989_;
v_infoState_1888_ = v_infoState_1990_;
v_traceState_1889_ = v_traceState_1991_;
v_snapshotTasks_1890_ = v_snapshotTasks_1992_;
v_reportedCmdState_1891_ = v___x_2009_;
goto v___jp_1862_;
}
}
else
{
lean_dec(v___y_1972_);
lean_inc_ref(v___x_1981_);
v___y_1926_ = v___y_1956_;
v___y_1927_ = v___y_1957_;
v___y_1928_ = v___y_1958_;
v___y_1929_ = v___y_1959_;
v___y_1930_ = v___y_1960_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1965_;
v___y_1935_ = v___y_1966_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1969_;
v___y_1939_ = v___y_1970_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___y_1974_;
v___y_1942_ = v___y_1973_;
v___y_1943_ = v___y_1976_;
v___y_1944_ = v___y_1978_;
v___y_1945_ = v___f_1984_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___x_1981_;
v_reportedCmdState_1948_ = v___x_1981_;
goto v___jp_1925_;
}
}
}
v___jp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2012_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1813_);
v___x_2013_ = l_IO_CancelToken_new();
v___x_2014_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1814_);
v___x_2015_ = l_Lean_Name_str___override(v___x_1814_, v___x_2014_);
v___x_2016_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2017_ = l_Lean_Name_str___override(v___x_2015_, v___x_2016_);
v___x_2018_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2019_ = l_Lean_Name_str___override(v___x_2017_, v___x_2018_);
v___x_2020_ = l_Lean_Name_str___override(v___x_2019_, v___x_2016_);
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = l_Lean_Name_num___override(v___x_2020_, v___x_2021_);
v___x_2023_ = l_Lean_Name_str___override(v___x_2022_, v___x_2016_);
v___x_2024_ = l_Lean_Name_str___override(v___x_2023_, v___x_2018_);
v___x_2025_ = l_Lean_Name_str___override(v___x_2024_, v___x_2016_);
v___x_2026_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2027_ = l_Lean_Name_str___override(v___x_2025_, v___x_2026_);
v___x_2028_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2029_ = l_Lean_Name_str___override(v___x_2027_, v___x_2028_);
v___x_2030_ = l_Lean_Name_toString(v___x_2029_, v___x_1815_);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_unsigned_to_nat(32u);
v___x_2033_ = ((size_t)5ULL);
v___x_2034_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2030_, 2);
v___x_2035_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2035_, 0, v___x_2030_);
lean_ctor_set(v___x_2035_, 1, v___x_2012_);
lean_ctor_set(v___x_2035_, 2, v___x_2031_);
lean_ctor_set(v___x_2035_, 3, v___x_2034_);
lean_ctor_set_uint8(v___x_2035_, sizeof(void*)*4, v_val_1811_);
v___x_2036_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2037_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2037_, 0, v___x_2030_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
lean_ctor_set(v___x_2037_, 2, v___x_2031_);
lean_ctor_set(v___x_2037_, 3, v___x_2034_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*4, v_val_1811_);
lean_inc(v_fst_1816_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_fst_1816_);
v___x_2039_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2038_);
lean_inc_ref(v___x_2013_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2013_);
v___x_2041_ = l_IO_Promise_result_x21___redArg(v_val_1817_);
lean_inc_ref(v___x_2041_);
lean_inc(v___x_2039_);
lean_inc_ref_n(v___x_2038_, 3);
v___x_2042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2038_);
lean_ctor_set(v___x_2042_, 1, v___x_2039_);
lean_ctor_set(v___x_2042_, 2, v___x_2040_);
lean_ctor_set(v___x_2042_, 3, v___x_2041_);
v___x_2043_ = l_IO_Promise_result_x21___redArg(v_val_1818_);
lean_inc_ref(v___x_2043_);
lean_inc_n(v___x_1808_, 3);
v___x_2044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2038_);
lean_ctor_set(v___x_2044_, 1, v___x_1808_);
lean_ctor_set(v___x_2044_, 2, v___x_2031_);
lean_ctor_set(v___x_2044_, 3, v___x_2043_);
v___x_2045_ = l_IO_Promise_result_x21___redArg(v_val_1819_);
lean_inc_ref(v___x_2045_);
v___x_2046_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2038_);
lean_ctor_set(v___x_2046_, 1, v___x_1808_);
lean_ctor_set(v___x_2046_, 2, v___x_2031_);
lean_ctor_set(v___x_2046_, 3, v___x_2045_);
v___x_2047_ = l_IO_Promise_result_x21___redArg(v_val_1809_);
v___x_2048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2031_);
lean_ctor_set(v___x_2048_, 1, v___x_1808_);
lean_ctor_set(v___x_2048_, 2, v___x_2031_);
lean_ctor_set(v___x_2048_, 3, v___x_2047_);
lean_inc_ref(v___x_2037_);
v___x_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2037_);
lean_ctor_set(v___x_2049_, 1, v___x_2042_);
lean_ctor_set(v___x_2049_, 2, v___x_2044_);
lean_ctor_set(v___x_2049_, 3, v___x_2046_);
lean_ctor_set(v___x_2049_, 4, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2035_);
lean_ctor_set(v___x_2050_, 1, v_fst_1816_);
lean_ctor_set(v___x_2050_, 2, v_snd_1820_);
lean_ctor_set(v___x_2050_, 3, v___x_2049_);
lean_ctor_set(v___x_2050_, 4, v___y_2011_);
v___x_2051_ = lean_io_promise_resolve(v___x_2050_, v_prom_1821_);
if (lean_obj_tag(v_old_x3f_1831_) == 0)
{
lean_inc_ref(v___x_2037_);
lean_inc_ref(v___x_2030_);
v___y_1956_ = v___x_2030_;
v___y_1957_ = v___x_2034_;
v___y_1958_ = v___x_2031_;
v___y_1959_ = v___x_2031_;
v___y_1960_ = v___x_2033_;
v___y_1961_ = v___x_2032_;
v___y_1962_ = v___x_2021_;
v___y_1963_ = v___x_2037_;
v___y_1964_ = v___x_2034_;
v___y_1965_ = v___x_2041_;
v___y_1966_ = v___x_2031_;
v___y_1967_ = v___x_2039_;
v___y_1968_ = v___x_2037_;
v___y_1969_ = v___x_2030_;
v___y_1970_ = v___x_2021_;
v___y_1971_ = v___x_2038_;
v___y_1972_ = v___x_2032_;
v___y_1973_ = v___x_2013_;
v___y_1974_ = v___x_2031_;
v___y_1975_ = v___x_2033_;
v___y_1976_ = v___x_2043_;
v___y_1977_ = v___x_2031_;
v___y_1978_ = v___x_2045_;
v___y_1979_ = v___x_2031_;
goto v___jp_1955_;
}
else
{
lean_object* v_val_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2063_; 
v_val_2052_ = lean_ctor_get(v_old_x3f_1831_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_old_x3f_1831_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2054_ = v_old_x3f_1831_;
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_val_2052_);
lean_dec(v_old_x3f_1831_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_elabSnap_2056_; lean_object* v_stx_2057_; lean_object* v_elabSnap_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
v_elabSnap_2056_ = lean_ctor_get(v_val_2052_, 3);
lean_inc_ref(v_elabSnap_2056_);
v_stx_2057_ = lean_ctor_get(v_val_2052_, 1);
lean_inc(v_stx_2057_);
lean_dec(v_val_2052_);
v_elabSnap_2058_ = lean_ctor_get(v_elabSnap_2056_, 1);
lean_inc_ref(v_elabSnap_2058_);
lean_dec_ref(v_elabSnap_2056_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_stx_2057_);
lean_ctor_set(v___x_2059_, 1, v_elabSnap_2058_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2059_);
v___x_2061_ = v___x_2054_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_inc_ref(v___x_2037_);
lean_inc_ref(v___x_2030_);
v___y_1956_ = v___x_2030_;
v___y_1957_ = v___x_2034_;
v___y_1958_ = v___x_2031_;
v___y_1959_ = v___x_2031_;
v___y_1960_ = v___x_2033_;
v___y_1961_ = v___x_2032_;
v___y_1962_ = v___x_2021_;
v___y_1963_ = v___x_2037_;
v___y_1964_ = v___x_2034_;
v___y_1965_ = v___x_2041_;
v___y_1966_ = v___x_2031_;
v___y_1967_ = v___x_2039_;
v___y_1968_ = v___x_2037_;
v___y_1969_ = v___x_2030_;
v___y_1970_ = v___x_2021_;
v___y_1971_ = v___x_2038_;
v___y_1972_ = v___x_2032_;
v___y_1973_ = v___x_2013_;
v___y_1974_ = v___x_2031_;
v___y_1975_ = v___x_2033_;
v___y_1976_ = v___x_2043_;
v___y_1977_ = v___x_2031_;
v___y_1978_ = v___x_2045_;
v___y_1979_ = v___x_2061_;
goto v___jp_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_fst_2076_, uint8_t v_val_2077_, lean_object* v_a_2078_, lean_object* v_snd_2079_, lean_object* v___x_2080_, uint8_t v___x_2081_, lean_object* v_prom_2082_, lean_object* v___x_2083_, lean_object* v___f_2084_, lean_object* v___f_2085_, lean_object* v___f_2086_, lean_object* v_pos_2087_, lean_object* v_fst_2088_, lean_object* v_cmdState_2089_, lean_object* v_opts_2090_, lean_object* v_old_x3f_2091_, lean_object* v_parseCancelTk_2092_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v_snapshotTasks_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v_traceTask_2107_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; size_t v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v_env_2144_; lean_object* v_messages_2145_; lean_object* v_scopes_2146_; lean_object* v_infoState_2147_; lean_object* v_traceState_2148_; lean_object* v_snapshotTasks_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v_reportedCmdState_2160_; size_t v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v_reportedCmdState_2219_; lean_object* v___x_2226_; size_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; size_t v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v_fst_2363_; lean_object* v_snd_2364_; uint8_t v___y_2377_; uint8_t v___x_2380_; 
v___x_2094_ = lean_io_promise_new();
v___x_2095_ = lean_io_promise_new();
v___x_2096_ = lean_io_promise_new();
v___x_2097_ = lean_io_promise_new();
v___x_2226_ = l_Lean_internal_cmdlineSnapshots;
v___x_2380_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2090_, v___x_2226_);
if (v___x_2380_ == 0)
{
v___y_2377_ = v___x_2380_;
goto v___jp_2376_;
}
else
{
uint8_t v___x_2381_; 
lean_inc(v_fst_2088_);
v___x_2381_ = l_Lean_Parser_isTerminalCommand(v_fst_2088_);
if (v___x_2381_ == 0)
{
v___y_2377_ = v___x_2380_;
goto v___jp_2376_;
}
else
{
lean_inc_ref(v_fst_2076_);
lean_inc(v_fst_2088_);
v_fst_2363_ = v_fst_2088_;
v_snd_2364_ = v_fst_2076_;
goto v___jp_2362_;
}
}
v___jp_2098_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2108_, 0, v___y_2106_);
lean_ctor_set(v___x_2108_, 1, v___y_2105_);
lean_ctor_set(v___x_2108_, 2, v___y_2100_);
lean_ctor_set(v___x_2108_, 3, v_traceTask_2107_);
v___x_2109_ = lean_array_push(v_snapshotTasks_2104_, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___y_2101_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_io_promise_resolve(v___x_2110_, v___x_2097_);
lean_dec(v___x_2097_);
if (lean_obj_tag(v___y_2102_) == 1)
{
lean_object* v_val_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_val_2112_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_val_2112_);
lean_dec_ref(v___y_2102_);
v___x_2113_ = lean_box(0);
v___x_2114_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2113_, v_fst_2076_, v___y_2103_, v_val_2112_, v_val_2077_, v___y_2099_, v_a_2078_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; 
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2099_);
lean_dec_ref(v_fst_2076_);
v___x_2115_ = lean_box(0);
return v___x_2115_;
}
}
v___jp_2116_:
{
lean_object* v_snapshotTasks_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_snapshotTasks_2125_ = lean_ctor_get(v___y_2120_, 10);
lean_inc_ref(v_snapshotTasks_2125_);
v___x_2126_ = lean_mk_empty_array_with_capacity(v___y_2124_);
lean_dec(v___y_2124_);
lean_inc_ref(v___y_2119_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___y_2119_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_task_pure(v___x_2127_);
v___y_2099_ = v___y_2117_;
v___y_2100_ = v___y_2118_;
v___y_2101_ = v___y_2119_;
v___y_2102_ = v___y_2121_;
v___y_2103_ = v___y_2120_;
v_snapshotTasks_2104_ = v_snapshotTasks_2125_;
v___y_2105_ = v___y_2122_;
v___y_2106_ = v___y_2123_;
v_traceTask_2107_ = v___x_2128_;
goto v___jp_2098_;
}
v___jp_2129_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v_opts_2170_; uint8_t v_hasTrace_2171_; 
v___x_2161_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2145_);
v___x_2162_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2162_, 0, v___y_2155_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
lean_ctor_set(v___x_2162_, 2, v___y_2150_);
lean_ctor_set(v___x_2162_, 3, v_traceState_2148_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*4, v_val_2077_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v_reportedCmdState_2160_);
v___x_2164_ = lean_io_promise_resolve(v___x_2163_, v___x_2095_);
lean_dec(v___x_2095_);
v___x_2165_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2147_);
lean_inc(v___y_2159_);
v___x_2166_ = l_BaseIO_chainTask___redArg(v___x_2165_, v___y_2154_, v___y_2159_, v___x_2081_);
v___x_2167_ = l_Lean_inheritedTraceOptions;
v___x_2168_ = lean_st_ref_get(v___x_2167_);
v___x_2169_ = l_List_head_x21___redArg(v___x_2083_, v_scopes_2146_);
lean_dec(v_scopes_2146_);
lean_dec_ref(v___x_2083_);
v_opts_2170_ = lean_ctor_get(v___x_2169_, 1);
lean_inc_ref(v_opts_2170_);
lean_dec(v___x_2169_);
v_hasTrace_2171_ = lean_ctor_get_uint8(v_opts_2170_, sizeof(void*)*1);
if (v_hasTrace_2171_ == 0)
{
lean_dec_ref(v_opts_2170_);
lean_dec(v___x_2168_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v_snapshotTasks_2149_);
lean_dec_ref(v_env_2144_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v_pos_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v___f_2085_);
lean_dec_ref(v___f_2084_);
lean_dec(v___x_2080_);
v___y_2117_ = v___y_2139_;
v___y_2118_ = v___y_2140_;
v___y_2119_ = v___y_2142_;
v___y_2120_ = v___y_2143_;
v___y_2121_ = v___y_2151_;
v___y_2122_ = v___y_2157_;
v___y_2123_ = v___y_2158_;
v___y_2124_ = v___y_2159_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2173_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2168_, v_opts_2170_, v___x_2172_);
lean_dec(v___x_2168_);
if (v___x_2173_ == 0)
{
lean_dec_ref(v_opts_2170_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v_snapshotTasks_2149_);
lean_dec_ref(v_env_2144_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v_pos_2087_);
lean_dec_ref(v___f_2086_);
lean_dec_ref(v___f_2085_);
lean_dec_ref(v___f_2084_);
lean_dec(v___x_2080_);
v___y_2117_ = v___y_2139_;
v___y_2118_ = v___y_2140_;
v___y_2119_ = v___y_2142_;
v___y_2120_ = v___y_2143_;
v___y_2121_ = v___y_2151_;
v___y_2122_ = v___y_2157_;
v___y_2123_ = v___y_2158_;
v___y_2124_ = v___y_2159_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; 
lean_inc_n(v___y_2159_, 3);
v___x_2174_ = lean_task_map(v___f_2084_, v___y_2152_, v___y_2159_, v___x_2081_);
lean_inc_n(v___y_2140_, 3);
lean_inc_n(v___y_2138_, 2);
lean_inc_n(v___y_2153_, 2);
v___x_2175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2175_, 0, v___y_2153_);
lean_ctor_set(v___x_2175_, 1, v___y_2138_);
lean_ctor_set(v___x_2175_, 2, v___y_2140_);
lean_ctor_set(v___x_2175_, 3, v___x_2174_);
v___x_2176_ = lean_task_map(v___f_2085_, v___y_2141_, v___y_2159_, v___x_2081_);
v___x_2177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2177_, 0, v___y_2153_);
lean_ctor_set(v___x_2177_, 1, v___y_2138_);
lean_ctor_set(v___x_2177_, 2, v___y_2140_);
lean_ctor_set(v___x_2177_, 3, v___x_2176_);
v___x_2178_ = lean_task_map(v___f_2086_, v___y_2156_, v___y_2159_, v___x_2081_);
v___x_2179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2179_, 0, v___y_2153_);
lean_ctor_set(v___x_2179_, 1, v___y_2138_);
lean_ctor_set(v___x_2179_, 2, v___y_2140_);
lean_ctor_set(v___x_2179_, 3, v___x_2178_);
v___x_2180_ = lean_unsigned_to_nat(3u);
v___x_2181_ = lean_mk_empty_array_with_capacity(v___x_2180_);
v___x_2182_ = lean_array_push(v___x_2181_, v___x_2175_);
v___x_2183_ = lean_array_push(v___x_2182_, v___x_2177_);
v___x_2184_ = lean_array_push(v___x_2183_, v___x_2179_);
v___x_2185_ = l_Array_append___redArg(v___x_2184_, v_snapshotTasks_2149_);
lean_inc_ref(v___y_2142_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2142_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
lean_inc_ref(v___x_2186_);
v___x_2187_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2186_);
v___x_2188_ = lean_box_usize(v___y_2130_);
v___x_2189_ = lean_box(v___x_2081_);
v___x_2190_ = lean_box(v_val_2077_);
v___x_2191_ = lean_box(v___x_2173_);
lean_inc_ref(v_a_2078_);
lean_inc_ref(v___y_2133_);
v___f_2192_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2192_, 0, v___x_2080_);
lean_closure_set(v___f_2192_, 1, v___y_2135_);
lean_closure_set(v___f_2192_, 2, v___y_2136_);
lean_closure_set(v___f_2192_, 3, v___x_2188_);
lean_closure_set(v___f_2192_, 4, v___x_2189_);
lean_closure_set(v___f_2192_, 5, v_env_2144_);
lean_closure_set(v___f_2192_, 6, v___y_2133_);
lean_closure_set(v___f_2192_, 7, v___x_2167_);
lean_closure_set(v___f_2192_, 8, v_a_2078_);
lean_closure_set(v___f_2192_, 9, v_opts_2170_);
lean_closure_set(v___f_2192_, 10, v___x_2186_);
lean_closure_set(v___f_2192_, 11, v_pos_2087_);
lean_closure_set(v___f_2192_, 12, v___x_2190_);
lean_closure_set(v___f_2192_, 13, v___y_2131_);
lean_closure_set(v___f_2192_, 14, v___y_2137_);
lean_closure_set(v___f_2192_, 15, v___y_2134_);
lean_closure_set(v___f_2192_, 16, v___y_2132_);
lean_closure_set(v___f_2192_, 17, v___x_2191_);
v___x_2193_ = lean_io_bind_task(v___x_2187_, v___f_2192_, v___y_2159_, v_val_2077_);
v___y_2099_ = v___y_2139_;
v___y_2100_ = v___y_2140_;
v___y_2101_ = v___y_2142_;
v___y_2102_ = v___y_2151_;
v___y_2103_ = v___y_2143_;
v_snapshotTasks_2104_ = v_snapshotTasks_2149_;
v___y_2105_ = v___y_2157_;
v___y_2106_ = v___y_2158_;
v_traceTask_2107_ = v___x_2193_;
goto v___jp_2098_;
}
}
}
v___jp_2194_:
{
lean_object* v_env_2220_; lean_object* v_messages_2221_; lean_object* v_scopes_2222_; lean_object* v_infoState_2223_; lean_object* v_traceState_2224_; lean_object* v_snapshotTasks_2225_; 
v_env_2220_ = lean_ctor_get(v___y_2208_, 0);
lean_inc_ref(v_env_2220_);
v_messages_2221_ = lean_ctor_get(v___y_2208_, 1);
lean_inc_ref(v_messages_2221_);
v_scopes_2222_ = lean_ctor_get(v___y_2208_, 2);
lean_inc(v_scopes_2222_);
v_infoState_2223_ = lean_ctor_get(v___y_2208_, 8);
lean_inc_ref(v_infoState_2223_);
v_traceState_2224_ = lean_ctor_get(v___y_2208_, 9);
lean_inc_ref(v_traceState_2224_);
v_snapshotTasks_2225_ = lean_ctor_get(v___y_2208_, 10);
lean_inc_ref(v_snapshotTasks_2225_);
v___y_2130_ = v___y_2195_;
v___y_2131_ = v___y_2196_;
v___y_2132_ = v___y_2198_;
v___y_2133_ = v___y_2197_;
v___y_2134_ = v___y_2199_;
v___y_2135_ = v___y_2200_;
v___y_2136_ = v___y_2201_;
v___y_2137_ = v___y_2202_;
v___y_2138_ = v___y_2203_;
v___y_2139_ = v___y_2204_;
v___y_2140_ = v___y_2205_;
v___y_2141_ = v___y_2206_;
v___y_2142_ = v___y_2207_;
v___y_2143_ = v___y_2208_;
v_env_2144_ = v_env_2220_;
v_messages_2145_ = v_messages_2221_;
v_scopes_2146_ = v_scopes_2222_;
v_infoState_2147_ = v_infoState_2223_;
v_traceState_2148_ = v_traceState_2224_;
v_snapshotTasks_2149_ = v_snapshotTasks_2225_;
v___y_2150_ = v___y_2209_;
v___y_2151_ = v___y_2210_;
v___y_2152_ = v___y_2211_;
v___y_2153_ = v___y_2212_;
v___y_2154_ = v___y_2213_;
v___y_2155_ = v___y_2214_;
v___y_2156_ = v___y_2215_;
v___y_2157_ = v___y_2216_;
v___y_2158_ = v___y_2217_;
v___y_2159_ = v___y_2218_;
v_reportedCmdState_2160_ = v_reportedCmdState_2219_;
goto v___jp_2129_;
}
v___jp_2227_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; uint8_t v___x_2259_; 
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___y_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2094_);
lean_inc_ref(v___y_2237_);
lean_inc_n(v_pos_2087_, 2);
lean_inc(v_fst_2088_);
v___x_2255_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2088_, v_cmdState_2089_, v_pos_2087_, v___x_2254_, v___y_2237_, v_a_2078_);
v___x_2256_ = lean_box(v_val_2077_);
v___x_2257_ = lean_box(v___x_2081_);
lean_inc_ref(v_a_2078_);
lean_inc(v___y_2234_);
lean_inc_ref(v___x_2083_);
lean_inc_ref(v___x_2255_);
lean_inc_ref(v___y_2231_);
lean_inc_ref(v___y_2229_);
v___f_2258_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2258_, 0, v___y_2229_);
lean_closure_set(v___f_2258_, 1, v___y_2231_);
lean_closure_set(v___f_2258_, 2, v___x_2256_);
lean_closure_set(v___f_2258_, 3, v___x_2096_);
lean_closure_set(v___f_2258_, 4, v___x_2255_);
lean_closure_set(v___f_2258_, 5, v___x_2083_);
lean_closure_set(v___f_2258_, 6, v___y_2234_);
lean_closure_set(v___f_2258_, 7, v___x_2257_);
lean_closure_set(v___f_2258_, 8, v_a_2078_);
lean_closure_set(v___f_2258_, 9, v_pos_2087_);
v___x_2259_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2090_, v___x_2226_);
if (v___x_2259_ == 0)
{
lean_dec(v___y_2248_);
lean_dec(v_fst_2088_);
lean_inc_ref(v___x_2255_);
v___y_2195_ = v___y_2228_;
v___y_2196_ = v___y_2229_;
v___y_2197_ = v___y_2231_;
v___y_2198_ = v___y_2230_;
v___y_2199_ = v___y_2232_;
v___y_2200_ = v___y_2233_;
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___x_2255_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2241_;
v___y_2211_ = v___y_2243_;
v___y_2212_ = v___y_2244_;
v___y_2213_ = v___f_2258_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2249_;
v___y_2216_ = v___y_2250_;
v___y_2217_ = v___y_2251_;
v___y_2218_ = v___y_2252_;
v_reportedCmdState_2219_ = v___x_2255_;
goto v___jp_2194_;
}
else
{
uint8_t v___x_2260_; 
v___x_2260_ = l_Lean_Parser_isTerminalCommand(v_fst_2088_);
if (v___x_2260_ == 0)
{
if (v___x_2259_ == 0)
{
lean_dec(v___y_2248_);
lean_inc_ref(v___x_2255_);
v___y_2195_ = v___y_2228_;
v___y_2196_ = v___y_2229_;
v___y_2197_ = v___y_2231_;
v___y_2198_ = v___y_2230_;
v___y_2199_ = v___y_2232_;
v___y_2200_ = v___y_2233_;
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___x_2255_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2241_;
v___y_2211_ = v___y_2243_;
v___y_2212_ = v___y_2244_;
v___y_2213_ = v___f_2258_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2249_;
v___y_2216_ = v___y_2250_;
v___y_2217_ = v___y_2251_;
v___y_2218_ = v___y_2252_;
v_reportedCmdState_2219_ = v___x_2255_;
goto v___jp_2194_;
}
else
{
lean_object* v_env_2261_; lean_object* v_messages_2262_; lean_object* v_scopes_2263_; lean_object* v_infoState_2264_; lean_object* v_traceState_2265_; lean_object* v_snapshotTasks_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_env_2261_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref_n(v_env_2261_, 2);
v_messages_2262_ = lean_ctor_get(v___x_2255_, 1);
lean_inc_ref(v_messages_2262_);
v_scopes_2263_ = lean_ctor_get(v___x_2255_, 2);
lean_inc(v_scopes_2263_);
v_infoState_2264_ = lean_ctor_get(v___x_2255_, 8);
lean_inc_ref(v_infoState_2264_);
v_traceState_2265_ = lean_ctor_get(v___x_2255_, 9);
lean_inc_ref(v_traceState_2265_);
v_snapshotTasks_2266_ = lean_ctor_get(v___x_2255_, 10);
lean_inc_ref(v_snapshotTasks_2266_);
v___x_2267_ = lean_mk_empty_array_with_capacity(v___y_2248_);
lean_dec(v___y_2248_);
lean_inc_ref(v___x_2267_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_inc_n(v___y_2252_, 3);
v___x_2269_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2267_);
lean_ctor_set(v___x_2269_, 2, v___y_2252_);
lean_ctor_set(v___x_2269_, 3, v___y_2252_);
lean_ctor_set_usize(v___x_2269_, 4, v___y_2245_);
v___x_2270_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2269_, 2);
v___x_2271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2269_);
lean_ctor_set(v___x_2271_, 2, v___x_2270_);
v___x_2272_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2273_ = l_Lean_Options_empty;
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_mk_empty_array_with_capacity(v___y_2252_);
lean_inc_ref_n(v___x_2275_, 3);
lean_inc_n(v___x_2080_, 2);
v___x_2276_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2276_, 0, v___x_2272_);
lean_ctor_set(v___x_2276_, 1, v___x_2273_);
lean_ctor_set(v___x_2276_, 2, v___x_2080_);
lean_ctor_set(v___x_2276_, 3, v___x_2274_);
lean_ctor_set(v___x_2276_, 4, v___x_2274_);
lean_ctor_set(v___x_2276_, 5, v___x_2275_);
lean_ctor_set(v___x_2276_, 6, v___x_2275_);
lean_ctor_set(v___x_2276_, 7, v___x_2274_);
lean_ctor_set(v___x_2276_, 8, v___x_2274_);
lean_ctor_set(v___x_2276_, 9, v___x_2274_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*10, v_val_2077_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*10 + 1, v_val_2077_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*10 + 2, v_val_2077_);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___x_2274_);
v___x_2278_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2279_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2280_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2080_);
v___x_2281_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2282_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
lean_ctor_set(v___x_2282_, 2, v___x_2269_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*3, v___x_2081_);
lean_inc_ref(v___y_2247_);
v___x_2283_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2283_, 0, v_env_2261_);
lean_ctor_set(v___x_2283_, 1, v___x_2271_);
lean_ctor_set(v___x_2283_, 2, v___x_2277_);
lean_ctor_set(v___x_2283_, 3, v___x_2270_);
lean_ctor_set(v___x_2283_, 4, v___x_2278_);
lean_ctor_set(v___x_2283_, 5, v___y_2252_);
lean_ctor_set(v___x_2283_, 6, v___x_2279_);
lean_ctor_set(v___x_2283_, 7, v___x_2280_);
lean_ctor_set(v___x_2283_, 8, v___x_2282_);
lean_ctor_set(v___x_2283_, 9, v___y_2247_);
lean_ctor_set(v___x_2283_, 10, v___x_2275_);
lean_ctor_set(v___x_2283_, 11, v___x_2275_);
v___y_2130_ = v___y_2228_;
v___y_2131_ = v___y_2229_;
v___y_2132_ = v___y_2230_;
v___y_2133_ = v___y_2231_;
v___y_2134_ = v___y_2232_;
v___y_2135_ = v___y_2233_;
v___y_2136_ = v___y_2234_;
v___y_2137_ = v___y_2235_;
v___y_2138_ = v___y_2236_;
v___y_2139_ = v___y_2237_;
v___y_2140_ = v___y_2238_;
v___y_2141_ = v___y_2239_;
v___y_2142_ = v___y_2240_;
v___y_2143_ = v___x_2255_;
v_env_2144_ = v_env_2261_;
v_messages_2145_ = v_messages_2262_;
v_scopes_2146_ = v_scopes_2263_;
v_infoState_2147_ = v_infoState_2264_;
v_traceState_2148_ = v_traceState_2265_;
v_snapshotTasks_2149_ = v_snapshotTasks_2266_;
v___y_2150_ = v___y_2242_;
v___y_2151_ = v___y_2241_;
v___y_2152_ = v___y_2243_;
v___y_2153_ = v___y_2244_;
v___y_2154_ = v___f_2258_;
v___y_2155_ = v___y_2246_;
v___y_2156_ = v___y_2249_;
v___y_2157_ = v___y_2250_;
v___y_2158_ = v___y_2251_;
v___y_2159_ = v___y_2252_;
v_reportedCmdState_2160_ = v___x_2283_;
goto v___jp_2129_;
}
}
else
{
lean_dec(v___y_2248_);
lean_inc_ref(v___x_2255_);
v___y_2195_ = v___y_2228_;
v___y_2196_ = v___y_2229_;
v___y_2197_ = v___y_2231_;
v___y_2198_ = v___y_2230_;
v___y_2199_ = v___y_2232_;
v___y_2200_ = v___y_2233_;
v___y_2201_ = v___y_2234_;
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___x_2255_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2241_;
v___y_2211_ = v___y_2243_;
v___y_2212_ = v___y_2244_;
v___y_2213_ = v___f_2258_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2249_;
v___y_2216_ = v___y_2250_;
v___y_2217_ = v___y_2251_;
v___y_2218_ = v___y_2252_;
v_reportedCmdState_2219_ = v___x_2255_;
goto v___jp_2194_;
}
}
}
v___jp_2284_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2290_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2079_);
v___x_2291_ = l_IO_CancelToken_new();
v___x_2292_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2080_);
v___x_2293_ = l_Lean_Name_str___override(v___x_2080_, v___x_2292_);
v___x_2294_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2295_ = l_Lean_Name_str___override(v___x_2293_, v___x_2294_);
v___x_2296_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2297_ = l_Lean_Name_str___override(v___x_2295_, v___x_2296_);
v___x_2298_ = l_Lean_Name_str___override(v___x_2297_, v___x_2294_);
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = l_Lean_Name_num___override(v___x_2298_, v___x_2299_);
v___x_2301_ = l_Lean_Name_str___override(v___x_2300_, v___x_2294_);
v___x_2302_ = l_Lean_Name_str___override(v___x_2301_, v___x_2296_);
v___x_2303_ = l_Lean_Name_str___override(v___x_2302_, v___x_2294_);
v___x_2304_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2305_ = l_Lean_Name_str___override(v___x_2303_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2307_ = l_Lean_Name_str___override(v___x_2305_, v___x_2306_);
v___x_2308_ = l_Lean_Name_toString(v___x_2307_, v___x_2081_);
v___x_2309_ = lean_box(0);
v___x_2310_ = lean_unsigned_to_nat(32u);
v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
lean_dec_ref(v___x_2311_);
v___x_2312_ = ((size_t)5ULL);
v___x_2313_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2308_, 2);
v___x_2314_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2314_, 0, v___x_2308_);
lean_ctor_set(v___x_2314_, 1, v___x_2290_);
lean_ctor_set(v___x_2314_, 2, v___x_2309_);
lean_ctor_set(v___x_2314_, 3, v___x_2313_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*4, v_val_2077_);
v___x_2315_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2316_, 0, v___x_2308_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
lean_ctor_set(v___x_2316_, 2, v___x_2309_);
lean_ctor_set(v___x_2316_, 3, v___x_2313_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*4, v_val_2077_);
lean_inc(v___y_2288_);
v___x_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___y_2288_);
v___x_2318_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2317_);
lean_inc_ref(v___x_2291_);
v___x_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2291_);
v___x_2320_ = l_IO_Promise_result_x21___redArg(v___x_2094_);
lean_inc_ref(v___x_2320_);
lean_inc(v___x_2318_);
lean_inc_ref_n(v___x_2317_, 3);
v___x_2321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2317_);
lean_ctor_set(v___x_2321_, 1, v___x_2318_);
lean_ctor_set(v___x_2321_, 2, v___x_2319_);
lean_ctor_set(v___x_2321_, 3, v___x_2320_);
v___x_2322_ = l_IO_Promise_result_x21___redArg(v___x_2095_);
lean_inc_ref(v___x_2322_);
lean_inc_n(v___y_2286_, 3);
v___x_2323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2317_);
lean_ctor_set(v___x_2323_, 1, v___y_2286_);
lean_ctor_set(v___x_2323_, 2, v___x_2309_);
lean_ctor_set(v___x_2323_, 3, v___x_2322_);
v___x_2324_ = l_IO_Promise_result_x21___redArg(v___x_2096_);
lean_inc_ref(v___x_2324_);
v___x_2325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2317_);
lean_ctor_set(v___x_2325_, 1, v___y_2286_);
lean_ctor_set(v___x_2325_, 2, v___x_2309_);
lean_ctor_set(v___x_2325_, 3, v___x_2324_);
v___x_2326_ = l_IO_Promise_result_x21___redArg(v___x_2097_);
v___x_2327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2309_);
lean_ctor_set(v___x_2327_, 1, v___y_2286_);
lean_ctor_set(v___x_2327_, 2, v___x_2309_);
lean_ctor_set(v___x_2327_, 3, v___x_2326_);
lean_inc_ref(v___x_2316_);
v___x_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2316_);
lean_ctor_set(v___x_2328_, 1, v___x_2321_);
lean_ctor_set(v___x_2328_, 2, v___x_2323_);
lean_ctor_set(v___x_2328_, 3, v___x_2325_);
lean_ctor_set(v___x_2328_, 4, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2314_);
lean_ctor_set(v___x_2329_, 1, v___y_2288_);
lean_ctor_set(v___x_2329_, 2, v___y_2287_);
lean_ctor_set(v___x_2329_, 3, v___x_2328_);
lean_ctor_set(v___x_2329_, 4, v___y_2289_);
v___x_2330_ = lean_io_promise_resolve(v___x_2329_, v_prom_2082_);
if (lean_obj_tag(v_old_x3f_2091_) == 0)
{
lean_inc_ref(v___x_2316_);
lean_inc_ref(v___x_2308_);
v___y_2228_ = v___x_2312_;
v___y_2229_ = v___x_2308_;
v___y_2230_ = v___x_2309_;
v___y_2231_ = v___x_2313_;
v___y_2232_ = v___x_2316_;
v___y_2233_ = v___x_2310_;
v___y_2234_ = v___x_2299_;
v___y_2235_ = v___x_2309_;
v___y_2236_ = v___x_2318_;
v___y_2237_ = v___x_2291_;
v___y_2238_ = v___x_2309_;
v___y_2239_ = v___x_2322_;
v___y_2240_ = v___x_2316_;
v___y_2241_ = v___y_2285_;
v___y_2242_ = v___x_2309_;
v___y_2243_ = v___x_2320_;
v___y_2244_ = v___x_2317_;
v___y_2245_ = v___x_2312_;
v___y_2246_ = v___x_2308_;
v___y_2247_ = v___x_2313_;
v___y_2248_ = v___x_2310_;
v___y_2249_ = v___x_2324_;
v___y_2250_ = v___y_2286_;
v___y_2251_ = v___x_2309_;
v___y_2252_ = v___x_2299_;
v___y_2253_ = v___x_2309_;
goto v___jp_2227_;
}
else
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2342_; 
v_val_2331_ = lean_ctor_get(v_old_x3f_2091_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_old_x3f_2091_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2333_ = v_old_x3f_2091_;
v_isShared_2334_ = v_isSharedCheck_2342_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v_old_x3f_2091_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2342_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_elabSnap_2335_; lean_object* v_stx_2336_; lean_object* v_elabSnap_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v_elabSnap_2335_ = lean_ctor_get(v_val_2331_, 3);
lean_inc_ref(v_elabSnap_2335_);
v_stx_2336_ = lean_ctor_get(v_val_2331_, 1);
lean_inc(v_stx_2336_);
lean_dec(v_val_2331_);
v_elabSnap_2337_ = lean_ctor_get(v_elabSnap_2335_, 1);
lean_inc_ref(v_elabSnap_2337_);
lean_dec_ref(v_elabSnap_2335_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_stx_2336_);
lean_ctor_set(v___x_2338_, 1, v_elabSnap_2337_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2338_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_inc_ref(v___x_2316_);
lean_inc_ref(v___x_2308_);
v___y_2228_ = v___x_2312_;
v___y_2229_ = v___x_2308_;
v___y_2230_ = v___x_2309_;
v___y_2231_ = v___x_2313_;
v___y_2232_ = v___x_2316_;
v___y_2233_ = v___x_2310_;
v___y_2234_ = v___x_2299_;
v___y_2235_ = v___x_2309_;
v___y_2236_ = v___x_2318_;
v___y_2237_ = v___x_2291_;
v___y_2238_ = v___x_2309_;
v___y_2239_ = v___x_2322_;
v___y_2240_ = v___x_2316_;
v___y_2241_ = v___y_2285_;
v___y_2242_ = v___x_2309_;
v___y_2243_ = v___x_2320_;
v___y_2244_ = v___x_2317_;
v___y_2245_ = v___x_2312_;
v___y_2246_ = v___x_2308_;
v___y_2247_ = v___x_2313_;
v___y_2248_ = v___x_2310_;
v___y_2249_ = v___x_2324_;
v___y_2250_ = v___y_2286_;
v___y_2251_ = v___x_2309_;
v___y_2252_ = v___x_2299_;
v___y_2253_ = v___x_2340_;
goto v___jp_2227_;
}
}
}
}
v___jp_2343_:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2346_);
lean_inc(v_fst_2088_);
v___x_2348_ = l_Lean_Parser_isTerminalCommand(v_fst_2088_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v_toProcessingContext_2350_; lean_object* v_pos_2351_; lean_object* v_endPos_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2349_ = lean_io_promise_new();
v_toProcessingContext_2350_ = lean_ctor_get(v_a_2078_, 0);
v_pos_2351_ = lean_ctor_get(v_fst_2076_, 0);
v_endPos_2352_ = lean_ctor_get(v_toProcessingContext_2350_, 3);
lean_inc(v___x_2349_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2349_);
v___x_2354_ = lean_box(0);
lean_inc(v_endPos_2352_);
lean_inc(v_pos_2351_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_pos_2351_);
lean_ctor_set(v___x_2355_, 1, v_endPos_2352_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_parseCancelTk_2092_);
v___x_2358_ = l_IO_Promise_result_x21___redArg(v___x_2349_);
lean_dec(v___x_2349_);
v___x_2359_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2354_);
lean_ctor_set(v___x_2359_, 1, v___x_2356_);
lean_ctor_set(v___x_2359_, 2, v___x_2357_);
lean_ctor_set(v___x_2359_, 3, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
v___y_2285_ = v___x_2353_;
v___y_2286_ = v___x_2347_;
v___y_2287_ = v___y_2344_;
v___y_2288_ = v___y_2345_;
v___y_2289_ = v___x_2360_;
goto v___jp_2284_;
}
else
{
lean_object* v___x_2361_; 
lean_dec_ref(v_parseCancelTk_2092_);
v___x_2361_ = lean_box(0);
v___y_2285_ = v___x_2361_;
v___y_2286_ = v___x_2347_;
v___y_2287_ = v___y_2344_;
v___y_2288_ = v___y_2345_;
v___y_2289_ = v___x_2361_;
goto v___jp_2284_;
}
}
v___jp_2362_:
{
lean_object* v___x_2365_; 
lean_inc(v_fst_2088_);
v___x_2365_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2088_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_box(0);
v___y_2344_ = v_snd_2364_;
v___y_2345_ = v_fst_2363_;
v___y_2346_ = v___x_2366_;
goto v___jp_2343_;
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2375_; 
v_val_2367_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2369_ = v___x_2365_;
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_val_2367_);
lean_dec(v___x_2365_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_inc(v_val_2367_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_val_2367_);
lean_ctor_set(v___x_2371_, 1, v_val_2367_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
v___y_2344_ = v_snd_2364_;
v___y_2345_ = v_fst_2363_;
v___y_2346_ = v___x_2373_;
goto v___jp_2343_;
}
}
}
}
v___jp_2376_:
{
if (v___y_2377_ == 0)
{
lean_inc_ref(v_fst_2076_);
lean_inc(v_fst_2088_);
v_fst_2363_ = v_fst_2088_;
v_snd_2364_ = v_fst_2076_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_box(0);
v___x_2379_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2363_ = v___x_2378_;
v_snd_2364_ = v___x_2379_;
goto v___jp_2362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_fst_2382_ = _args[0];
lean_object* v_val_2383_ = _args[1];
lean_object* v_a_2384_ = _args[2];
lean_object* v_snd_2385_ = _args[3];
lean_object* v___x_2386_ = _args[4];
lean_object* v___x_2387_ = _args[5];
lean_object* v_prom_2388_ = _args[6];
lean_object* v___x_2389_ = _args[7];
lean_object* v___f_2390_ = _args[8];
lean_object* v___f_2391_ = _args[9];
lean_object* v___f_2392_ = _args[10];
lean_object* v_pos_2393_ = _args[11];
lean_object* v_fst_2394_ = _args[12];
lean_object* v_cmdState_2395_ = _args[13];
lean_object* v_opts_2396_ = _args[14];
lean_object* v_old_x3f_2397_ = _args[15];
lean_object* v_parseCancelTk_2398_ = _args[16];
lean_object* v___y_2399_ = _args[17];
_start:
{
uint8_t v_val_45914__boxed_2400_; uint8_t v___x_45917__boxed_2401_; lean_object* v_res_2402_; 
v_val_45914__boxed_2400_ = lean_unbox(v_val_2383_);
v___x_45917__boxed_2401_ = lean_unbox(v___x_2387_);
v_res_2402_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_fst_2382_, v_val_45914__boxed_2400_, v_a_2384_, v_snd_2385_, v___x_2386_, v___x_45917__boxed_2401_, v_prom_2388_, v___x_2389_, v___f_2390_, v___f_2391_, v___f_2392_, v_pos_2393_, v_fst_2394_, v_cmdState_2395_, v_opts_2396_, v_old_x3f_2397_, v_parseCancelTk_2398_);
lean_dec_ref(v_opts_2396_);
lean_dec(v_prom_2388_);
lean_dec_ref(v_a_2384_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2405_, lean_object* v_parserState_2406_, lean_object* v_cmdState_2407_, lean_object* v_prom_2408_, uint8_t v_sync_2409_, lean_object* v_parseCancelTk_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_toSnapshot_2414_; lean_object* v_stx_2415_; lean_object* v_parserState_2416_; lean_object* v_elabSnap_2417_; lean_object* v_val_2418_; lean_object* v_newParserState_2419_; lean_object* v___y_2453_; lean_object* v___y_2455_; lean_object* v___y_2456_; uint8_t v___y_2457_; lean_object* v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___f_2495_; lean_object* v___f_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; uint8_t v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2525_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; uint8_t v___y_2537_; lean_object* v___y_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___y_2553_; lean_object* v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; uint8_t v___y_2568_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; 
v___f_2495_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2496_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2497_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2498_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2405_) == 1)
{
lean_object* v_val_2643_; lean_object* v_nextCmdSnap_x3f_2644_; 
v_val_2643_ = lean_ctor_get(v_old_x3f_2405_, 0);
v_nextCmdSnap_x3f_2644_ = lean_ctor_get(v_val_2643_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2644_) == 0)
{
goto v___jp_2610_;
}
else
{
lean_object* v_toSnapshot_2645_; lean_object* v_stx_2646_; lean_object* v_parserState_2647_; lean_object* v_elabSnap_2648_; lean_object* v_val_2649_; lean_object* v___x_2650_; 
v_toSnapshot_2645_ = lean_ctor_get(v_val_2643_, 0);
v_stx_2646_ = lean_ctor_get(v_val_2643_, 1);
v_parserState_2647_ = lean_ctor_get(v_val_2643_, 2);
v_elabSnap_2648_ = lean_ctor_get(v_val_2643_, 3);
v_val_2649_ = lean_ctor_get(v_nextCmdSnap_x3f_2644_, 0);
lean_inc(v_val_2649_);
v___x_2650_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2649_);
if (lean_obj_tag(v___x_2650_) == 1)
{
lean_object* v_val_2651_; lean_object* v_nextCmdSnap_x3f_2652_; 
v_val_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref(v___x_2650_);
v_nextCmdSnap_x3f_2652_ = lean_ctor_get(v_val_2651_, 4);
lean_inc(v_nextCmdSnap_x3f_2652_);
lean_dec(v_val_2651_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2652_) == 0)
{
goto v___jp_2610_;
}
else
{
lean_object* v_val_2653_; lean_object* v___x_2654_; 
v_val_2653_ = lean_ctor_get(v_nextCmdSnap_x3f_2652_, 0);
lean_inc(v_val_2653_);
lean_dec_ref(v_nextCmdSnap_x3f_2652_);
v___x_2654_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2653_);
if (lean_obj_tag(v___x_2654_) == 1)
{
lean_object* v_val_2655_; lean_object* v_parserState_2656_; lean_object* v_pos_2657_; uint8_t v___x_2658_; 
v_val_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_val_2655_);
lean_dec_ref(v___x_2654_);
v_parserState_2656_ = lean_ctor_get(v_val_2655_, 2);
lean_inc_ref(v_parserState_2656_);
lean_dec(v_val_2655_);
v_pos_2657_ = lean_ctor_get(v_parserState_2656_, 0);
lean_inc(v_pos_2657_);
lean_dec_ref(v_parserState_2656_);
v___x_2658_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2657_, v_a_2411_);
lean_dec(v_pos_2657_);
if (v___x_2658_ == 0)
{
goto v___jp_2610_;
}
else
{
lean_inc(v_val_2649_);
lean_inc_ref(v_elabSnap_2648_);
lean_inc_ref_n(v_parserState_2647_, 2);
lean_inc(v_stx_2646_);
lean_inc_ref(v_toSnapshot_2645_);
lean_dec_ref(v_old_x3f_2405_);
lean_dec_ref(v_parseCancelTk_2410_);
lean_dec_ref(v_cmdState_2407_);
lean_dec_ref(v_parserState_2406_);
v_toSnapshot_2414_ = v_toSnapshot_2645_;
v_stx_2415_ = v_stx_2646_;
v_parserState_2416_ = v_parserState_2647_;
v_elabSnap_2417_ = v_elabSnap_2648_;
v_val_2418_ = v_val_2649_;
v_newParserState_2419_ = v_parserState_2647_;
goto v___jp_2413_;
}
}
else
{
lean_dec(v___x_2654_);
goto v___jp_2610_;
}
}
}
else
{
lean_dec(v___x_2650_);
goto v___jp_2610_;
}
}
}
else
{
goto v___jp_2610_;
}
v___jp_2413_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_resultSnap_2422_; lean_object* v_task_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2446_; 
v___x_2420_ = lean_io_promise_new();
v___x_2421_ = l_IO_CancelToken_new();
v_resultSnap_2422_ = lean_ctor_get(v_elabSnap_2417_, 2);
lean_inc_ref(v_resultSnap_2422_);
v_task_2423_ = lean_ctor_get(v_resultSnap_2422_, 3);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_resultSnap_2422_);
if (v_isSharedCheck_2446_ == 0)
{
lean_object* v_unused_2447_; lean_object* v_unused_2448_; lean_object* v_unused_2449_; 
v_unused_2447_ = lean_ctor_get(v_resultSnap_2422_, 2);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_resultSnap_2422_, 1);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_resultSnap_2422_, 0);
lean_dec(v_unused_2449_);
v___x_2425_ = v_resultSnap_2422_;
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_task_2423_);
lean_dec(v_resultSnap_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v_toProcessingContext_2432_; lean_object* v_pos_2433_; lean_object* v_endPos_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2427_ = lean_box(v_sync_2409_);
lean_inc_ref(v_a_2411_);
lean_inc_ref(v___x_2421_);
lean_inc(v___x_2420_);
lean_inc_ref(v_newParserState_2419_);
v___f_2428_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2428_, 0, v_val_2418_);
lean_closure_set(v___f_2428_, 1, v_newParserState_2419_);
lean_closure_set(v___f_2428_, 2, v___x_2420_);
lean_closure_set(v___f_2428_, 3, v___x_2427_);
lean_closure_set(v___f_2428_, 4, v___x_2421_);
lean_closure_set(v___f_2428_, 5, v_a_2411_);
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = 1;
v___x_2431_ = l_BaseIO_chainTask___redArg(v_task_2423_, v___f_2428_, v___x_2429_, v___x_2430_);
v_toProcessingContext_2432_ = lean_ctor_get(v_a_2411_, 0);
v_pos_2433_ = lean_ctor_get(v_newParserState_2419_, 0);
lean_inc(v_pos_2433_);
lean_dec_ref(v_newParserState_2419_);
v_endPos_2434_ = lean_ctor_get(v_toProcessingContext_2432_, 3);
v___x_2435_ = lean_box(0);
lean_inc(v_endPos_2434_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_pos_2433_);
lean_ctor_set(v___x_2436_, 1, v_endPos_2434_);
v___x_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2421_);
v___x_2439_ = l_IO_Promise_result_x21___redArg(v___x_2420_);
lean_dec(v___x_2420_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 3, v___x_2439_);
lean_ctor_set(v___x_2425_, 2, v___x_2438_);
lean_ctor_set(v___x_2425_, 1, v___x_2437_);
lean_ctor_set(v___x_2425_, 0, v___x_2435_);
v___x_2441_ = v___x_2425_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2445_, 2, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2445_, 3, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2443_, 0, v_toSnapshot_2414_);
lean_ctor_set(v___x_2443_, 1, v_stx_2415_);
lean_ctor_set(v___x_2443_, 2, v_parserState_2416_);
lean_ctor_set(v___x_2443_, 3, v_elabSnap_2417_);
lean_ctor_set(v___x_2443_, 4, v___x_2442_);
v___x_2444_ = lean_io_promise_resolve(v___x_2443_, v_prom_2408_);
lean_dec(v_prom_2408_);
return v___x_2444_;
}
}
}
v___jp_2450_:
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_box(0);
return v___x_2451_;
}
v___jp_2452_:
{
goto v___jp_2450_;
}
v___jp_2454_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2458_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2459_ = l_Lean_Name_str___override(v___y_2455_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2461_ = l_Lean_Name_str___override(v___x_2459_, v___x_2460_);
v___x_2462_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2463_ = l_Lean_Name_str___override(v___x_2461_, v___x_2462_);
v___x_2464_ = l_Lean_Name_str___override(v___x_2463_, v___x_2460_);
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = l_Lean_Name_num___override(v___x_2464_, v___x_2465_);
v___x_2467_ = l_Lean_Name_str___override(v___x_2466_, v___x_2460_);
v___x_2468_ = l_Lean_Name_str___override(v___x_2467_, v___x_2462_);
v___x_2469_ = l_Lean_Name_str___override(v___x_2468_, v___x_2460_);
v___x_2470_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2471_ = l_Lean_Name_str___override(v___x_2469_, v___x_2470_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2473_ = l_Lean_Name_str___override(v___x_2471_, v___x_2472_);
v___x_2474_ = l_Lean_Name_toString(v___x_2473_, v___y_2457_);
v___x_2475_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2478_ = 0;
v___x_2479_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2479_, 0, v___x_2474_);
lean_ctor_set(v___x_2479_, 1, v___x_2475_);
lean_ctor_set(v___x_2479_, 2, v___x_2476_);
lean_ctor_set(v___x_2479_, 3, v___x_2477_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*4, v___x_2478_);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2479_, 3);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2479_);
lean_ctor_set(v___x_2482_, 1, v_cmdState_2407_);
v___x_2483_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2476_, v___x_2482_);
v___x_2484_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2476_, v___x_2479_);
v___x_2485_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2479_);
lean_ctor_set(v___x_2486_, 1, v___x_2481_);
lean_ctor_set(v___x_2486_, 2, v___x_2483_);
lean_ctor_set(v___x_2486_, 3, v___x_2484_);
lean_ctor_set(v___x_2486_, 4, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2479_);
lean_ctor_set(v___x_2487_, 1, v___x_2480_);
lean_ctor_set(v___x_2487_, 2, v___y_2456_);
lean_ctor_set(v___x_2487_, 3, v___x_2486_);
lean_ctor_set(v___x_2487_, 4, v___x_2476_);
v___x_2488_ = lean_io_promise_resolve(v___x_2487_, v_prom_2408_);
lean_dec(v_prom_2408_);
v___x_2489_ = lean_box(0);
return v___x_2489_;
}
v___jp_2490_:
{
v___y_2455_ = v___y_2491_;
v___y_2456_ = v___y_2492_;
v___y_2457_ = v___y_2493_;
goto v___jp_2454_;
}
v___jp_2499_:
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2516_);
v___x_2518_ = l_Lean_Parser_isTerminalCommand(v___y_2514_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_io_promise_new();
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
v___x_2521_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2517_, v___y_2510_, v___y_2511_, v___y_2503_, v_a_2411_, v___y_2505_, v___y_2501_, v___y_2515_, v___y_2509_, v___y_2507_, v___y_2513_, v___y_2500_, v___y_2502_, v_prom_2408_, v___x_2498_, v___f_2497_, v___f_2496_, v___f_2495_, v___y_2508_, v___y_2512_, v_cmdState_2407_, v___y_2506_, v___y_2504_, v_old_x3f_2405_, v_parseCancelTk_2410_, v___x_2520_);
lean_dec_ref(v___y_2506_);
lean_dec(v_prom_2408_);
lean_dec(v___y_2513_);
lean_dec(v___y_2510_);
v___y_2453_ = v___x_2521_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2517_, v___y_2510_, v___y_2511_, v___y_2503_, v_a_2411_, v___y_2505_, v___y_2501_, v___y_2515_, v___y_2509_, v___y_2507_, v___y_2513_, v___y_2500_, v___y_2502_, v_prom_2408_, v___x_2498_, v___f_2497_, v___f_2496_, v___f_2495_, v___y_2508_, v___y_2512_, v_cmdState_2407_, v___y_2506_, v___y_2504_, v_old_x3f_2405_, v_parseCancelTk_2410_, v___x_2522_);
lean_dec_ref(v___y_2506_);
lean_dec(v_prom_2408_);
lean_dec(v___y_2513_);
lean_dec(v___y_2510_);
v___y_2453_ = v___x_2523_;
goto v___jp_2452_;
}
}
v___jp_2524_:
{
lean_object* v___x_2541_; 
lean_inc(v___y_2538_);
v___x_2541_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2538_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_box(0);
v___y_2500_ = v___y_2525_;
v___y_2501_ = v___y_2526_;
v___y_2502_ = v_snd_2540_;
v___y_2503_ = v___y_2527_;
v___y_2504_ = v___y_2528_;
v___y_2505_ = v___y_2529_;
v___y_2506_ = v___y_2530_;
v___y_2507_ = v___y_2531_;
v___y_2508_ = v___y_2532_;
v___y_2509_ = v_fst_2539_;
v___y_2510_ = v___y_2533_;
v___y_2511_ = v___y_2534_;
v___y_2512_ = v___y_2535_;
v___y_2513_ = v___y_2536_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2537_;
v___y_2516_ = v___x_2542_;
goto v___jp_2499_;
}
else
{
lean_object* v_val_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_val_2543_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v___x_2541_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_val_2543_);
lean_dec(v___x_2541_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc(v_val_2543_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_val_2543_);
lean_ctor_set(v___x_2547_, 1, v_val_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
v___y_2500_ = v___y_2525_;
v___y_2501_ = v___y_2526_;
v___y_2502_ = v_snd_2540_;
v___y_2503_ = v___y_2527_;
v___y_2504_ = v___y_2528_;
v___y_2505_ = v___y_2529_;
v___y_2506_ = v___y_2530_;
v___y_2507_ = v___y_2531_;
v___y_2508_ = v___y_2532_;
v___y_2509_ = v_fst_2539_;
v___y_2510_ = v___y_2533_;
v___y_2511_ = v___y_2534_;
v___y_2512_ = v___y_2535_;
v___y_2513_ = v___y_2536_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2537_;
v___y_2516_ = v___x_2549_;
goto v___jp_2499_;
}
}
}
}
v___jp_2552_:
{
if (v___y_2568_ == 0)
{
lean_inc(v___y_2567_);
v___y_2525_ = v___y_2553_;
v___y_2526_ = v___y_2554_;
v___y_2527_ = v___y_2555_;
v___y_2528_ = v___y_2556_;
v___y_2529_ = v___y_2557_;
v___y_2530_ = v___y_2558_;
v___y_2531_ = v___y_2559_;
v___y_2532_ = v___y_2560_;
v___y_2533_ = v___y_2561_;
v___y_2534_ = v___y_2562_;
v___y_2535_ = v___y_2563_;
v___y_2536_ = v___y_2564_;
v___y_2537_ = v___y_2565_;
v___y_2538_ = v___y_2567_;
v_fst_2539_ = v___y_2567_;
v_snd_2540_ = v___y_2566_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v___y_2566_);
v___x_2569_ = lean_box(0);
v___x_2570_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2525_ = v___y_2553_;
v___y_2526_ = v___y_2554_;
v___y_2527_ = v___y_2555_;
v___y_2528_ = v___y_2556_;
v___y_2529_ = v___y_2557_;
v___y_2530_ = v___y_2558_;
v___y_2531_ = v___y_2559_;
v___y_2532_ = v___y_2560_;
v___y_2533_ = v___y_2561_;
v___y_2534_ = v___y_2562_;
v___y_2535_ = v___y_2563_;
v___y_2536_ = v___y_2564_;
v___y_2537_ = v___y_2565_;
v___y_2538_ = v___y_2567_;
v_fst_2539_ = v___x_2569_;
v_snd_2540_ = v___x_2570_;
goto v___jp_2524_;
}
}
v___jp_2571_:
{
uint8_t v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = l_IO_CancelToken_isSet(v_parseCancelTk_2410_);
v___x_2583_ = 1;
if (v___x_2582_ == 0)
{
lean_dec(v___y_2578_);
if (v_sync_2409_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2584_ = lean_io_promise_new();
v___x_2585_ = lean_io_promise_new();
v___x_2586_ = lean_io_promise_new();
v___x_2587_ = lean_io_promise_new();
v___x_2588_ = l_Lean_internal_cmdlineSnapshots;
v___x_2589_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2581_, v___x_2588_);
lean_dec_ref(v___y_2581_);
if (v___x_2589_ == 0)
{
v___y_2553_ = v___x_2586_;
v___y_2554_ = v___y_2573_;
v___y_2555_ = v___x_2582_;
v___y_2556_ = v___x_2588_;
v___y_2557_ = v___y_2576_;
v___y_2558_ = v___y_2577_;
v___y_2559_ = v___x_2584_;
v___y_2560_ = v___y_2572_;
v___y_2561_ = v___x_2587_;
v___y_2562_ = v___y_2575_;
v___y_2563_ = v___y_2574_;
v___y_2564_ = v___x_2585_;
v___y_2565_ = v___x_2583_;
v___y_2566_ = v___y_2580_;
v___y_2567_ = v___y_2579_;
v___y_2568_ = v___x_2589_;
goto v___jp_2552_;
}
else
{
uint8_t v___x_2590_; 
lean_inc(v___y_2579_);
v___x_2590_ = l_Lean_Parser_isTerminalCommand(v___y_2579_);
if (v___x_2590_ == 0)
{
v___y_2553_ = v___x_2586_;
v___y_2554_ = v___y_2573_;
v___y_2555_ = v___x_2582_;
v___y_2556_ = v___x_2588_;
v___y_2557_ = v___y_2576_;
v___y_2558_ = v___y_2577_;
v___y_2559_ = v___x_2584_;
v___y_2560_ = v___y_2572_;
v___y_2561_ = v___x_2587_;
v___y_2562_ = v___y_2575_;
v___y_2563_ = v___y_2574_;
v___y_2564_ = v___x_2585_;
v___y_2565_ = v___x_2583_;
v___y_2566_ = v___y_2580_;
v___y_2567_ = v___y_2579_;
v___y_2568_ = v___x_2589_;
goto v___jp_2552_;
}
else
{
lean_inc(v___y_2579_);
v___y_2525_ = v___x_2586_;
v___y_2526_ = v___y_2573_;
v___y_2527_ = v___x_2582_;
v___y_2528_ = v___x_2588_;
v___y_2529_ = v___y_2576_;
v___y_2530_ = v___y_2577_;
v___y_2531_ = v___x_2584_;
v___y_2532_ = v___y_2572_;
v___y_2533_ = v___x_2587_;
v___y_2534_ = v___y_2575_;
v___y_2535_ = v___y_2574_;
v___y_2536_ = v___x_2585_;
v___y_2537_ = v___x_2583_;
v___y_2538_ = v___y_2579_;
v_fst_2539_ = v___y_2579_;
v_snd_2540_ = v___y_2580_;
goto v___jp_2524_;
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___f_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
v___x_2591_ = lean_box(v___x_2582_);
v___x_2592_ = lean_box(v___x_2583_);
lean_inc_ref(v_a_2411_);
v___f_2593_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 18, 17);
lean_closure_set(v___f_2593_, 0, v___y_2575_);
lean_closure_set(v___f_2593_, 1, v___x_2591_);
lean_closure_set(v___f_2593_, 2, v_a_2411_);
lean_closure_set(v___f_2593_, 3, v___y_2576_);
lean_closure_set(v___f_2593_, 4, v___y_2573_);
lean_closure_set(v___f_2593_, 5, v___x_2592_);
lean_closure_set(v___f_2593_, 6, v_prom_2408_);
lean_closure_set(v___f_2593_, 7, v___x_2498_);
lean_closure_set(v___f_2593_, 8, v___f_2497_);
lean_closure_set(v___f_2593_, 9, v___f_2496_);
lean_closure_set(v___f_2593_, 10, v___f_2495_);
lean_closure_set(v___f_2593_, 11, v___y_2572_);
lean_closure_set(v___f_2593_, 12, v___y_2574_);
lean_closure_set(v___f_2593_, 13, v_cmdState_2407_);
lean_closure_set(v___f_2593_, 14, v___y_2577_);
lean_closure_set(v___f_2593_, 15, v_old_x3f_2405_);
lean_closure_set(v___f_2593_, 16, v_parseCancelTk_2410_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_io_as_task(v___f_2593_, v___x_2594_);
lean_dec_ref(v___x_2595_);
goto v___jp_2450_;
}
}
else
{
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v_parseCancelTk_2410_);
if (lean_obj_tag(v_old_x3f_2405_) == 1)
{
lean_object* v_val_2596_; lean_object* v___x_2597_; lean_object* v_children_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_val_2596_ = lean_ctor_get(v_old_x3f_2405_, 0);
lean_inc(v_val_2596_);
lean_dec_ref(v_old_x3f_2405_);
v___x_2597_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_val_2596_);
v_children_2598_ = lean_ctor_get(v___x_2597_, 1);
lean_inc_ref(v_children_2598_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_array_get_size(v_children_2598_);
v___x_2601_ = lean_nat_dec_lt(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_dec_ref(v_children_2598_);
v___y_2455_ = v___y_2578_;
v___y_2456_ = v___y_2580_;
v___y_2457_ = v___x_2583_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = lean_nat_dec_le(v___x_2600_, v___x_2600_);
if (v___x_2603_ == 0)
{
if (v___x_2601_ == 0)
{
lean_dec_ref(v_children_2598_);
v___y_2455_ = v___y_2578_;
v___y_2456_ = v___y_2580_;
v___y_2457_ = v___x_2583_;
goto v___jp_2454_;
}
else
{
size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = ((size_t)0ULL);
v___x_2605_ = lean_usize_of_nat(v___x_2600_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2598_, v___x_2604_, v___x_2605_, v___x_2602_);
lean_dec_ref(v_children_2598_);
v___y_2491_ = v___y_2578_;
v___y_2492_ = v___y_2580_;
v___y_2493_ = v___x_2583_;
v___y_2494_ = v___x_2606_;
goto v___jp_2490_;
}
}
else
{
size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = lean_usize_of_nat(v___x_2600_);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2598_, v___x_2607_, v___x_2608_, v___x_2602_);
lean_dec_ref(v_children_2598_);
v___y_2491_ = v___y_2578_;
v___y_2492_ = v___y_2580_;
v___y_2493_ = v___x_2583_;
v___y_2494_ = v___x_2609_;
goto v___jp_2490_;
}
}
}
else
{
lean_dec(v_old_x3f_2405_);
v___y_2455_ = v___y_2578_;
v___y_2456_ = v___y_2580_;
v___y_2457_ = v___x_2583_;
goto v___jp_2454_;
}
}
}
v___jp_2610_:
{
lean_object* v_env_2611_; lean_object* v_scopes_2612_; lean_object* v___x_2613_; lean_object* v_opts_2614_; lean_object* v_currNamespace_2615_; lean_object* v_openDecls_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_snd_2622_; 
v_env_2611_ = lean_ctor_get(v_cmdState_2407_, 0);
v_scopes_2612_ = lean_ctor_get(v_cmdState_2407_, 2);
v___x_2613_ = l_List_head_x21___redArg(v___x_2498_, v_scopes_2612_);
v_opts_2614_ = lean_ctor_get(v___x_2613_, 1);
lean_inc_ref_n(v_opts_2614_, 2);
v_currNamespace_2615_ = lean_ctor_get(v___x_2613_, 2);
lean_inc(v_currNamespace_2615_);
v_openDecls_2616_ = lean_ctor_get(v___x_2613_, 3);
lean_inc(v_openDecls_2616_);
lean_dec(v___x_2613_);
lean_inc_ref(v_env_2611_);
v___x_2617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2617_, 0, v_env_2611_);
lean_ctor_set(v___x_2617_, 1, v_opts_2614_);
lean_ctor_set(v___x_2617_, 2, v_currNamespace_2615_);
lean_ctor_set(v___x_2617_, 3, v_openDecls_2616_);
lean_inc_ref(v_parserState_2406_);
lean_inc_ref(v_a_2411_);
v___f_2618_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2618_, 0, v_a_2411_);
lean_closure_set(v___f_2618_, 1, v___x_2617_);
lean_closure_set(v___f_2618_, 2, v_parserState_2406_);
v___x_2619_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_profileit(v___x_2619_, v_opts_2614_, v___f_2618_, v___x_2620_);
v_snd_2622_ = lean_ctor_get(v___x_2621_, 1);
lean_inc(v_snd_2622_);
if (lean_obj_tag(v_old_x3f_2405_) == 1)
{
lean_object* v_val_2623_; lean_object* v_fst_2624_; lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v_pos_2627_; lean_object* v_toSnapshot_2628_; lean_object* v_stx_2629_; lean_object* v_parserState_2630_; lean_object* v_elabSnap_2631_; lean_object* v_nextCmdSnap_x3f_2632_; uint8_t v___x_2633_; 
v_val_2623_ = lean_ctor_get(v_old_x3f_2405_, 0);
v_fst_2624_ = lean_ctor_get(v___x_2621_, 0);
lean_inc_n(v_fst_2624_, 2);
lean_dec(v___x_2621_);
v_fst_2625_ = lean_ctor_get(v_snd_2622_, 0);
lean_inc(v_fst_2625_);
v_snd_2626_ = lean_ctor_get(v_snd_2622_, 1);
lean_inc(v_snd_2626_);
lean_dec(v_snd_2622_);
v_pos_2627_ = lean_ctor_get(v_parserState_2406_, 0);
lean_inc(v_pos_2627_);
lean_dec_ref(v_parserState_2406_);
v_toSnapshot_2628_ = lean_ctor_get(v_val_2623_, 0);
v_stx_2629_ = lean_ctor_get(v_val_2623_, 1);
v_parserState_2630_ = lean_ctor_get(v_val_2623_, 2);
v_elabSnap_2631_ = lean_ctor_get(v_val_2623_, 3);
v_nextCmdSnap_x3f_2632_ = lean_ctor_get(v_val_2623_, 4);
lean_inc(v_stx_2629_);
v___x_2633_ = l_Lean_Syntax_eqWithInfo(v_fst_2624_, v_stx_2629_);
if (v___x_2633_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2632_) == 0)
{
lean_inc_ref(v_opts_2614_);
lean_inc(v_fst_2625_);
lean_inc(v_fst_2624_);
v___y_2572_ = v_pos_2627_;
v___y_2573_ = v___x_2620_;
v___y_2574_ = v_fst_2624_;
v___y_2575_ = v_fst_2625_;
v___y_2576_ = v_snd_2626_;
v___y_2577_ = v_opts_2614_;
v___y_2578_ = v___x_2620_;
v___y_2579_ = v_fst_2624_;
v___y_2580_ = v_fst_2625_;
v___y_2581_ = v_opts_2614_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_val_2634_ = lean_ctor_get(v_nextCmdSnap_x3f_2632_, 0);
v___x_2635_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2634_);
v___x_2636_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2635_, v_val_2634_);
lean_inc_ref(v_opts_2614_);
lean_inc(v_fst_2625_);
lean_inc(v_fst_2624_);
v___y_2572_ = v_pos_2627_;
v___y_2573_ = v___x_2620_;
v___y_2574_ = v_fst_2624_;
v___y_2575_ = v_fst_2625_;
v___y_2576_ = v_snd_2626_;
v___y_2577_ = v_opts_2614_;
v___y_2578_ = v___x_2620_;
v___y_2579_ = v_fst_2624_;
v___y_2580_ = v_fst_2625_;
v___y_2581_ = v_opts_2614_;
goto v___jp_2571_;
}
}
else
{
lean_inc(v_val_2623_);
lean_dec(v_pos_2627_);
lean_dec(v_snd_2626_);
lean_dec(v_fst_2624_);
lean_dec_ref(v_old_x3f_2405_);
lean_dec_ref(v_opts_2614_);
lean_dec_ref(v_parseCancelTk_2410_);
lean_dec_ref(v_cmdState_2407_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2632_) == 1)
{
lean_object* v_val_2637_; 
lean_inc_ref(v_nextCmdSnap_x3f_2632_);
lean_inc_ref(v_elabSnap_2631_);
lean_inc_ref(v_parserState_2630_);
lean_inc(v_stx_2629_);
lean_inc_ref(v_toSnapshot_2628_);
lean_dec(v_val_2623_);
v_val_2637_ = lean_ctor_get(v_nextCmdSnap_x3f_2632_, 0);
lean_inc(v_val_2637_);
lean_dec_ref(v_nextCmdSnap_x3f_2632_);
v_toSnapshot_2414_ = v_toSnapshot_2628_;
v_stx_2415_ = v_stx_2629_;
v_parserState_2416_ = v_parserState_2630_;
v_elabSnap_2417_ = v_elabSnap_2631_;
v_val_2418_ = v_val_2637_;
v_newParserState_2419_ = v_fst_2625_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2638_; 
lean_dec(v_fst_2625_);
v___x_2638_ = lean_io_promise_resolve(v_val_2623_, v_prom_2408_);
lean_dec(v_prom_2408_);
return v___x_2638_;
}
}
}
else
{
lean_object* v_fst_2639_; lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v_pos_2642_; 
v_fst_2639_ = lean_ctor_get(v___x_2621_, 0);
lean_inc_n(v_fst_2639_, 2);
lean_dec(v___x_2621_);
v_fst_2640_ = lean_ctor_get(v_snd_2622_, 0);
lean_inc_n(v_fst_2640_, 2);
v_snd_2641_ = lean_ctor_get(v_snd_2622_, 1);
lean_inc(v_snd_2641_);
lean_dec(v_snd_2622_);
v_pos_2642_ = lean_ctor_get(v_parserState_2406_, 0);
lean_inc(v_pos_2642_);
lean_dec_ref(v_parserState_2406_);
lean_inc_ref(v_opts_2614_);
v___y_2572_ = v_pos_2642_;
v___y_2573_ = v___x_2620_;
v___y_2574_ = v_fst_2639_;
v___y_2575_ = v_fst_2640_;
v___y_2576_ = v_snd_2641_;
v___y_2577_ = v_opts_2614_;
v___y_2578_ = v___x_2620_;
v___y_2579_ = v_fst_2639_;
v___y_2580_ = v_fst_2640_;
v___y_2581_ = v_opts_2614_;
goto v___jp_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2659_, lean_object* v_newParserState_2660_, lean_object* v_val_2661_, uint8_t v_sync_2662_, lean_object* v_val_2663_, lean_object* v_a_2664_, lean_object* v_oldNext_2665_){
_start:
{
lean_object* v_cmdState_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_cmdState_2667_ = lean_ctor_get(v_oldResult_2659_, 1);
lean_inc_ref(v_cmdState_2667_);
lean_dec_ref(v_oldResult_2659_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_oldNext_2665_);
v___x_2669_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2668_, v_newParserState_2660_, v_cmdState_2667_, v_val_2661_, v_sync_2662_, v_val_2663_, v_a_2664_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2670_ = _args[0];
lean_object* v_val_2671_ = _args[1];
lean_object* v_fst_2672_ = _args[2];
lean_object* v_val_2673_ = _args[3];
lean_object* v_a_2674_ = _args[4];
lean_object* v_snd_2675_ = _args[5];
lean_object* v___x_2676_ = _args[6];
lean_object* v___x_2677_ = _args[7];
lean_object* v_fst_2678_ = _args[8];
lean_object* v_val_2679_ = _args[9];
lean_object* v_val_2680_ = _args[10];
lean_object* v_val_2681_ = _args[11];
lean_object* v_snd_2682_ = _args[12];
lean_object* v_prom_2683_ = _args[13];
lean_object* v___x_2684_ = _args[14];
lean_object* v___f_2685_ = _args[15];
lean_object* v___f_2686_ = _args[16];
lean_object* v___f_2687_ = _args[17];
lean_object* v_pos_2688_ = _args[18];
lean_object* v_fst_2689_ = _args[19];
lean_object* v_cmdState_2690_ = _args[20];
lean_object* v_opts_2691_ = _args[21];
lean_object* v___x_2692_ = _args[22];
lean_object* v_old_x3f_2693_ = _args[23];
lean_object* v_parseCancelTk_2694_ = _args[24];
lean_object* v_next_x3f_2695_ = _args[25];
lean_object* v___y_2696_ = _args[26];
_start:
{
uint8_t v_val_45699__boxed_2697_; uint8_t v___x_45702__boxed_2698_; lean_object* v_res_2699_; 
v_val_45699__boxed_2697_ = lean_unbox(v_val_2673_);
v___x_45702__boxed_2698_ = lean_unbox(v___x_2677_);
v_res_2699_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2670_, v_val_2671_, v_fst_2672_, v_val_45699__boxed_2697_, v_a_2674_, v_snd_2675_, v___x_2676_, v___x_45702__boxed_2698_, v_fst_2678_, v_val_2679_, v_val_2680_, v_val_2681_, v_snd_2682_, v_prom_2683_, v___x_2684_, v___f_2685_, v___f_2686_, v___f_2687_, v_pos_2688_, v_fst_2689_, v_cmdState_2690_, v_opts_2691_, v___x_2692_, v_old_x3f_2693_, v_parseCancelTk_2694_, v_next_x3f_2695_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_opts_2691_);
lean_dec(v_prom_2683_);
lean_dec(v_val_2680_);
lean_dec_ref(v_a_2674_);
lean_dec(v_val_2671_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2700_, lean_object* v_parserState_2701_, lean_object* v_cmdState_2702_, lean_object* v_prom_2703_, lean_object* v_sync_2704_, lean_object* v_parseCancelTk_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
uint8_t v_sync_boxed_2708_; lean_object* v_res_2709_; 
v_sync_boxed_2708_ = lean_unbox(v_sync_2704_);
v_res_2709_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2700_, v_parserState_2701_, v_cmdState_2702_, v_prom_2703_, v_sync_boxed_2708_, v_parseCancelTk_2705_, v_a_2706_);
lean_dec_ref(v_a_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2710_, size_t v_i_2711_, size_t v_stop_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2710_, v_i_2711_, v_stop_2712_, v_b_2713_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2717_, lean_object* v_i_2718_, lean_object* v_stop_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
size_t v_i_boxed_2723_; size_t v_stop_boxed_2724_; lean_object* v_res_2725_; 
v_i_boxed_2723_ = lean_unbox_usize(v_i_2718_);
lean_dec(v_i_2718_);
v_stop_boxed_2724_ = lean_unbox_usize(v_stop_2719_);
lean_dec(v_stop_2719_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2717_, v_i_boxed_2723_, v_stop_boxed_2724_, v_b_2720_, v___y_2721_);
lean_dec_ref(v___y_2721_);
lean_dec_ref(v_as_2717_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2726_, lean_object* v_opt_2727_){
_start:
{
lean_object* v_name_2728_; lean_object* v_map_2729_; lean_object* v___x_2730_; 
v_name_2728_ = lean_ctor_get(v_opt_2727_, 0);
v_map_2729_ = lean_ctor_get(v_opts_2726_, 0);
v___x_2730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2729_, v_name_2728_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2731_; 
v___x_2731_ = lean_box(0);
return v___x_2731_;
}
else
{
lean_object* v_val_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2741_; 
v_val_2732_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2734_ = v___x_2730_;
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_val_2732_);
lean_dec(v___x_2730_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
if (lean_obj_tag(v_val_2732_) == 0)
{
lean_object* v_v_2736_; lean_object* v___x_2738_; 
v_v_2736_ = lean_ctor_get(v_val_2732_, 0);
lean_inc_ref(v_v_2736_);
lean_dec_ref(v_val_2732_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v_v_2736_);
v___x_2738_ = v___x_2734_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_v_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
lean_object* v___x_2740_; 
lean_del_object(v___x_2734_);
lean_dec(v_val_2732_);
v___x_2740_ = lean_box(0);
return v___x_2740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2742_, lean_object* v_opt_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2742_, v_opt_2743_);
lean_dec_ref(v_opt_2743_);
lean_dec_ref(v_opts_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2745_, lean_object* v_x_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2745_);
v___x_2748_ = lean_box(0);
v___x_2749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2749_, 0, v_x_2746_);
lean_ctor_set(v___x_2749_, 1, v___x_2747_);
lean_ctor_set(v___x_2749_, 2, v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2756_ = l_Array_toPArray_x27___redArg(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
if (lean_obj_tag(v_a_2757_) == 0)
{
lean_object* v___x_2759_; 
v___x_2759_ = l_List_reverse___redArg(v_a_2758_);
return v___x_2759_;
}
else
{
lean_object* v_head_2760_; lean_object* v_tail_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2774_; 
v_head_2760_ = lean_ctor_get(v_a_2757_, 0);
v_tail_2761_ = lean_ctor_get(v_a_2757_, 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_a_2757_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2763_ = v_a_2757_;
v_isShared_2764_ = v_isSharedCheck_2774_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_tail_2761_);
lean_inc(v_head_2760_);
lean_dec(v_a_2757_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2774_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2765_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v_head_2760_);
v___x_2767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 1, v_a_2758_);
lean_ctor_set(v___x_2763_, 0, v___x_2769_);
v___x_2771_ = v___x_2763_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_a_2758_);
v___x_2771_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
v_a_2757_ = v_tail_2761_;
v_a_2758_ = v___x_2771_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2785_; double v___x_2786_; 
v___x_2785_ = lean_unsigned_to_nat(1000000000u);
v___x_2786_ = lean_float_of_nat(v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2794_ = l_Lean_MessageData_ofFormat(v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2795_, lean_object* v_stx_2796_, lean_object* v_origStx_2797_, lean_object* v_toProcessingContext_2798_, lean_object* v___x_2799_, lean_object* v_fileMap_2800_, lean_object* v_parserState_2801_, lean_object* v_a_2802_, lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_toProcessingContext_2807_; lean_object* v___x_2808_; 
v_toProcessingContext_2807_ = lean_ctor_get(v___y_2805_, 0);
lean_inc_ref(v_toProcessingContext_2807_);
lean_inc(v_stx_2796_);
v___x_2808_ = lean_apply_3(v_setupImports_2795_, v_stx_2796_, v_toProcessingContext_2807_, lean_box(0));
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_3021_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_3021_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_3021_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; 
lean_dec_ref(v___x_2804_);
lean_dec(v___x_2803_);
lean_dec_ref(v_parserState_2801_);
lean_dec_ref(v_fileMap_2800_);
lean_dec(v___x_2799_);
lean_dec_ref(v_toProcessingContext_2798_);
lean_dec(v_origStx_2797_);
lean_dec(v_stx_2796_);
v_a_2813_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v_a_2809_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v_a_2813_);
v___x_2815_ = v___x_2811_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_3020_; 
v_a_2817_ = lean_ctor_get(v_a_2809_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_a_2809_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2819_ = v_a_2809_;
v_isShared_2820_ = v_isSharedCheck_3020_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v_a_2809_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_3020_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v_mainModuleName_2822_; lean_object* v_package_x3f_2823_; uint8_t v_isModule_2824_; lean_object* v_imports_2825_; lean_object* v_opts_2826_; uint32_t v_trustLevel_2827_; lean_object* v_importArts_2828_; lean_object* v_plugins_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2834_; 
v___x_2821_ = lean_io_mono_nanos_now();
v_mainModuleName_2822_ = lean_ctor_get(v_a_2817_, 0);
lean_inc(v_mainModuleName_2822_);
v_package_x3f_2823_ = lean_ctor_get(v_a_2817_, 1);
lean_inc(v_package_x3f_2823_);
v_isModule_2824_ = lean_ctor_get_uint8(v_a_2817_, sizeof(void*)*6 + 4);
v_imports_2825_ = lean_ctor_get(v_a_2817_, 2);
lean_inc_ref(v_imports_2825_);
v_opts_2826_ = lean_ctor_get(v_a_2817_, 3);
lean_inc_ref(v_opts_2826_);
v_trustLevel_2827_ = lean_ctor_get_uint32(v_a_2817_, sizeof(void*)*6);
v_importArts_2828_ = lean_ctor_get(v_a_2817_, 4);
lean_inc(v_importArts_2828_);
v_plugins_2829_ = lean_ctor_get(v_a_2817_, 5);
lean_inc_ref(v_plugins_2829_);
lean_dec(v_a_2817_);
v___x_2830_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2796_);
v___x_2831_ = l_Lean_MessageLog_empty;
v___x_2832_ = 1;
lean_inc(v_stx_2796_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v_stx_2796_);
v___x_2834_ = v___x_2819_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_stx_2796_);
v___x_2834_ = v_reuseFailAlloc_3019_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_origStx_2797_);
lean_inc_ref(v___x_2834_);
lean_inc_ref(v_opts_2826_);
v___x_2836_ = l_Lean_Elab_processHeaderCore(v___x_2830_, v_imports_2825_, v_isModule_2824_, v_opts_2826_, v___x_2831_, v_toProcessingContext_2798_, v_trustLevel_2827_, v_plugins_2829_, v___x_2832_, v_mainModuleName_2822_, v_package_x3f_2823_, v_importArts_2828_, v___x_2834_, v___x_2835_);
lean_dec(v___x_2830_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_3010_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_3010_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_3010_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_3009_; 
v_fst_2841_ = lean_ctor_get(v_a_2837_, 0);
v_snd_2842_ = lean_ctor_get(v_a_2837_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_a_2837_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2844_ = v_a_2837_;
v_isShared_2845_ = v_isSharedCheck_3009_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snd_2842_);
lean_inc(v_fst_2841_);
lean_dec(v_a_2837_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_3009_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v_traceState_2864_; 
v___x_2846_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2842_);
v___x_2847_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2842_);
v___x_2848_ = l_Lean_MessageLog_hasErrors(v_snd_2842_);
if (v___x_2848_ == 0)
{
double v___x_2957_; double v___x_2958_; double v___x_2959_; double v___x_2960_; double v___x_2961_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_del_object(v___x_2811_);
lean_dec_ref(v___x_2804_);
v___x_2957_ = lean_float_of_nat(v___x_2821_);
v___x_2958_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2959_ = lean_float_div(v___x_2957_, v___x_2958_);
v___x_2960_ = lean_float_of_nat(v___x_2846_);
v___x_2961_ = lean_float_div(v___x_2960_, v___x_2958_);
v___x_2978_ = l_Lean_trace_profiler_output;
v___x_2979_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2826_, v___x_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = l_Lean_trace_profiler_serve;
v___x_2981_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2826_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2864_ = v___x_2982_;
goto v___jp_2863_;
}
else
{
goto v___jp_2962_;
}
}
else
{
lean_dec_ref(v___x_2979_);
goto v___jp_2962_;
}
v___jp_2962_:
{
uint64_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2963_ = 0ULL;
v___x_2964_ = lean_box(0);
v___x_2965_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2966_ = lean_box(0);
v___x_2967_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2968_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2968_, 0, v___x_2965_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
lean_ctor_set(v___x_2968_, 2, v___x_2967_);
lean_ctor_set_float(v___x_2968_, sizeof(void*)*3, v___x_2959_);
lean_ctor_set_float(v___x_2968_, sizeof(void*)*3 + 8, v___x_2961_);
lean_ctor_set_uint8(v___x_2968_, sizeof(void*)*3 + 16, v___x_2832_);
v___x_2969_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2970_ = lean_mk_empty_array_with_capacity(v___x_2799_);
v___x_2971_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2968_);
lean_ctor_set(v___x_2971_, 1, v___x_2969_);
lean_ctor_set(v___x_2971_, 2, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2964_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_unsigned_to_nat(1u);
v___x_2974_ = lean_mk_empty_array_with_capacity(v___x_2973_);
v___x_2975_ = lean_array_push(v___x_2974_, v___x_2972_);
v___x_2976_ = l_Array_toPArray_x27___redArg(v___x_2975_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set_uint64(v___x_2977_, sizeof(void*)*1, v___x_2963_);
v_traceState_2864_ = v___x_2977_;
goto v___jp_2863_;
}
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint64_t v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; size_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
lean_dec(v___x_2846_);
lean_del_object(v___x_2844_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_opts_2826_);
lean_dec(v___x_2821_);
lean_dec(v___x_2803_);
lean_dec_ref(v_parserState_2801_);
lean_dec_ref(v_fileMap_2800_);
lean_dec(v_stx_2796_);
v___x_2983_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2984_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2985_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2799_, 2);
v___x_2986_ = l_Lean_Name_num___override(v___x_2985_, v___x_2799_);
v___x_2987_ = l_Lean_Name_str___override(v___x_2986_, v___x_2983_);
v___x_2988_ = l_Lean_Name_str___override(v___x_2987_, v___x_2984_);
v___x_2989_ = l_Lean_Name_str___override(v___x_2988_, v___x_2983_);
v___x_2990_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2991_ = l_Lean_Name_str___override(v___x_2989_, v___x_2990_);
v___x_2992_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2993_ = l_Lean_Name_str___override(v___x_2991_, v___x_2992_);
v___x_2994_ = l_Lean_Name_toString(v___x_2993_, v___x_2832_);
v___x_2995_ = lean_box(0);
v___x_2996_ = 0ULL;
v___x_2997_ = lean_unsigned_to_nat(32u);
v___x_2998_ = lean_mk_empty_array_with_capacity(v___x_2997_);
v___x_2999_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3000_ = ((size_t)5ULL);
v___x_3001_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_2998_);
lean_ctor_set(v___x_3001_, 2, v___x_2799_);
lean_ctor_set(v___x_3001_, 3, v___x_2799_);
lean_ctor_set_usize(v___x_3001_, 4, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set_uint64(v___x_3002_, sizeof(void*)*1, v___x_2996_);
v___x_3003_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3003_, 0, v___x_2994_);
lean_ctor_set(v___x_3003_, 1, v___x_2847_);
lean_ctor_set(v___x_3003_, 2, v___x_2995_);
lean_ctor_set(v___x_3003_, 3, v___x_3002_);
lean_ctor_set_uint8(v___x_3003_, sizeof(void*)*4, v___x_2848_);
v___x_3004_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2804_);
v___x_3005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
lean_ctor_set(v___x_3005_, 2, v___x_2995_);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_3005_);
v___x_3007_ = v___x_2811_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
v___jp_2849_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___y_2855_);
v___x_2857_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2857_, 0, v___y_2854_);
lean_ctor_set(v___x_2857_, 1, v___x_2847_);
lean_ctor_set(v___x_2857_, 2, v___x_2856_);
lean_ctor_set(v___x_2857_, 3, v___y_2852_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*4, v___x_2848_);
v___x_2858_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2853_, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2859_, 0, v___y_2850_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
lean_ctor_set(v___x_2859_, 2, v___y_2851_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2859_);
v___x_2861_ = v___x_2839_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
v___jp_2863_:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Language_Lean_reparseOptions(v_opts_2826_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v_env_2872_; lean_object* v_messages_2873_; lean_object* v_scopes_2874_; lean_object* v_usedQuotCtxts_2875_; lean_object* v_nextMacroScope_2876_; lean_object* v_maxRecDepth_2877_; lean_object* v_ngen_2878_; lean_object* v_auxDeclNGen_2879_; lean_object* v_snapshotTasks_2880_; lean_object* v_newDecls_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2946_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2799_, 4);
v___x_2868_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2799_);
lean_ctor_set(v___x_2868_, 1, v___x_2799_);
lean_ctor_set(v___x_2868_, 2, v___x_2799_);
lean_ctor_set(v___x_2868_, 3, v___x_2799_);
lean_ctor_set(v___x_2868_, 4, v___x_2867_);
lean_ctor_set(v___x_2868_, 5, v___x_2867_);
lean_ctor_set(v___x_2868_, 6, v___x_2867_);
lean_ctor_set(v___x_2868_, 7, v___x_2867_);
lean_ctor_set(v___x_2868_, 8, v___x_2867_);
lean_ctor_set(v___x_2868_, 9, v___x_2867_);
v___x_2869_ = lean_io_promise_new();
v___x_2870_ = l_IO_CancelToken_new();
lean_inc(v_fst_2841_);
v___x_2871_ = l_Lean_Elab_Command_mkState(v_fst_2841_, v_snd_2842_, v_a_2866_);
v_env_2872_ = lean_ctor_get(v___x_2871_, 0);
v_messages_2873_ = lean_ctor_get(v___x_2871_, 1);
v_scopes_2874_ = lean_ctor_get(v___x_2871_, 2);
v_usedQuotCtxts_2875_ = lean_ctor_get(v___x_2871_, 3);
v_nextMacroScope_2876_ = lean_ctor_get(v___x_2871_, 4);
v_maxRecDepth_2877_ = lean_ctor_get(v___x_2871_, 5);
v_ngen_2878_ = lean_ctor_get(v___x_2871_, 6);
v_auxDeclNGen_2879_ = lean_ctor_get(v___x_2871_, 7);
v_snapshotTasks_2880_ = lean_ctor_get(v___x_2871_, 10);
v_newDecls_2881_ = lean_ctor_get(v___x_2871_, 11);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; lean_object* v_unused_2948_; 
v_unused_2947_ = lean_ctor_get(v___x_2871_, 9);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v___x_2871_, 8);
lean_dec(v_unused_2948_);
v___x_2883_ = v___x_2871_;
v_isShared_2884_ = v_isSharedCheck_2946_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_newDecls_2881_);
lean_inc(v_snapshotTasks_2880_);
lean_inc(v_auxDeclNGen_2879_);
lean_inc(v_ngen_2878_);
lean_inc(v_maxRecDepth_2877_);
lean_inc(v_nextMacroScope_2876_);
lean_inc(v_usedQuotCtxts_2875_);
lean_inc(v_scopes_2874_);
lean_inc(v_messages_2873_);
lean_inc(v_env_2872_);
lean_dec(v___x_2871_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2946_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2885_ = lean_box(0);
v___x_2886_ = l_Lean_Options_empty;
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2891_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2891_, 0, v_fst_2841_);
lean_ctor_set(v___x_2891_, 1, v___x_2885_);
lean_ctor_set(v___x_2891_, 2, v_fileMap_2800_);
lean_ctor_set(v___x_2891_, 3, v___x_2868_);
lean_ctor_set(v___x_2891_, 4, v___x_2886_);
lean_ctor_set(v___x_2891_, 5, v___x_2887_);
lean_ctor_set(v___x_2891_, 6, v___x_2888_);
lean_ctor_set(v___x_2891_, 7, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2796_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v_stx_2796_);
lean_ctor_set(v___x_2844_, 0, v___x_2893_);
v___x_2895_ = v___x_2844_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_stx_2796_);
v___x_2895_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
v___x_2897_ = lean_unsigned_to_nat(2u);
v___x_2898_ = l_Lean_Syntax_getArg(v_stx_2796_, v___x_2897_);
lean_dec(v_stx_2796_);
v___x_2899_ = l_Lean_Syntax_getArgs(v___x_2898_);
lean_dec(v___x_2898_);
v___x_2900_ = lean_array_to_list(v___x_2899_);
v___x_2901_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2900_, v___x_2888_);
v___x_2902_ = l_List_toPArray_x27___redArg(v___x_2901_);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2896_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2892_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_2906_ = lean_array_push(v___x_2905_, v___x_2904_);
v___x_2907_ = l_Array_toPArray_x27___redArg(v___x_2906_);
lean_dec_ref(v___x_2906_);
lean_inc_ref(v___x_2907_);
v___x_2908_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2908_, 0, v___x_2867_);
lean_ctor_set(v___x_2908_, 1, v___x_2867_);
lean_ctor_set(v___x_2908_, 2, v___x_2907_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3, v___x_2832_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 9, v_traceState_2864_);
lean_ctor_set(v___x_2883_, 8, v___x_2908_);
v___x_2910_ = v___x_2883_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_env_2872_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_messages_2873_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_scopes_2874_);
lean_ctor_set(v_reuseFailAlloc_2944_, 3, v_usedQuotCtxts_2875_);
lean_ctor_set(v_reuseFailAlloc_2944_, 4, v_nextMacroScope_2876_);
lean_ctor_set(v_reuseFailAlloc_2944_, 5, v_maxRecDepth_2877_);
lean_ctor_set(v_reuseFailAlloc_2944_, 6, v_ngen_2878_);
lean_ctor_set(v_reuseFailAlloc_2944_, 7, v_auxDeclNGen_2879_);
lean_ctor_set(v_reuseFailAlloc_2944_, 8, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2944_, 9, v_traceState_2864_);
lean_ctor_set(v_reuseFailAlloc_2944_, 10, v_snapshotTasks_2880_);
lean_ctor_set(v_reuseFailAlloc_2944_, 11, v_newDecls_2881_);
v___x_2910_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; lean_object* v_size_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; uint64_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
lean_inc_ref(v___x_2870_);
lean_inc(v___x_2869_);
lean_inc_ref(v___x_2910_);
v___x_2911_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2885_, v_parserState_2801_, v___x_2910_, v___x_2869_, v___x_2832_, v___x_2870_, v_a_2802_);
v___x_2912_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2913_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2914_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2799_, 3);
v___x_2915_ = l_Lean_Name_num___override(v___x_2914_, v___x_2799_);
v___x_2916_ = lean_unsigned_to_nat(32u);
v___x_2917_ = lean_mk_empty_array_with_capacity(v___x_2916_);
v___x_2918_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2919_ = ((size_t)5ULL);
v___x_2920_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2917_);
lean_ctor_set(v___x_2920_, 2, v___x_2799_);
lean_ctor_set(v___x_2920_, 3, v___x_2799_);
lean_ctor_set_usize(v___x_2920_, 4, v___x_2919_);
v_size_2921_ = lean_ctor_get(v___x_2907_, 2);
lean_inc(v_size_2921_);
v___x_2922_ = l_Lean_Name_str___override(v___x_2915_, v___x_2912_);
v___x_2923_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2803_);
v___x_2924_ = l_Lean_Name_str___override(v___x_2922_, v___x_2913_);
v___x_2925_ = l_Lean_Name_str___override(v___x_2924_, v___x_2912_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2927_ = l_Lean_Name_str___override(v___x_2925_, v___x_2926_);
v___x_2928_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2929_ = l_Lean_Name_str___override(v___x_2927_, v___x_2928_);
v___x_2930_ = l_Lean_Name_toString(v___x_2929_, v___x_2832_);
v___x_2931_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2932_ = 0ULL;
v___x_2933_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2933_, 0, v___x_2920_);
lean_ctor_set_uint64(v___x_2933_, sizeof(void*)*1, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2870_);
v___x_2935_ = l_IO_Promise_result_x21___redArg(v___x_2869_);
lean_dec(v___x_2869_);
v___x_2936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2803_);
lean_ctor_set(v___x_2936_, 1, v___x_2923_);
lean_ctor_set(v___x_2936_, 2, v___x_2934_);
lean_ctor_set(v___x_2936_, 3, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2910_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_inc_ref(v___x_2933_);
lean_inc_ref(v___x_2930_);
v___x_2939_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2939_, 0, v___x_2930_);
lean_ctor_set(v___x_2939_, 1, v___x_2931_);
lean_ctor_set(v___x_2939_, 2, v___x_2885_);
lean_ctor_set(v___x_2939_, 3, v___x_2933_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*4, v___x_2848_);
v___x_2940_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2941_ = lean_nat_dec_lt(v___x_2799_, v_size_2921_);
lean_dec(v_size_2921_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref(v___x_2907_);
lean_dec(v___x_2799_);
v___x_2942_ = l_outOfBounds___redArg(v___x_2940_);
v___y_2850_ = v___x_2939_;
v___y_2851_ = v___x_2938_;
v___y_2852_ = v___x_2933_;
v___y_2853_ = v___x_2834_;
v___y_2854_ = v___x_2930_;
v___y_2855_ = v___x_2942_;
goto v___jp_2849_;
}
else
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2940_, v___x_2907_, v___x_2799_);
lean_dec(v___x_2799_);
lean_dec_ref(v___x_2907_);
v___y_2850_ = v___x_2939_;
v___y_2851_ = v___x_2938_;
v___y_2852_ = v___x_2933_;
v___y_2853_ = v___x_2834_;
v___y_2854_ = v___x_2930_;
v___y_2855_ = v___x_2943_;
goto v___jp_2849_;
}
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_traceState_2864_);
lean_dec_ref(v___x_2847_);
lean_del_object(v___x_2844_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec_ref(v___x_2834_);
lean_dec(v___x_2803_);
lean_dec_ref(v_parserState_2801_);
lean_dec_ref(v_fileMap_2800_);
lean_dec(v___x_2799_);
lean_dec(v_stx_2796_);
v_a_2949_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2865_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2865_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_opts_2826_);
lean_dec(v___x_2821_);
lean_del_object(v___x_2811_);
lean_dec_ref(v___x_2804_);
lean_dec(v___x_2803_);
lean_dec_ref(v_parserState_2801_);
lean_dec_ref(v_fileMap_2800_);
lean_dec(v___x_2799_);
lean_dec(v_stx_2796_);
v_a_3011_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2836_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2836_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
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
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref(v___x_2804_);
lean_dec(v___x_2803_);
lean_dec_ref(v_parserState_2801_);
lean_dec_ref(v_fileMap_2800_);
lean_dec(v___x_2799_);
lean_dec_ref(v_toProcessingContext_2798_);
lean_dec(v_origStx_2797_);
lean_dec(v_stx_2796_);
v_a_3022_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2808_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2808_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3030_, lean_object* v_stx_3031_, lean_object* v_origStx_3032_, lean_object* v_toProcessingContext_3033_, lean_object* v___x_3034_, lean_object* v_fileMap_3035_, lean_object* v_parserState_3036_, lean_object* v_a_3037_, lean_object* v___x_3038_, lean_object* v___x_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3030_, v_stx_3031_, v_origStx_3032_, v_toProcessingContext_3033_, v___x_3034_, v_fileMap_3035_, v_parserState_3036_, v_a_3037_, v___x_3038_, v___x_3039_, v___y_3040_);
lean_dec_ref(v___y_3040_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___f_3044_; 
v___x_3043_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3044_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3044_, 0, v___x_3043_);
return v___f_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3045_, lean_object* v_stx_3046_, lean_object* v_origStx_3047_, lean_object* v_parserState_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_toProcessingContext_3051_; lean_object* v_fileMap_3052_; lean_object* v_endPos_3053_; lean_object* v___x_3054_; lean_object* v___f_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_toProcessingContext_3051_ = lean_ctor_get(v_a_3049_, 0);
v_fileMap_3052_ = lean_ctor_get(v_toProcessingContext_3051_, 2);
v_endPos_3053_ = lean_ctor_get(v_toProcessingContext_3051_, 3);
v___x_3054_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3055_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3056_ = lean_box(0);
v___x_3057_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3049_, 2);
lean_inc_ref(v_fileMap_3052_);
lean_inc_ref(v_toProcessingContext_3051_);
v___f_3058_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3058_, 0, v_setupImports_3045_);
lean_closure_set(v___f_3058_, 1, v_stx_3046_);
lean_closure_set(v___f_3058_, 2, v_origStx_3047_);
lean_closure_set(v___f_3058_, 3, v_toProcessingContext_3051_);
lean_closure_set(v___f_3058_, 4, v___x_3057_);
lean_closure_set(v___f_3058_, 5, v_fileMap_3052_);
lean_closure_set(v___f_3058_, 6, v_parserState_3048_);
lean_closure_set(v___f_3058_, 7, v_a_3049_);
lean_closure_set(v___f_3058_, 8, v___x_3056_);
lean_closure_set(v___f_3058_, 9, v___x_3054_);
lean_inc(v_endPos_3053_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v_endPos_3053_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
v___x_3061_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3061_, 0, lean_box(0));
lean_closure_set(v___x_3061_, 1, v___f_3055_);
lean_closure_set(v___x_3061_, 2, v___f_3058_);
lean_closure_set(v___x_3061_, 3, v_a_3049_);
v___x_3062_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3056_, v___x_3056_, v___x_3060_, v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3063_, lean_object* v_stx_3064_, lean_object* v_origStx_3065_, lean_object* v_parserState_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3063_, v_stx_3064_, v_origStx_3065_, v_parserState_3066_, v_a_3067_);
lean_dec_ref(v_a_3067_);
return v_res_3069_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3070_);
return v___x_3071_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = 1;
v___x_3077_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3078_ = l_Lean_Name_toString(v___x_3077_, v___x_3076_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3079_ = 0;
v___x_3080_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3081_ = lean_box(0);
v___x_3082_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3083_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3084_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3082_);
lean_ctor_set(v___x_3084_, 2, v___x_3081_);
lean_ctor_set(v___x_3084_, 3, v___x_3080_);
lean_ctor_set_uint8(v___x_3084_, sizeof(void*)*4, v___x_3079_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3085_, lean_object* v_cmdState_3086_, lean_object* v_a_3087_, lean_object* v_toSnapshot_3088_, lean_object* v_newStx_3089_, lean_object* v_oldCmd_3090_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v_diagnostics_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3119_; 
v___x_3092_ = lean_io_promise_new();
v___x_3093_ = l_IO_CancelToken_new();
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_oldCmd_3090_);
v___x_3095_ = 1;
lean_inc_ref(v___x_3093_);
lean_inc(v___x_3092_);
lean_inc_ref(v_cmdState_3086_);
v___x_3096_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3094_, v_newParserState_3085_, v_cmdState_3086_, v___x_3092_, v___x_3095_, v___x_3093_, v_a_3087_);
v_diagnostics_3097_ = lean_ctor_get(v_toSnapshot_3088_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_toSnapshot_3088_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; lean_object* v_unused_3121_; lean_object* v_unused_3122_; 
v_unused_3120_ = lean_ctor_get(v_toSnapshot_3088_, 3);
lean_dec(v_unused_3120_);
v_unused_3121_ = lean_ctor_get(v_toSnapshot_3088_, 2);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_toSnapshot_3088_, 0);
lean_dec(v_unused_3122_);
v___x_3099_ = v_toSnapshot_3088_;
v_isShared_3100_ = v_isSharedCheck_3119_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_diagnostics_3097_);
lean_dec(v_toSnapshot_3088_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3119_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3103_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3104_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3093_);
v___x_3106_ = l_IO_Promise_result_x21___redArg(v___x_3092_);
lean_dec(v___x_3092_);
v___x_3107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3101_);
lean_ctor_set(v___x_3107_, 1, v___x_3102_);
lean_ctor_set(v___x_3107_, 2, v___x_3105_);
lean_ctor_set(v___x_3107_, 3, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_cmdState_3086_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
v___x_3110_ = 0;
v___x_3111_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_newStx_3089_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 3, v___x_3104_);
lean_ctor_set(v___x_3099_, 2, v___x_3101_);
lean_ctor_set(v___x_3099_, 0, v___x_3103_);
v___x_3114_ = v___x_3099_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_diagnostics_3097_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3118_, 3, v___x_3104_);
v___x_3114_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*4, v___x_3110_);
v___x_3115_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3112_, v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3111_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
lean_ctor_set(v___x_3116_, 2, v___x_3109_);
v___x_3117_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3101_, v___x_3116_);
return v___x_3117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3123_, lean_object* v_cmdState_3124_, lean_object* v_a_3125_, lean_object* v_toSnapshot_3126_, lean_object* v_newStx_3127_, lean_object* v_oldCmd_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3123_, v_cmdState_3124_, v_a_3125_, v_toSnapshot_3126_, v_newStx_3127_, v_oldCmd_3128_);
lean_dec_ref(v_a_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3131_, lean_object* v_a_3132_, lean_object* v_newStx_3133_, lean_object* v___x_3134_, lean_object* v_oldProcessed_3135_){
_start:
{
lean_object* v_result_x3f_3137_; 
v_result_x3f_3137_ = lean_ctor_get(v_oldProcessed_3135_, 2);
if (lean_obj_tag(v_result_x3f_3137_) == 1)
{
lean_object* v_val_3138_; lean_object* v_firstCmdSnap_3139_; lean_object* v_toSnapshot_3140_; lean_object* v_cmdState_3141_; lean_object* v_stx_x3f_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; lean_object* v___x_3146_; 
v_val_3138_ = lean_ctor_get(v_result_x3f_3137_, 0);
lean_inc(v_val_3138_);
v_firstCmdSnap_3139_ = lean_ctor_get(v_val_3138_, 1);
lean_inc_ref(v_firstCmdSnap_3139_);
v_toSnapshot_3140_ = lean_ctor_get(v_oldProcessed_3135_, 0);
lean_inc_ref(v_toSnapshot_3140_);
lean_dec_ref(v_oldProcessed_3135_);
v_cmdState_3141_ = lean_ctor_get(v_val_3138_, 0);
lean_inc_ref(v_cmdState_3141_);
lean_dec(v_val_3138_);
v_stx_x3f_3142_ = lean_ctor_get(v_firstCmdSnap_3139_, 0);
lean_inc(v_stx_x3f_3142_);
lean_inc_ref(v_a_3132_);
v___f_3143_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3143_, 0, v_newParserState_3131_);
lean_closure_set(v___f_3143_, 1, v_cmdState_3141_);
lean_closure_set(v___f_3143_, 2, v_a_3132_);
lean_closure_set(v___f_3143_, 3, v_toSnapshot_3140_);
lean_closure_set(v___f_3143_, 4, v_newStx_3133_);
v___x_3144_ = lean_box(0);
v___x_3145_ = 1;
v___x_3146_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3139_, v___f_3143_, v_stx_x3f_3142_, v___x_3134_, v___x_3144_, v___x_3145_);
return v___x_3146_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec(v___x_3134_);
lean_dec_ref(v_newParserState_3131_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_newStx_3133_);
v___x_3148_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3147_, v_oldProcessed_3135_);
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3149_, lean_object* v_a_3150_, lean_object* v_newStx_3151_, lean_object* v___x_3152_, lean_object* v_oldProcessed_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3149_, v_a_3150_, v_newStx_3151_, v___x_3152_, v_oldProcessed_3153_);
lean_dec_ref(v_a_3150_);
return v_res_3155_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3156_ = 0;
v___x_3157_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3158_ = lean_box(0);
v___x_3159_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3160_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3161_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
lean_ctor_set(v___x_3161_, 2, v___x_3158_);
lean_ctor_set(v___x_3161_, 3, v___x_3157_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*4, v___x_3156_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3162_, lean_object* v_a_3163_, lean_object* v_old_3164_, lean_object* v_newStx_3165_, lean_object* v_newParserState_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_result_x3f_3169_; 
v_result_x3f_3169_ = lean_ctor_get(v_old_3164_, 4);
lean_inc(v_result_x3f_3169_);
if (lean_obj_tag(v_result_x3f_3169_) == 1)
{
lean_object* v_val_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3224_; 
v_val_3170_ = lean_ctor_get(v_result_x3f_3169_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_result_x3f_3169_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3172_ = v_result_x3f_3169_;
v_isShared_3173_ = v_isSharedCheck_3224_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_val_3170_);
lean_dec(v_result_x3f_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3224_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_processedSnap_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3222_; 
v_processedSnap_3174_ = lean_ctor_get(v_val_3170_, 1);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_val_3170_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; 
v_unused_3223_ = lean_ctor_get(v_val_3170_, 0);
lean_dec(v_unused_3223_);
v___x_3176_ = v_val_3170_;
v_isShared_3177_ = v_isSharedCheck_3222_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_processedSnap_3174_);
lean_dec(v_val_3170_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3222_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v_toSnapshot_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3217_; 
v_toSnapshot_3178_ = lean_ctor_get(v_old_3164_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_old_3164_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; lean_object* v_unused_3219_; lean_object* v_unused_3220_; lean_object* v_unused_3221_; 
v_unused_3218_ = lean_ctor_get(v_old_3164_, 4);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_old_3164_, 3);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_old_3164_, 2);
lean_dec(v_unused_3220_);
v_unused_3221_ = lean_ctor_get(v_old_3164_, 1);
lean_dec(v_unused_3221_);
v___x_3180_ = v_old_3164_;
v_isShared_3181_ = v_isSharedCheck_3217_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_toSnapshot_3178_);
lean_dec(v_old_3164_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3217_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_pos_3182_; lean_object* v_endPos_3183_; lean_object* v_stx_x3f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___f_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; lean_object* v_diagnostics_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3213_; 
v_pos_3182_ = lean_ctor_get(v_newParserState_3166_, 0);
v_endPos_3183_ = lean_ctor_get(v_toProcessingContext_3162_, 3);
v_stx_x3f_3184_ = lean_ctor_get(v_processedSnap_3174_, 0);
lean_inc(v_stx_x3f_3184_);
lean_inc(v_endPos_3183_);
lean_inc(v_pos_3182_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v_pos_3182_);
lean_ctor_set(v___x_3185_, 1, v_endPos_3183_);
v___x_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_inc_ref(v___x_3186_);
lean_inc(v_newStx_3165_);
lean_inc_ref(v_a_3163_);
lean_inc_ref(v_newParserState_3166_);
v___f_3187_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3187_, 0, v_newParserState_3166_);
lean_closure_set(v___f_3187_, 1, v_a_3163_);
lean_closure_set(v___f_3187_, 2, v_newStx_3165_);
lean_closure_set(v___f_3187_, 3, v___x_3186_);
v___x_3188_ = lean_box(0);
v___x_3189_ = 1;
v___x_3190_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3174_, v___f_3187_, v_stx_x3f_3184_, v___x_3186_, v___x_3188_, v___x_3189_);
v_diagnostics_3191_ = lean_ctor_get(v_toSnapshot_3178_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_toSnapshot_3178_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; lean_object* v_unused_3215_; lean_object* v_unused_3216_; 
v_unused_3214_ = lean_ctor_get(v_toSnapshot_3178_, 3);
lean_dec(v_unused_3214_);
v_unused_3215_ = lean_ctor_get(v_toSnapshot_3178_, 2);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_toSnapshot_3178_, 0);
lean_dec(v_unused_3216_);
v___x_3193_ = v_toSnapshot_3178_;
v_isShared_3194_ = v_isSharedCheck_3213_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_diagnostics_3191_);
lean_dec(v_toSnapshot_3178_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3213_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3195_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3196_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 1, v___x_3190_);
lean_ctor_set(v___x_3176_, 0, v_newParserState_3166_);
v___x_3198_ = v___x_3176_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_newParserState_3166_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3190_);
v___x_3198_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3200_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3198_);
v___x_3200_ = v___x_3172_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
uint8_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3201_ = 0;
v___x_3202_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3165_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_newStx_3165_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 3, v___x_3196_);
lean_ctor_set(v___x_3193_, 2, v___x_3188_);
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3205_ = v___x_3193_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_diagnostics_3191_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v___x_3196_);
v___x_3205_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
lean_ctor_set_uint8(v___x_3205_, sizeof(void*)*4, v___x_3201_);
v___x_3206_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3203_, v___x_3205_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 4, v___x_3200_);
lean_ctor_set(v___x_3180_, 3, v_newStx_3165_);
lean_ctor_set(v___x_3180_, 2, v_toProcessingContext_3162_);
lean_ctor_set(v___x_3180_, 1, v___x_3206_);
lean_ctor_set(v___x_3180_, 0, v___x_3202_);
v___x_3208_ = v___x_3180_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_toProcessingContext_3162_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v_newStx_3165_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v___x_3200_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
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
lean_dec(v_result_x3f_3169_);
lean_dec_ref(v_newParserState_3166_);
lean_dec(v_newStx_3165_);
lean_dec_ref(v_toProcessingContext_3162_);
return v_old_3164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3225_, lean_object* v_a_3226_, lean_object* v_old_3227_, lean_object* v_newStx_3228_, lean_object* v_newParserState_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3225_, v_a_3226_, v_old_3227_, v_newStx_3228_, v_newParserState_3229_, v___y_3230_);
lean_dec_ref(v___y_3230_);
lean_dec_ref(v_a_3226_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3233_, lean_object* v_setupImports_3234_, lean_object* v_old_x3f_3235_, lean_object* v___f_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
lean_inc_ref(v_toProcessingContext_3233_);
v___x_3239_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3233_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3309_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3309_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3309_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_snd_3244_; lean_object* v_fst_3245_; lean_object* v_fst_3246_; lean_object* v_snd_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3308_; 
v_snd_3244_ = lean_ctor_get(v_a_3240_, 1);
lean_inc(v_snd_3244_);
v_fst_3245_ = lean_ctor_get(v_a_3240_, 0);
lean_inc(v_fst_3245_);
lean_dec(v_a_3240_);
v_fst_3246_ = lean_ctor_get(v_snd_3244_, 0);
v_snd_3247_ = lean_ctor_get(v_snd_3244_, 1);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_snd_3244_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3249_ = v_snd_3244_;
v_isShared_3250_ = v_isSharedCheck_3308_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_snd_3247_);
lean_inc(v_fst_3246_);
lean_dec(v_snd_3244_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3308_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Lean_MessageLog_hasErrors(v_snd_3247_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; lean_object* v___y_3254_; 
lean_inc(v_fst_3245_);
v___x_3252_ = l_Lean_Syntax_unsetTrailing(v_fst_3245_);
if (lean_obj_tag(v_old_x3f_3235_) == 1)
{
lean_object* v_val_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3291_; 
v_val_3275_ = lean_ctor_get(v_old_x3f_3235_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_old_x3f_3235_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3277_ = v_old_x3f_3235_;
v_isShared_3278_ = v_isSharedCheck_3291_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_val_3275_);
lean_dec(v_old_x3f_3235_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3291_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_stx_3279_; lean_object* v_result_x3f_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v_stx_3279_ = lean_ctor_get(v_val_3275_, 3);
v_result_x3f_3280_ = lean_ctor_get(v_val_3275_, 4);
lean_inc(v_stx_3279_);
v___x_3281_ = l_Lean_Syntax_unsetTrailing(v_stx_3279_);
lean_inc(v___x_3252_);
v___x_3282_ = l_Lean_Syntax_eqWithInfo(v___x_3252_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_inc(v_result_x3f_3280_);
lean_del_object(v___x_3277_);
lean_dec(v_val_3275_);
lean_dec_ref(v___f_3236_);
if (lean_obj_tag(v_result_x3f_3280_) == 0)
{
v___y_3254_ = v___y_3237_;
goto v___jp_3253_;
}
else
{
lean_object* v_val_3283_; lean_object* v_processedSnap_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_val_3283_ = lean_ctor_get(v_result_x3f_3280_, 0);
lean_inc(v_val_3283_);
lean_dec_ref(v_result_x3f_3280_);
v_processedSnap_3284_ = lean_ctor_get(v_val_3283_, 1);
lean_inc_ref(v_processedSnap_3284_);
lean_dec(v_val_3283_);
v___x_3285_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3286_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3285_, v_processedSnap_3284_);
v___y_3254_ = v___y_3237_;
goto v___jp_3253_;
}
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
lean_dec(v___x_3252_);
lean_del_object(v___x_3249_);
lean_dec(v_snd_3247_);
lean_del_object(v___x_3242_);
lean_dec_ref(v_setupImports_3234_);
lean_dec_ref(v_toProcessingContext_3233_);
lean_inc_ref(v___y_3237_);
v___x_3287_ = lean_apply_5(v___f_3236_, v_val_3275_, v_fst_3245_, v_fst_3246_, v___y_3237_, lean_box(0));
if (v_isShared_3278_ == 0)
{
lean_ctor_set_tag(v___x_3277_, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3287_);
v___x_3289_ = v___x_3277_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_dec_ref(v___f_3236_);
lean_dec(v_old_x3f_3235_);
v___y_3254_ = v___y_3237_;
goto v___jp_3253_;
}
v___jp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3255_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3247_);
lean_inc(v_fst_3246_);
lean_inc(v_fst_3245_);
v___x_3256_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3234_, v___x_3252_, v_fst_3245_, v_fst_3246_, v___y_3254_);
v___x_3257_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3258_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3259_ = lean_box(0);
v___x_3260_ = lean_unsigned_to_nat(32u);
v___x_3261_ = lean_mk_empty_array_with_capacity(v___x_3260_);
lean_dec_ref(v___x_3261_);
v___x_3262_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3256_);
v___x_3264_ = v___x_3249_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_fst_3246_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v___x_3256_);
v___x_3264_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3257_);
lean_ctor_set(v___x_3266_, 1, v___x_3258_);
lean_ctor_set(v___x_3266_, 2, v___x_3259_);
lean_ctor_set(v___x_3266_, 3, v___x_3262_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*4, v___x_3251_);
lean_inc(v_fst_3245_);
v___x_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_fst_3245_);
v___x_3268_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3268_, 0, v___x_3257_);
lean_ctor_set(v___x_3268_, 1, v___x_3255_);
lean_ctor_set(v___x_3268_, 2, v___x_3259_);
lean_ctor_set(v___x_3268_, 3, v___x_3262_);
lean_ctor_set_uint8(v___x_3268_, sizeof(void*)*4, v___x_3251_);
v___x_3269_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3267_, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3266_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
lean_ctor_set(v___x_3270_, 2, v_toProcessingContext_3233_);
lean_ctor_set(v___x_3270_, 3, v_fst_3245_);
lean_ctor_set(v___x_3270_, 4, v___x_3265_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3270_);
v___x_3272_ = v___x_3242_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
lean_del_object(v___x_3249_);
lean_dec(v_fst_3246_);
lean_dec_ref(v___f_3236_);
lean_dec(v_old_x3f_3235_);
lean_dec_ref(v_setupImports_3234_);
v___x_3292_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3247_);
v___x_3293_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3294_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_unsigned_to_nat(32u);
v___x_3297_ = lean_mk_empty_array_with_capacity(v___x_3296_);
lean_dec_ref(v___x_3297_);
v___x_3298_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3299_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3299_, 0, v___x_3293_);
lean_ctor_set(v___x_3299_, 1, v___x_3294_);
lean_ctor_set(v___x_3299_, 2, v___x_3295_);
lean_ctor_set(v___x_3299_, 3, v___x_3298_);
lean_ctor_set_uint8(v___x_3299_, sizeof(void*)*4, v___x_3251_);
lean_inc(v_fst_3245_);
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_fst_3245_);
v___x_3301_ = 0;
v___x_3302_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3302_, 0, v___x_3293_);
lean_ctor_set(v___x_3302_, 1, v___x_3292_);
lean_ctor_set(v___x_3302_, 2, v___x_3295_);
lean_ctor_set(v___x_3302_, 3, v___x_3298_);
lean_ctor_set_uint8(v___x_3302_, sizeof(void*)*4, v___x_3301_);
v___x_3303_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3300_, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3299_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
lean_ctor_set(v___x_3304_, 2, v_toProcessingContext_3233_);
lean_ctor_set(v___x_3304_, 3, v_fst_3245_);
lean_ctor_set(v___x_3304_, 4, v___x_3295_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3304_);
v___x_3306_ = v___x_3242_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v___f_3236_);
lean_dec(v_old_x3f_3235_);
lean_dec_ref(v_setupImports_3234_);
lean_dec_ref(v_toProcessingContext_3233_);
v_a_3310_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3239_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3239_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3318_, lean_object* v_setupImports_3319_, lean_object* v_old_x3f_3320_, lean_object* v___f_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3318_, v_setupImports_3319_, v_old_x3f_3320_, v___f_3321_, v___y_3322_);
lean_dec_ref(v___y_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3325_, lean_object* v_toProcessingContext_3326_, lean_object* v_x_3327_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3328_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3325_);
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3331_, 0, v_x_3327_);
lean_ctor_set(v___x_3331_, 1, v___x_3328_);
lean_ctor_set(v___x_3331_, 2, v_toProcessingContext_3326_);
lean_ctor_set(v___x_3331_, 3, v___x_3329_);
lean_ctor_set(v___x_3331_, 4, v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3332_, lean_object* v_old_x3f_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_toProcessingContext_3336_; lean_object* v___x_3337_; lean_object* v___f_3338_; lean_object* v___f_3339_; lean_object* v___f_3340_; 
v_toProcessingContext_3336_ = lean_ctor_get(v_a_3334_, 0);
v___x_3337_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3334_);
lean_inc_ref_n(v_toProcessingContext_3336_, 3);
v___f_3338_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3338_, 0, v_toProcessingContext_3336_);
lean_closure_set(v___f_3338_, 1, v_a_3334_);
lean_inc(v_old_x3f_3333_);
v___f_3339_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3339_, 0, v_toProcessingContext_3336_);
lean_closure_set(v___f_3339_, 1, v_setupImports_3332_);
lean_closure_set(v___f_3339_, 2, v_old_x3f_3333_);
lean_closure_set(v___f_3339_, 3, v___f_3338_);
v___f_3340_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3340_, 0, v___x_3337_);
lean_closure_set(v___f_3340_, 1, v_toProcessingContext_3336_);
if (lean_obj_tag(v_old_x3f_3333_) == 1)
{
lean_object* v_val_3341_; lean_object* v_result_x3f_3342_; 
v_val_3341_ = lean_ctor_get(v_old_x3f_3333_, 0);
lean_inc(v_val_3341_);
lean_dec_ref(v_old_x3f_3333_);
v_result_x3f_3342_ = lean_ctor_get(v_val_3341_, 4);
if (lean_obj_tag(v_result_x3f_3342_) == 1)
{
lean_object* v_stx_3343_; lean_object* v_val_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_stx_3343_ = lean_ctor_get(v_val_3341_, 3);
lean_inc(v_stx_3343_);
v_val_3344_ = lean_ctor_get(v_result_x3f_3342_, 0);
lean_inc(v_val_3341_);
v___x_3345_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3341_);
v___x_3346_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3345_);
if (lean_obj_tag(v___x_3346_) == 1)
{
lean_object* v_val_3347_; 
v_val_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_val_3347_);
lean_dec_ref(v___x_3346_);
if (lean_obj_tag(v_val_3347_) == 1)
{
lean_object* v_val_3348_; lean_object* v_firstCmdSnap_3349_; lean_object* v___x_3350_; 
v_val_3348_ = lean_ctor_get(v_val_3347_, 0);
lean_inc(v_val_3348_);
lean_dec_ref(v_val_3347_);
v_firstCmdSnap_3349_ = lean_ctor_get(v_val_3348_, 1);
lean_inc_ref(v_firstCmdSnap_3349_);
lean_dec(v_val_3348_);
v___x_3350_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3349_);
if (lean_obj_tag(v___x_3350_) == 1)
{
lean_object* v_val_3351_; lean_object* v_nextCmdSnap_x3f_3352_; 
v_val_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_val_3351_);
lean_dec_ref(v___x_3350_);
v_nextCmdSnap_x3f_3352_ = lean_ctor_get(v_val_3351_, 4);
lean_inc(v_nextCmdSnap_x3f_3352_);
lean_dec(v_val_3351_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3352_) == 0)
{
lean_object* v___x_3353_; 
lean_dec(v_stx_3343_);
lean_dec(v_val_3341_);
v___x_3353_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3353_;
}
else
{
lean_object* v_val_3354_; lean_object* v___x_3355_; 
v_val_3354_ = lean_ctor_get(v_nextCmdSnap_x3f_3352_, 0);
lean_inc(v_val_3354_);
lean_dec_ref(v_nextCmdSnap_x3f_3352_);
v___x_3355_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3354_);
if (lean_obj_tag(v___x_3355_) == 1)
{
lean_object* v_val_3356_; lean_object* v_parserState_3357_; lean_object* v_pos_3358_; uint8_t v___x_3359_; 
v_val_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_val_3356_);
lean_dec_ref(v___x_3355_);
v_parserState_3357_ = lean_ctor_get(v_val_3356_, 2);
lean_inc_ref(v_parserState_3357_);
lean_dec(v_val_3356_);
v_pos_3358_ = lean_ctor_get(v_parserState_3357_, 0);
lean_inc(v_pos_3358_);
lean_dec_ref(v_parserState_3357_);
v___x_3359_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3358_, v_a_3334_);
lean_dec(v_pos_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_dec(v_stx_3343_);
lean_dec(v_val_3341_);
v___x_3360_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3360_;
}
else
{
lean_object* v_parserState_3361_; lean_object* v___x_3362_; 
lean_dec_ref(v___f_3340_);
lean_dec_ref(v___f_3339_);
v_parserState_3361_ = lean_ctor_get(v_val_3344_, 0);
lean_inc_ref(v_parserState_3361_);
lean_inc_ref(v_toProcessingContext_3336_);
v___x_3362_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3336_, v_a_3334_, v_val_3341_, v_stx_3343_, v_parserState_3361_, v_a_3334_);
return v___x_3362_;
}
}
else
{
lean_object* v___x_3363_; 
lean_dec(v___x_3355_);
lean_dec(v_stx_3343_);
lean_dec(v_val_3341_);
v___x_3363_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3363_;
}
}
}
else
{
lean_object* v___x_3364_; 
lean_dec(v___x_3350_);
lean_dec(v_stx_3343_);
lean_dec(v_val_3341_);
v___x_3364_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3364_;
}
}
else
{
lean_object* v___x_3365_; 
lean_dec(v_val_3347_);
lean_dec(v_stx_3343_);
lean_dec(v_val_3341_);
v___x_3365_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3365_;
}
}
else
{
lean_object* v___x_3366_; 
lean_dec(v___x_3346_);
lean_dec(v_stx_3343_);
lean_dec(v_val_3341_);
v___x_3366_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3366_;
}
}
else
{
lean_object* v___x_3367_; 
lean_dec(v_val_3341_);
v___x_3367_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3367_;
}
}
else
{
lean_object* v___x_3368_; 
lean_dec(v_old_x3f_3333_);
v___x_3368_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3340_, v___f_3339_, v_a_3334_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3369_, lean_object* v_old_x3f_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3369_, v_old_x3f_3370_, v_a_3371_);
lean_dec_ref(v_a_3371_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3374_, lean_object* v_old_x3f_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v___x_3378_; 
lean_inc(v_old_x3f_3375_);
v___x_3378_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3378_, 0, v_setupImports_3374_);
lean_closure_set(v___x_3378_, 1, v_old_x3f_3375_);
if (lean_obj_tag(v_old_x3f_3375_) == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_box(0);
v___x_3380_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3378_, v___x_3379_, v_a_3376_);
return v___x_3380_;
}
else
{
lean_object* v_val_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3390_; 
v_val_3381_ = lean_ctor_get(v_old_x3f_3375_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_old_x3f_3375_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3383_ = v_old_x3f_3375_;
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_val_3381_);
lean_dec(v_old_x3f_3375_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_ictx_3385_; lean_object* v___x_3387_; 
v_ictx_3385_ = lean_ctor_get(v_val_3381_, 2);
lean_inc_ref(v_ictx_3385_);
lean_dec(v_val_3381_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v_ictx_3385_);
v___x_3387_ = v___x_3383_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_ictx_3385_);
v___x_3387_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3378_, v___x_3387_, v_a_3376_);
return v___x_3388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3391_, lean_object* v_old_x3f_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Language_Lean_process(v_setupImports_3391_, v_old_x3f_3392_, v_a_3393_);
lean_dec_ref(v_a_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3396_, lean_object* v_parserState_3397_, lean_object* v_commandState_3398_, lean_object* v_old_x3f_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3409_; 
v___x_3401_ = lean_io_promise_new();
v___x_3402_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3399_) == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_box(0);
v___y_3409_ = v___x_3423_;
goto v___jp_3408_;
}
else
{
lean_object* v_val_3424_; lean_object* v_snd_3425_; lean_object* v___x_3426_; 
v_val_3424_ = lean_ctor_get(v_old_x3f_3399_, 0);
v_snd_3425_ = lean_ctor_get(v_val_3424_, 1);
lean_inc(v_snd_3425_);
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v_snd_3425_);
v___y_3409_ = v___x_3426_;
goto v___jp_3408_;
}
v___jp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3404_, v___y_3405_, v_inputCtx_3396_);
lean_dec(v___x_3406_);
v___x_3407_ = l_IO_Promise_result_x21___redArg(v___x_3401_);
lean_dec(v___x_3401_);
return v___x_3407_;
}
v___jp_3408_:
{
uint8_t v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = 1;
v___x_3411_ = lean_box(v___x_3410_);
lean_inc(v___x_3401_);
v___x_3412_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 8, 6);
lean_closure_set(v___x_3412_, 0, v___y_3409_);
lean_closure_set(v___x_3412_, 1, v_parserState_3397_);
lean_closure_set(v___x_3412_, 2, v_commandState_3398_);
lean_closure_set(v___x_3412_, 3, v___x_3401_);
lean_closure_set(v___x_3412_, 4, v___x_3411_);
lean_closure_set(v___x_3412_, 5, v___x_3402_);
if (lean_obj_tag(v_old_x3f_3399_) == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_box(0);
v___y_3404_ = v___x_3412_;
v___y_3405_ = v___x_3413_;
goto v___jp_3403_;
}
else
{
lean_object* v_val_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3422_; 
v_val_3414_ = lean_ctor_get(v_old_x3f_3399_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_old_x3f_3399_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3416_ = v_old_x3f_3399_;
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_val_3414_);
lean_dec(v_old_x3f_3399_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_fst_3418_; lean_object* v___x_3420_; 
v_fst_3418_ = lean_ctor_get(v_val_3414_, 0);
lean_inc(v_fst_3418_);
lean_dec(v_val_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_fst_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_fst_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
v___y_3404_ = v___x_3412_;
v___y_3405_ = v___x_3420_;
goto v___jp_3403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3427_, lean_object* v_parserState_3428_, lean_object* v_commandState_3429_, lean_object* v_old_x3f_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3427_, v_parserState_3428_, v_commandState_3429_, v_old_x3f_3430_);
lean_dec_ref(v_inputCtx_3427_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3433_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3434_; 
v_nextCmdSnap_x3f_3434_ = lean_ctor_get(v_snap_3433_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3434_) == 1)
{
lean_object* v_val_3435_; lean_object* v___x_3436_; 
lean_inc_ref(v_nextCmdSnap_x3f_3434_);
lean_dec_ref(v_snap_3433_);
v_val_3435_ = lean_ctor_get(v_nextCmdSnap_x3f_3434_, 0);
lean_inc(v_val_3435_);
lean_dec_ref(v_nextCmdSnap_x3f_3434_);
v___x_3436_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3435_);
v_snap_3433_ = v___x_3436_;
goto _start;
}
else
{
lean_object* v_elabSnap_3438_; lean_object* v_resultSnap_3439_; lean_object* v___x_3440_; lean_object* v_cmdState_3441_; lean_object* v___x_3442_; 
v_elabSnap_3438_ = lean_ctor_get(v_snap_3433_, 3);
lean_inc_ref(v_elabSnap_3438_);
lean_dec_ref(v_snap_3433_);
v_resultSnap_3439_ = lean_ctor_get(v_elabSnap_3438_, 2);
lean_inc_ref(v_resultSnap_3439_);
lean_dec_ref(v_elabSnap_3438_);
v___x_3440_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3439_);
v_cmdState_3441_ = lean_ctor_get(v___x_3440_, 1);
lean_inc_ref(v_cmdState_3441_);
lean_dec(v___x_3440_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v_cmdState_3441_);
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3443_){
_start:
{
lean_object* v_result_x3f_3444_; 
v_result_x3f_3444_ = lean_ctor_get(v_snap_3443_, 4);
lean_inc(v_result_x3f_3444_);
lean_dec_ref(v_snap_3443_);
if (lean_obj_tag(v_result_x3f_3444_) == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_box(0);
return v___x_3445_;
}
else
{
lean_object* v_val_3446_; lean_object* v_processedSnap_3447_; lean_object* v___x_3448_; lean_object* v_result_x3f_3449_; 
v_val_3446_ = lean_ctor_get(v_result_x3f_3444_, 0);
lean_inc(v_val_3446_);
lean_dec_ref(v_result_x3f_3444_);
v_processedSnap_3447_ = lean_ctor_get(v_val_3446_, 1);
lean_inc_ref(v_processedSnap_3447_);
lean_dec(v_val_3446_);
v___x_3448_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3447_);
v_result_x3f_3449_ = lean_ctor_get(v___x_3448_, 2);
lean_inc(v_result_x3f_3449_);
lean_dec(v___x_3448_);
if (lean_obj_tag(v_result_x3f_3449_) == 0)
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_box(0);
return v___x_3450_;
}
else
{
lean_object* v_val_3451_; lean_object* v_firstCmdSnap_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v_val_3451_ = lean_ctor_get(v_result_x3f_3449_, 0);
lean_inc(v_val_3451_);
lean_dec_ref(v_result_x3f_3449_);
v_firstCmdSnap_3452_ = lean_ctor_get(v_val_3451_, 1);
lean_inc_ref(v_firstCmdSnap_3452_);
lean_dec(v_val_3451_);
v___x_3453_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3452_);
v___x_3454_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3453_);
return v___x_3454_;
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
res = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
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

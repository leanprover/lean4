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
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object**);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parsing"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parseHeader"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__1_value),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 110, 119, 15, 255, 246, 245, 53)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5;
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
static const lean_string_object l_Lean_Language_Lean_truncateToHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "truncateToHeader"};
static const lean_object* l_Lean_Language_Lean_truncateToHeader___closed__0 = (const lean_object*)&l_Lean_Language_Lean_truncateToHeader___closed__0_value;
static const lean_ctor_object l_Lean_Language_Lean_truncateToHeader___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Language_Lean_truncateToHeader___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_truncateToHeader___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 167, 200, 3, 29, 231, 56, 85)}};
static const lean_ctor_object l_Lean_Language_Lean_truncateToHeader___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_truncateToHeader___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 222, 85, 59, 197, 113, 89, 237)}};
static const lean_ctor_object l_Lean_Language_Lean_truncateToHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Language_Lean_truncateToHeader___closed__1_value_aux_2),((lean_object*)&l_Lean_Language_Lean_truncateToHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 193, 8, 11, 35, 111, 210, 68)}};
static const lean_object* l_Lean_Language_Lean_truncateToHeader___closed__1 = (const lean_object*)&l_Lean_Language_Lean_truncateToHeader___closed__1_value;
static lean_once_cell_t l_Lean_Language_Lean_truncateToHeader___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_truncateToHeader___closed__2;
static lean_once_cell_t l_Lean_Language_Lean_truncateToHeader___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_truncateToHeader___closed__3;
static lean_once_cell_t l_Lean_Language_Lean_truncateToHeader___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_truncateToHeader___closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object*);
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
lean_dec_ref_known(v___x_121_, 1);
return v_a_122_;
}
else
{
lean_object* v_a_123_; lean_object* v_toProcessingContext_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_123_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_121_, 1);
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
lean_dec_ref_known(v_defValue_227_, 0);
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
lean_dec_ref_known(v___x_247_, 3);
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
lean_dec_ref_known(v_x_317_, 5);
v___x_327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_315_, v_init_316_, v_l_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
if (lean_obj_tag(v_a_328_) == 0)
{
lean_object* v_a_329_; 
lean_dec_ref_known(v___x_327_, 1);
lean_dec(v_r_326_);
lean_dec(v_v_324_);
lean_dec(v_k_323_);
v_a_329_ = lean_ctor_get(v_a_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_a_328_, 1);
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
lean_dec_ref_known(v___x_327_, 1);
if (lean_obj_tag(v_v_324_) == 0)
{
lean_object* v_val_339_; lean_object* v_v_340_; lean_object* v___x_341_; 
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v___x_338_, 1);
v_v_340_ = lean_ctor_get(v_v_324_, 0);
lean_inc_ref(v_v_340_);
lean_dec_ref_known(v_v_324_, 1);
v___x_341_ = l_Lean_Language_Lean_setOption(v_a_330_, v_val_339_, v___x_337_, v_v_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
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
lean_dec_ref_known(v___x_338_, 1);
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
lean_dec_ref_known(v___x_327_, 1);
if (lean_obj_tag(v_a_377_) == 0)
{
lean_object* v_a_378_; 
lean_dec(v_r_326_);
v_a_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v_a_377_, 1);
v_d_320_ = v_a_378_;
goto v___jp_319_;
}
else
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v_a_377_, 1);
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
lean_dec_ref_known(v___x_391_, 1);
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
lean_object* v___x_510_; lean_object* v_infoState_511_; lean_object* v_trees_512_; lean_object* v___x_513_; lean_object* v_infoState_514_; lean_object* v_env_515_; lean_object* v_messages_516_; lean_object* v_scopes_517_; lean_object* v_usedQuotCtxts_518_; lean_object* v_nextMacroScope_519_; lean_object* v_maxRecDepth_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_traceState_523_; lean_object* v_snapshotTasks_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_545_; 
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
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_545_ == 0)
{
v___x_526_ = v___x_513_;
v_isShared_527_ = v_isSharedCheck_545_;
goto v_resetjp_525_;
}
else
{
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
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_545_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v_enabled_528_; lean_object* v_assignment_529_; lean_object* v_lazyAssignment_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_543_; 
v_enabled_528_ = lean_ctor_get_uint8(v_infoState_514_, sizeof(void*)*3);
v_assignment_529_ = lean_ctor_get(v_infoState_514_, 0);
v_lazyAssignment_530_ = lean_ctor_get(v_infoState_514_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_infoState_514_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_infoState_514_, 2);
lean_dec(v_unused_544_);
v___x_532_ = v_infoState_514_;
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_lazyAssignment_530_);
lean_inc(v_assignment_529_);
lean_dec(v_infoState_514_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_543_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_assignment_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_lazyAssignment_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v___x_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_542_, sizeof(void*)*3, v_enabled_528_);
v___x_536_ = v_reuseFailAlloc_542_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 8, v___x_536_);
v___x_538_ = v___x_526_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_env_515_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_messages_516_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_scopes_517_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_usedQuotCtxts_518_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v_maxRecDepth_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_541_, 8, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 9, v_traceState_523_);
lean_ctor_set(v_reuseFailAlloc_541_, 10, v_snapshotTasks_524_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_st_ref_set(v___y_508_, v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_trees_512_);
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_546_);
lean_dec(v___y_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_556_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_557_, lean_object* v_opt_558_){
_start:
{
lean_object* v_name_559_; lean_object* v_defValue_560_; lean_object* v_map_561_; lean_object* v___x_562_; 
v_name_559_ = lean_ctor_get(v_opt_558_, 0);
v_defValue_560_ = lean_ctor_get(v_opt_558_, 1);
v_map_561_ = lean_ctor_get(v_opts_557_, 0);
v___x_562_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_561_, v_name_559_);
if (lean_obj_tag(v___x_562_) == 0)
{
uint8_t v___x_563_; 
v___x_563_ = lean_unbox(v_defValue_560_);
return v___x_563_;
}
else
{
lean_object* v_val_564_; 
v_val_564_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v___x_562_, 1);
if (lean_obj_tag(v_val_564_) == 1)
{
uint8_t v_v_565_; 
v_v_565_ = lean_ctor_get_uint8(v_val_564_, 0);
lean_dec_ref_known(v_val_564_, 0);
return v_v_565_;
}
else
{
uint8_t v___x_566_; 
lean_dec(v_val_564_);
v___x_566_ = lean_unbox(v_defValue_560_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_567_, lean_object* v_opt_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_567_, v_opt_568_);
lean_dec_ref(v_opt_568_);
lean_dec_ref(v_opts_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_val_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_577_, lean_object* v_val_578_){
_start:
{
lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_inc_ref(v_val_578_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_579_, 0, v_val_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_inst_577_);
lean_ctor_set(v___x_580_, 1, v_val_578_);
v___x_581_ = lean_mk_thunk(v___f_579_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_583_, lean_object* v_cmds_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_586_);
lean_dec_ref(v___x_588_);
v___x_589_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_583_, v_cmds_584_, v___y_585_, v___y_586_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_590_, lean_object* v_cmds_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_590_, v_cmds_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_596_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
lean_ctor_set(v___x_601_, 3, v___x_600_);
lean_ctor_set(v___x_601_, 4, v___x_599_);
lean_ctor_set(v___x_601_, 5, v___x_599_);
lean_ctor_set(v___x_601_, 6, v___x_599_);
lean_ctor_set(v___x_601_, 7, v___x_599_);
lean_ctor_set(v___x_601_, 8, v___x_599_);
lean_ctor_set(v___x_601_, 9, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(32u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_605_ = ((size_t)5ULL);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_unsigned_to_nat(32u);
v___x_608_ = lean_mk_empty_array_with_capacity(v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_610_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_606_);
lean_ctor_set(v___x_610_, 3, v___x_606_);
lean_ctor_set_usize(v___x_610_, 4, v___x_605_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_box(1);
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; lean_object* v_env_619_; lean_object* v___x_620_; lean_object* v_scopes_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_opts_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_618_ = lean_st_ref_get(v___y_616_);
v_env_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_env_619_);
lean_dec(v___x_618_);
v___x_620_ = lean_st_ref_get(v___y_616_);
v_scopes_621_ = lean_ctor_get(v___x_620_, 2);
lean_inc(v_scopes_621_);
lean_dec(v___x_620_);
v___x_622_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_623_ = l_List_head_x21___redArg(v___x_622_, v_scopes_621_);
lean_dec(v_scopes_621_);
v_opts_624_ = lean_ctor_get(v___x_623_, 1);
lean_inc_ref(v_opts_624_);
lean_dec(v___x_623_);
v___x_625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_627_, 0, v_env_619_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
lean_ctor_set(v___x_627_, 3, v_opts_624_);
v___x_628_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_msgData_615_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_630_, v___y_631_);
lean_dec(v___y_631_);
return v_res_633_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_634_, uint8_t v_suppressElabErrors_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 1)
{
lean_object* v_pre_637_; 
v_pre_637_ = lean_ctor_get(v_x_636_, 0);
if (lean_obj_tag(v_pre_637_) == 0)
{
lean_object* v_str_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_str_638_ = lean_ctor_get(v_x_636_, 1);
v___x_639_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_640_ = lean_string_dec_eq(v_str_638_, v___x_639_);
if (v___x_640_ == 0)
{
return v___y_634_;
}
else
{
return v_suppressElabErrors_635_;
}
}
else
{
return v___y_634_;
}
}
else
{
return v___y_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_641_, lean_object* v_suppressElabErrors_642_, lean_object* v_x_643_){
_start:
{
uint8_t v___y_9164__boxed_644_; uint8_t v_suppressElabErrors_boxed_645_; uint8_t v_res_646_; lean_object* v_r_647_; 
v___y_9164__boxed_644_ = lean_unbox(v___y_641_);
v_suppressElabErrors_boxed_645_ = lean_unbox(v_suppressElabErrors_642_);
v_res_646_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9164__boxed_644_, v_suppressElabErrors_boxed_645_, v_x_643_);
lean_dec(v_x_643_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_649_, lean_object* v_msgData_650_, uint8_t v_severity_651_, uint8_t v_isSilent_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; uint8_t v___y_720_; uint8_t v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; uint8_t v___y_751_; lean_object* v___y_752_; uint8_t v___y_756_; uint8_t v___y_757_; uint8_t v___y_758_; uint8_t v___x_773_; uint8_t v___y_775_; uint8_t v___y_776_; uint8_t v___y_777_; uint8_t v___y_779_; uint8_t v___x_791_; 
v___x_773_ = 2;
v___x_791_ = l_Lean_instBEqMessageSeverity_beq(v_severity_651_, v___x_773_);
if (v___x_791_ == 0)
{
v___y_779_ = v___x_791_;
goto v___jp_778_;
}
else
{
uint8_t v___x_792_; 
lean_inc_ref(v_msgData_650_);
v___x_792_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_650_);
v___y_779_ = v___x_792_;
goto v___jp_778_;
}
v___jp_656_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Elab_Command_getScope___redArg(v___y_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_Elab_Command_getScope___redArg(v___y_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_702_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_702_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_702_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_702_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v_currNamespace_673_; lean_object* v_openDecls_674_; lean_object* v_env_675_; lean_object* v_messages_676_; lean_object* v_scopes_677_; lean_object* v_usedQuotCtxts_678_; lean_object* v_nextMacroScope_679_; lean_object* v_maxRecDepth_680_; lean_object* v_ngen_681_; lean_object* v_auxDeclNGen_682_; lean_object* v_infoState_683_; lean_object* v_traceState_684_; lean_object* v_snapshotTasks_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_701_; 
v___x_672_ = lean_st_ref_take(v___y_664_);
v_currNamespace_673_ = lean_ctor_get(v_a_666_, 2);
lean_inc(v_currNamespace_673_);
lean_dec(v_a_666_);
v_openDecls_674_ = lean_ctor_get(v_a_668_, 3);
lean_inc(v_openDecls_674_);
lean_dec(v_a_668_);
v_env_675_ = lean_ctor_get(v___x_672_, 0);
v_messages_676_ = lean_ctor_get(v___x_672_, 1);
v_scopes_677_ = lean_ctor_get(v___x_672_, 2);
v_usedQuotCtxts_678_ = lean_ctor_get(v___x_672_, 3);
v_nextMacroScope_679_ = lean_ctor_get(v___x_672_, 4);
v_maxRecDepth_680_ = lean_ctor_get(v___x_672_, 5);
v_ngen_681_ = lean_ctor_get(v___x_672_, 6);
v_auxDeclNGen_682_ = lean_ctor_get(v___x_672_, 7);
v_infoState_683_ = lean_ctor_get(v___x_672_, 8);
v_traceState_684_ = lean_ctor_get(v___x_672_, 9);
v_snapshotTasks_685_ = lean_ctor_get(v___x_672_, 10);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_701_ == 0)
{
v___x_687_ = v___x_672_;
v_isShared_688_ = v_isSharedCheck_701_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snapshotTasks_685_);
lean_inc(v_traceState_684_);
lean_inc(v_infoState_683_);
lean_inc(v_auxDeclNGen_682_);
lean_inc(v_ngen_681_);
lean_inc(v_maxRecDepth_680_);
lean_inc(v_nextMacroScope_679_);
lean_inc(v_usedQuotCtxts_678_);
lean_inc(v_scopes_677_);
lean_inc(v_messages_676_);
lean_inc(v_env_675_);
lean_dec(v___x_672_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_701_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_currNamespace_673_);
lean_ctor_set(v___x_689_, 1, v_openDecls_674_);
v___x_690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_659_);
lean_inc_ref(v___y_662_);
lean_inc_ref(v___y_657_);
v___x_691_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_691_, 0, v___y_657_);
lean_ctor_set(v___x_691_, 1, v___y_661_);
lean_ctor_set(v___x_691_, 2, v___y_658_);
lean_ctor_set(v___x_691_, 3, v___y_662_);
lean_ctor_set(v___x_691_, 4, v___x_690_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5, v___y_660_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5 + 1, v___y_663_);
lean_ctor_set_uint8(v___x_691_, sizeof(void*)*5 + 2, v_isSilent_652_);
v___x_692_ = l_Lean_MessageLog_add(v___x_691_, v_messages_676_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_692_);
v___x_694_ = v___x_687_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_env_675_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_scopes_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_usedQuotCtxts_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_nextMacroScope_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_maxRecDepth_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_ngen_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_auxDeclNGen_682_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_infoState_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 9, v_traceState_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 10, v_snapshotTasks_685_);
v___x_694_ = v_reuseFailAlloc_700_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = lean_st_ref_set(v___y_664_, v___x_694_);
v___x_696_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_696_);
v___x_698_ = v___x_670_;
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
lean_dec(v_a_666_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
v_a_703_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_667_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_667_);
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
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
v_a_711_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_665_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_665_);
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
v_fileName_725_ = lean_ctor_get(v___y_653_, 0);
v_fileMap_726_ = lean_ctor_get(v___y_653_, 1);
v_suppressElabErrors_727_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*10);
v___x_728_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_650_);
v___x_729_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_728_, v___y_654_);
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
v___y_657_ = v_fileName_725_;
v___y_658_ = v___x_736_;
v___y_659_ = v_a_730_;
v___y_660_ = v___y_721_;
v___y_661_ = v___x_734_;
v___y_662_ = v___x_737_;
v___y_663_ = v___y_722_;
v___y_664_ = v___y_654_;
goto v___jp_656_;
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
lean_dec_ref_known(v___x_736_, 1);
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
v___y_657_ = v_fileName_725_;
v___y_658_ = v___x_736_;
v___y_659_ = v_a_730_;
v___y_660_ = v___y_721_;
v___y_661_ = v___x_734_;
v___y_662_ = v___x_737_;
v___y_663_ = v___y_722_;
v___y_664_ = v___y_654_;
goto v___jp_656_;
}
}
}
}
v___jp_747_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Syntax_getTailPos_x3f(v___y_749_, v___y_750_);
lean_dec(v___y_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_inc(v___y_752_);
v___y_720_ = v___y_748_;
v___y_721_ = v___y_750_;
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
lean_dec_ref_known(v___x_753_, 1);
v___y_720_ = v___y_748_;
v___y_721_ = v___y_750_;
v___y_722_ = v___y_751_;
v___y_723_ = v___y_752_;
v___y_724_ = v_val_754_;
goto v___jp_719_;
}
}
v___jp_755_:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Elab_Command_getRef___redArg(v___y_653_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_ref_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v_ref_761_ = l_Lean_replaceRef(v_ref_649_, v_a_760_);
lean_dec(v_a_760_);
v___x_762_ = l_Lean_Syntax_getPos_x3f(v_ref_761_, v___y_757_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___y_748_ = v___y_756_;
v___y_749_ = v_ref_761_;
v___y_750_ = v___y_757_;
v___y_751_ = v___y_758_;
v___y_752_ = v___x_763_;
goto v___jp_747_;
}
else
{
lean_object* v_val_764_; 
v_val_764_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_764_);
lean_dec_ref_known(v___x_762_, 1);
v___y_748_ = v___y_756_;
v___y_749_ = v_ref_761_;
v___y_750_ = v___y_757_;
v___y_751_ = v___y_758_;
v___y_752_ = v_val_764_;
goto v___jp_747_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_msgData_650_);
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
v___y_758_ = v_severity_651_;
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
v___x_780_ = lean_st_ref_get(v___y_654_);
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
v___x_786_ = l_Lean_instBEqMessageSeverity_beq(v_severity_651_, v___x_785_);
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
lean_dec_ref(v_msgData_650_);
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
lean_dec_ref_known(v___x_809_, 1);
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
lean_dec_ref_known(v_ex_858_, 2);
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
lean_dec_ref_known(v_ex_858_, 2);
v___y_867_ = v___x_890_;
goto v___jp_866_;
}
else
{
lean_dec_ref_known(v_ex_858_, 2);
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
lean_dec_ref_known(v___x_868_, 1);
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
lean_dec_ref_known(v___x_900_, 1);
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
lean_dec_ref_known(v___x_917_, 1);
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
lean_dec_ref_known(v___x_917_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1050_, lean_object* v_cmds_1051_, lean_object* v_cmdState_1052_, lean_object* v_beginPos_1053_, lean_object* v_snap_1054_, lean_object* v_cancelTk_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_env_1058_; lean_object* v_scopes_1059_; lean_object* v_usedQuotCtxts_1060_; lean_object* v_nextMacroScope_1061_; lean_object* v_maxRecDepth_1062_; lean_object* v_ngen_1063_; lean_object* v_auxDeclNGen_1064_; lean_object* v_infoState_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1141_; 
v_env_1058_ = lean_ctor_get(v_cmdState_1052_, 0);
v_scopes_1059_ = lean_ctor_get(v_cmdState_1052_, 2);
v_usedQuotCtxts_1060_ = lean_ctor_get(v_cmdState_1052_, 3);
v_nextMacroScope_1061_ = lean_ctor_get(v_cmdState_1052_, 4);
v_maxRecDepth_1062_ = lean_ctor_get(v_cmdState_1052_, 5);
v_ngen_1063_ = lean_ctor_get(v_cmdState_1052_, 6);
v_auxDeclNGen_1064_ = lean_ctor_get(v_cmdState_1052_, 7);
v_infoState_1065_ = lean_ctor_get(v_cmdState_1052_, 8);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_cmdState_1052_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1142_ = lean_ctor_get(v_cmdState_1052_, 10);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_cmdState_1052_, 9);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_cmdState_1052_, 1);
lean_dec(v_unused_1144_);
v___x_1067_ = v_cmdState_1052_;
v_isShared_1068_ = v_isSharedCheck_1141_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_infoState_1065_);
lean_inc(v_auxDeclNGen_1064_);
lean_inc(v_ngen_1063_);
lean_inc(v_maxRecDepth_1062_);
lean_inc(v_nextMacroScope_1061_);
lean_inc(v_usedQuotCtxts_1060_);
lean_inc(v_scopes_1059_);
lean_inc(v_env_1058_);
lean_dec(v_cmdState_1052_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1141_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1069_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1070_ = l_List_head_x21___redArg(v___x_1069_, v_scopes_1059_);
v___x_1071_ = l_Lean_MessageLog_empty;
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1074_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 10, v___x_1074_);
lean_ctor_set(v___x_1067_, 9, v___x_1073_);
lean_ctor_set(v___x_1067_, 1, v___x_1071_);
v___x_1076_ = v___x_1067_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_env_1058_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_scopes_1059_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_usedQuotCtxts_1060_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_nextMacroScope_1061_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_maxRecDepth_1062_);
lean_ctor_set(v_reuseFailAlloc_1140_, 6, v_ngen_1063_);
lean_ctor_set(v_reuseFailAlloc_1140_, 7, v_auxDeclNGen_1064_);
lean_ctor_set(v_reuseFailAlloc_1140_, 8, v_infoState_1065_);
lean_ctor_set(v_reuseFailAlloc_1140_, 9, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1140_, 10, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v_toProcessingContext_1078_; lean_object* v_fileName_1079_; lean_object* v_fileMap_1080_; lean_object* v_opts_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; uint8_t v___y_1091_; lean_object* v___y_1092_; lean_object* v_messages_1093_; lean_object* v___y_1119_; 
v___x_1077_ = lean_st_mk_ref(v___x_1076_);
v_toProcessingContext_1078_ = lean_ctor_get(v_a_1056_, 0);
v_fileName_1079_ = lean_ctor_get(v_toProcessingContext_1078_, 1);
v_fileMap_1080_ = lean_ctor_get(v_toProcessingContext_1078_, 2);
v_opts_1081_ = lean_ctor_get(v___x_1070_, 1);
lean_inc_ref(v_opts_1081_);
lean_dec(v___x_1070_);
v___f_1082_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1082_, 0, v_stx_1050_);
lean_closure_set(v___f_1082_, 1, v_cmds_1051_);
v___x_1083_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Lean_firstFrontendMacroScope;
v___x_1087_ = lean_box(0);
v___x_1088_ = l_Lean_internal_cmdlineSnapshots;
v___x_1089_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1081_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1139_; 
lean_inc_ref(v_snap_1054_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_snap_1054_);
v___y_1119_ = v___x_1139_;
goto v___jp_1118_;
}
else
{
v___y_1119_ = v___x_1085_;
goto v___jp_1118_;
}
v___jp_1090_:
{
lean_object* v_new_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_env_1100_; lean_object* v_scopes_1101_; lean_object* v_usedQuotCtxts_1102_; lean_object* v_nextMacroScope_1103_; lean_object* v_maxRecDepth_1104_; lean_object* v_ngen_1105_; lean_object* v_auxDeclNGen_1106_; lean_object* v_infoState_1107_; lean_object* v_traceState_1108_; lean_object* v_snapshotTasks_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_new_1094_ = lean_ctor_get(v_snap_1054_, 1);
lean_inc(v_new_1094_);
lean_dec_ref(v_snap_1054_);
v___x_1095_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1096_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1097_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_ctor_set(v___x_1097_, 2, v___x_1085_);
lean_ctor_set(v___x_1097_, 3, v___x_1073_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*4, v___y_1091_);
v___x_1098_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1083_, v___x_1097_);
v___x_1099_ = lean_io_promise_resolve(v___x_1098_, v_new_1094_);
lean_dec(v_new_1094_);
v_env_1100_ = lean_ctor_get(v___y_1092_, 0);
v_scopes_1101_ = lean_ctor_get(v___y_1092_, 2);
v_usedQuotCtxts_1102_ = lean_ctor_get(v___y_1092_, 3);
v_nextMacroScope_1103_ = lean_ctor_get(v___y_1092_, 4);
v_maxRecDepth_1104_ = lean_ctor_get(v___y_1092_, 5);
v_ngen_1105_ = lean_ctor_get(v___y_1092_, 6);
v_auxDeclNGen_1106_ = lean_ctor_get(v___y_1092_, 7);
v_infoState_1107_ = lean_ctor_get(v___y_1092_, 8);
v_traceState_1108_ = lean_ctor_get(v___y_1092_, 9);
v_snapshotTasks_1109_ = lean_ctor_get(v___y_1092_, 10);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___y_1092_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___y_1092_, 1);
lean_dec(v_unused_1117_);
v___x_1111_ = v___y_1092_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snapshotTasks_1109_);
lean_inc(v_traceState_1108_);
lean_inc(v_infoState_1107_);
lean_inc(v_auxDeclNGen_1106_);
lean_inc(v_ngen_1105_);
lean_inc(v_maxRecDepth_1104_);
lean_inc(v_nextMacroScope_1103_);
lean_inc(v_usedQuotCtxts_1102_);
lean_inc(v_scopes_1101_);
lean_inc(v_env_1100_);
lean_dec(v___y_1092_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_messages_1093_);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_env_1100_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_messages_1093_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_scopes_1101_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_usedQuotCtxts_1102_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_nextMacroScope_1103_);
lean_ctor_set(v_reuseFailAlloc_1115_, 5, v_maxRecDepth_1104_);
lean_ctor_set(v_reuseFailAlloc_1115_, 6, v_ngen_1105_);
lean_ctor_set(v_reuseFailAlloc_1115_, 7, v_auxDeclNGen_1106_);
lean_ctor_set(v_reuseFailAlloc_1115_, 8, v_infoState_1107_);
lean_ctor_set(v_reuseFailAlloc_1115_, 9, v_traceState_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 10, v_snapshotTasks_1109_);
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
lean_ctor_set(v___x_1120_, 0, v_cancelTk_1055_);
v___x_1121_ = 0;
lean_inc(v_beginPos_1053_);
lean_inc_ref(v_fileMap_1080_);
lean_inc_ref(v_fileName_1079_);
v___x_1122_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1122_, 0, v_fileName_1079_);
lean_ctor_set(v___x_1122_, 1, v_fileMap_1080_);
lean_ctor_set(v___x_1122_, 2, v___x_1072_);
lean_ctor_set(v___x_1122_, 3, v_beginPos_1053_);
lean_ctor_set(v___x_1122_, 4, v___x_1084_);
lean_ctor_set(v___x_1122_, 5, v___x_1085_);
lean_ctor_set(v___x_1122_, 6, v___x_1086_);
lean_ctor_set(v___x_1122_, 7, v___x_1087_);
lean_ctor_set(v___x_1122_, 8, v___y_1119_);
lean_ctor_set(v___x_1122_, 9, v___x_1120_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*10, v___x_1121_);
lean_inc(v___x_1077_);
v___f_1123_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1123_, 0, v___f_1082_);
lean_closure_set(v___f_1123_, 1, v___x_1122_);
lean_closure_set(v___f_1123_, 2, v___x_1077_);
v___x_1124_ = l_Lean_Core_stderrAsMessages;
v___x_1125_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1081_, v___x_1124_);
lean_dec_ref(v_opts_1081_);
v___x_1126_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1123_, v___x_1125_, v_a_1056_);
v_fst_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_fst_1127_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = lean_st_ref_get(v___x_1077_);
lean_dec(v___x_1077_);
v_messages_1129_ = lean_ctor_get(v___x_1128_, 1);
lean_inc_ref(v_messages_1129_);
v___x_1130_ = lean_string_utf8_byte_size(v_fst_1127_);
v___x_1131_ = lean_nat_dec_eq(v___x_1130_, v___x_1072_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_inc_ref(v_fileMap_1080_);
v___x_1132_ = l_Lean_FileMap_toPosition(v_fileMap_1080_, v_beginPos_1053_);
lean_dec(v_beginPos_1053_);
v___x_1133_ = 0;
v___x_1134_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_fst_1127_);
v___x_1136_ = l_Lean_MessageData_ofFormat(v___x_1135_);
lean_inc_ref(v_fileName_1079_);
v___x_1137_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1137_, 0, v_fileName_1079_);
lean_ctor_set(v___x_1137_, 1, v___x_1132_);
lean_ctor_set(v___x_1137_, 2, v___x_1085_);
lean_ctor_set(v___x_1137_, 3, v___x_1134_);
lean_ctor_set(v___x_1137_, 4, v___x_1136_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*5, v___x_1121_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*5 + 1, v___x_1133_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*5 + 2, v___x_1121_);
v___x_1138_ = l_Lean_MessageLog_add(v___x_1137_, v_messages_1129_);
v___y_1091_ = v___x_1121_;
v___y_1092_ = v___x_1128_;
v_messages_1093_ = v___x_1138_;
goto v___jp_1090_;
}
else
{
lean_dec(v_fst_1127_);
lean_dec(v_beginPos_1053_);
v___y_1091_ = v___x_1121_;
v___y_1092_ = v___x_1128_;
v_messages_1093_ = v_messages_1129_;
goto v___jp_1090_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1145_, lean_object* v_cmds_1146_, lean_object* v_cmdState_1147_, lean_object* v_beginPos_1148_, lean_object* v_snap_1149_, lean_object* v_cancelTk_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1145_, v_cmds_1146_, v_cmdState_1147_, v_beginPos_1148_, v_snap_1149_, v_cancelTk_1150_, v_a_1151_);
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
lean_dec_ref_known(v___x_1194_, 1);
if (lean_obj_tag(v_val_1195_) == 3)
{
lean_object* v_v_1196_; 
v_v_1196_ = lean_ctor_get(v_val_1195_, 0);
lean_inc(v_v_1196_);
lean_dec_ref_known(v_val_1195_, 1);
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
uint8_t v_val_44654__boxed_1270_; size_t v_sz_boxed_1271_; size_t v_i_boxed_1272_; lean_object* v_res_1273_; 
v_val_44654__boxed_1270_ = lean_unbox(v_val_1264_);
v_sz_boxed_1271_ = lean_unbox_usize(v_sz_1266_);
lean_dec(v_sz_1266_);
v_i_boxed_1272_ = lean_unbox_usize(v_i_1267_);
lean_dec(v_i_1267_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1261_, v___x_1262_, v___x_1263_, v_val_44654__boxed_1270_, v_as_1265_, v_sz_boxed_1271_, v_i_boxed_1272_, v_b_1268_);
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
uint8_t v_val_44706__boxed_1313_; size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_val_44706__boxed_1313_ = lean_unbox(v_val_1307_);
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1304_, v___x_1305_, v___x_1306_, v_val_44706__boxed_1313_, v_as_1308_, v_sz_boxed_1314_, v_i_boxed_1315_, v_b_1311_);
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
lean_dec_ref_known(v_fst_1331_, 1);
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
lean_dec_ref_known(v_fst_1341_, 1);
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
lean_dec_ref_known(v___x_1361_, 1);
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
uint8_t v_val_44757__boxed_1386_; size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_val_44757__boxed_1386_ = lean_unbox(v_val_1380_);
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1376_, v___x_1377_, v___x_1378_, v___x_1379_, v_val_44757__boxed_1386_, v_as_1381_, v_sz_boxed_1387_, v_i_boxed_1388_, v_b_1384_);
lean_dec_ref(v_as_1381_);
lean_dec(v___x_1378_);
lean_dec_ref(v_init_1376_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v_init_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v_val_1394_, lean_object* v_n_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_val_44773__boxed_1398_; lean_object* v_res_1399_; 
v_val_44773__boxed_1398_ = lean_unbox(v_val_1394_);
v_res_1399_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v_val_44773__boxed_1398_, v_n_1395_, v_b_1396_);
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
uint8_t v_val_44855__boxed_1439_; size_t v_sz_boxed_1440_; size_t v_i_boxed_1441_; lean_object* v_res_1442_; 
v_val_44855__boxed_1439_ = lean_unbox(v_val_1433_);
v_sz_boxed_1440_ = lean_unbox_usize(v_sz_1435_);
lean_dec(v_sz_1435_);
v_i_boxed_1441_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1430_, v___x_1431_, v___x_1432_, v_val_44855__boxed_1439_, v_as_1434_, v_sz_boxed_1440_, v_i_boxed_1441_, v_b_1437_);
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
uint8_t v_val_44907__boxed_1482_; size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_val_44907__boxed_1482_ = lean_unbox(v_val_1476_);
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1473_, v___x_1474_, v___x_1475_, v_val_44907__boxed_1482_, v_as_1477_, v_sz_boxed_1483_, v_i_boxed_1484_, v_b_1480_);
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
lean_dec_ref_known(v___x_1495_, 1);
return v_a_1496_;
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_1502_; lean_object* v_fst_1503_; 
v_a_1497_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1495_, 1);
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
lean_dec_ref_known(v_fst_1503_, 1);
return v_val_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v___x_1508_, lean_object* v_val_1509_, lean_object* v_t_1510_, lean_object* v_init_1511_, lean_object* v___y_1512_){
_start:
{
uint8_t v_val_44958__boxed_1513_; lean_object* v_res_1514_; 
v_val_44958__boxed_1513_ = lean_unbox(v_val_1509_);
v_res_1514_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1506_, v___x_1507_, v___x_1508_, v_val_44958__boxed_1513_, v_t_1510_, v_init_1511_);
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
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_toProcessingContext_1568_; lean_object* v_fileName_1569_; lean_object* v_fileMap_1570_; lean_object* v_env_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v_fileName_1577_; lean_object* v_fileMap_1578_; lean_object* v_currRecDepth_1579_; lean_object* v_ref_1580_; lean_object* v_currNamespace_1581_; lean_object* v_openDecls_1582_; lean_object* v_initHeartbeats_1583_; lean_object* v_maxHeartbeats_1584_; lean_object* v_quotContext_1585_; lean_object* v_currMacroScope_1586_; lean_object* v_cancelTk_x3f_1587_; uint8_t v_suppressElabErrors_1588_; lean_object* v_inheritedTraceOptions_1589_; lean_object* v___y_1590_; uint8_t v___y_1607_; uint8_t v___x_1627_; 
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
lean_inc_ref(v___x_1563_);
lean_inc_ref(v___x_1535_);
v___x_1564_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1564_, 0, v_env_1534_);
lean_ctor_set(v___x_1564_, 1, v___x_1551_);
lean_ctor_set(v___x_1564_, 2, v___x_1552_);
lean_ctor_set(v___x_1564_, 3, v___x_1554_);
lean_ctor_set(v___x_1564_, 4, v___x_1535_);
lean_ctor_set(v___x_1564_, 5, v___x_1556_);
lean_ctor_set(v___x_1564_, 6, v___x_1561_);
lean_ctor_set(v___x_1564_, 7, v___x_1562_);
lean_ctor_set(v___x_1564_, 8, v___x_1563_);
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
v___x_1627_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1571_);
lean_dec_ref(v_env_1571_);
if (v___x_1627_ == 0)
{
if (v___x_1575_ == 0)
{
v___y_1607_ = v___x_1546_;
goto v___jp_1606_;
}
else
{
v___y_1607_ = v___x_1627_;
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
lean_dec_ref_known(v___x_1593_, 14);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; lean_object* v_traceState_1596_; lean_object* v_traces_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref_known(v___x_1594_, 1);
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
lean_dec_ref_known(v___x_1594_, 1);
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
lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v_nextMacroScope_1610_; lean_object* v_ngen_1611_; lean_object* v_auxDeclNGen_1612_; lean_object* v_traceState_1613_; lean_object* v_messages_1614_; lean_object* v_infoState_1615_; lean_object* v_snapshotTasks_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1625_; 
v___x_1608_ = lean_st_ref_take(v___x_1565_);
v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
v_nextMacroScope_1610_ = lean_ctor_get(v___x_1608_, 1);
v_ngen_1611_ = lean_ctor_get(v___x_1608_, 2);
v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1608_, 3);
v_traceState_1613_ = lean_ctor_get(v___x_1608_, 4);
v_messages_1614_ = lean_ctor_get(v___x_1608_, 6);
v_infoState_1615_ = lean_ctor_get(v___x_1608_, 7);
v_snapshotTasks_1616_ = lean_ctor_get(v___x_1608_, 8);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v___x_1608_, 5);
lean_dec(v_unused_1626_);
v___x_1618_ = v___x_1608_;
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_snapshotTasks_1616_);
lean_inc(v_infoState_1615_);
lean_inc(v_messages_1614_);
lean_inc(v_traceState_1613_);
lean_inc(v_auxDeclNGen_1612_);
lean_inc(v_ngen_1611_);
lean_inc(v_nextMacroScope_1610_);
lean_inc(v_env_1609_);
lean_dec(v___x_1608_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = l_Lean_Kernel_enableDiag(v_env_1609_, v___x_1575_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 5, v___x_1556_);
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_nextMacroScope_1610_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_ngen_1611_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_auxDeclNGen_1612_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_traceState_1613_);
lean_ctor_set(v_reuseFailAlloc_1624_, 5, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1624_, 6, v_messages_1614_);
lean_ctor_set(v_reuseFailAlloc_1624_, 7, v_infoState_1615_);
lean_ctor_set(v_reuseFailAlloc_1624_, 8, v_snapshotTasks_1616_);
v___x_1622_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_st_ref_set(v___x_1565_, v___x_1622_);
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
lean_object* v___x_1628_ = _args[0];
lean_object* v___x_1629_ = _args[1];
lean_object* v___x_1630_ = _args[2];
lean_object* v___x_1631_ = _args[3];
lean_object* v___x_1632_ = _args[4];
lean_object* v_env_1633_ = _args[5];
lean_object* v___x_1634_ = _args[6];
lean_object* v___x_1635_ = _args[7];
lean_object* v_a_1636_ = _args[8];
lean_object* v_opts_1637_ = _args[9];
lean_object* v___x_1638_ = _args[10];
lean_object* v_pos_1639_ = _args[11];
lean_object* v_val_1640_ = _args[12];
lean_object* v___x_1641_ = _args[13];
lean_object* v___x_1642_ = _args[14];
lean_object* v___x_1643_ = _args[15];
lean_object* v___x_1644_ = _args[16];
lean_object* v___x_1645_ = _args[17];
lean_object* v_x_1646_ = _args[18];
lean_object* v___y_1647_ = _args[19];
_start:
{
size_t v___x_45019__boxed_1648_; uint8_t v___x_45020__boxed_1649_; uint8_t v_val_45024__boxed_1650_; uint8_t v___x_45029__boxed_1651_; lean_object* v_res_1652_; 
v___x_45019__boxed_1648_ = lean_unbox_usize(v___x_1631_);
lean_dec(v___x_1631_);
v___x_45020__boxed_1649_ = lean_unbox(v___x_1632_);
v_val_45024__boxed_1650_ = lean_unbox(v_val_1640_);
v___x_45029__boxed_1651_ = lean_unbox(v___x_1645_);
v_res_1652_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1628_, v___x_1629_, v___x_1630_, v___x_45019__boxed_1648_, v___x_45020__boxed_1649_, v_env_1633_, v___x_1634_, v___x_1635_, v_a_1636_, v_opts_1637_, v___x_1638_, v_pos_1639_, v_val_45024__boxed_1650_, v___x_1641_, v___x_1642_, v___x_1643_, v___x_1644_, v___x_45029__boxed_1651_, v_x_1646_);
lean_dec(v_pos_1639_);
lean_dec_ref(v_a_1636_);
lean_dec(v___x_1635_);
lean_dec(v___x_1629_);
return v_res_1652_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1659_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1660_ = l_Lean_Name_append(v___x_1659_, v___x_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1661_, lean_object* v___x_1662_, uint8_t v_val_1663_, lean_object* v_val_1664_, lean_object* v_val_1665_, lean_object* v___x_1666_, lean_object* v___x_1667_, uint8_t v___x_1668_, lean_object* v_a_1669_, lean_object* v_pos_1670_, lean_object* v_infoSt_1671_){
_start:
{
lean_object* v___y_1674_; lean_object* v_msgLog_1675_; lean_object* v___y_1681_; lean_object* v_trees_1713_; lean_object* v_size_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_trees_1713_ = lean_ctor_get(v_infoSt_1671_, 2);
v_size_1714_ = lean_ctor_get(v_trees_1713_, 2);
v___x_1715_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1716_ = lean_nat_dec_lt(v___x_1667_, v_size_1714_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = l_outOfBounds___redArg(v___x_1715_);
v___y_1681_ = v___x_1717_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1715_, v_trees_1713_, v___x_1667_);
v___y_1681_ = v___x_1718_;
goto v___jp_1680_;
}
v___jp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1676_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1675_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1674_);
v___x_1678_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1678_, 0, v___x_1661_);
lean_ctor_set(v___x_1678_, 1, v___x_1676_);
lean_ctor_set(v___x_1678_, 2, v___x_1677_);
lean_ctor_set(v___x_1678_, 3, v___x_1662_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*4, v_val_1663_);
v___x_1679_ = lean_io_promise_resolve(v___x_1678_, v_val_1664_);
return v___x_1679_;
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_scopes_1684_; lean_object* v___x_1685_; lean_object* v_opts_1686_; uint8_t v_hasTrace_1687_; lean_object* v___x_1688_; 
v___x_1682_ = l_Lean_inheritedTraceOptions;
v___x_1683_ = lean_st_ref_get(v___x_1682_);
v_scopes_1684_ = lean_ctor_get(v_val_1665_, 2);
v___x_1685_ = l_List_head_x21___redArg(v___x_1666_, v_scopes_1684_);
v_opts_1686_ = lean_ctor_get(v___x_1685_, 1);
lean_inc_ref(v_opts_1686_);
lean_dec(v___x_1685_);
v_hasTrace_1687_ = lean_ctor_get_uint8(v_opts_1686_, sizeof(void*)*1);
v___x_1688_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1687_ == 0)
{
lean_dec_ref(v_opts_1686_);
lean_dec(v___x_1683_);
lean_dec(v___x_1667_);
v___y_1674_ = v___y_1681_;
v_msgLog_1675_ = v___x_1688_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1689_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1690_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1691_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1683_, v_opts_1686_, v___x_1691_);
lean_dec_ref(v_opts_1686_);
lean_dec(v___x_1683_);
if (v___x_1692_ == 0)
{
lean_dec(v___x_1667_);
v___y_1674_ = v___y_1681_;
v_msgLog_1675_ = v___x_1688_;
goto v___jp_1673_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_box(0);
lean_inc_ref(v___y_1681_);
v___x_1694_ = l_Lean_Elab_InfoTree_format(v___y_1681_, v___x_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; double v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_toProcessingContext_1699_; lean_object* v_fileName_1700_; lean_object* v_fileMap_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = lean_float_of_nat(v___x_1667_);
v___x_1697_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1698_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1698_, 0, v___x_1689_);
lean_ctor_set(v___x_1698_, 1, v___x_1693_);
lean_ctor_set(v___x_1698_, 2, v___x_1697_);
lean_ctor_set_float(v___x_1698_, sizeof(void*)*3, v___x_1696_);
lean_ctor_set_float(v___x_1698_, sizeof(void*)*3 + 8, v___x_1696_);
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*3 + 16, v___x_1668_);
v_toProcessingContext_1699_ = lean_ctor_get(v_a_1669_, 0);
v_fileName_1700_ = lean_ctor_get(v_toProcessingContext_1699_, 1);
v_fileMap_1701_ = lean_ctor_get(v_toProcessingContext_1699_, 2);
v___x_1702_ = l_Lean_MessageData_nil;
v___x_1703_ = l_Lean_MessageData_ofFormat(v_a_1695_);
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = lean_mk_empty_array_with_capacity(v___x_1704_);
v___x_1706_ = lean_array_push(v___x_1705_, v___x_1703_);
v___x_1707_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1698_);
lean_ctor_set(v___x_1707_, 1, v___x_1702_);
lean_ctor_set(v___x_1707_, 2, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1690_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
lean_inc_ref(v_fileMap_1701_);
v___x_1709_ = l_Lean_FileMap_toPosition(v_fileMap_1701_, v_pos_1670_);
v___x_1710_ = 0;
lean_inc_ref(v_fileName_1700_);
v___x_1711_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1711_, 0, v_fileName_1700_);
lean_ctor_set(v___x_1711_, 1, v___x_1709_);
lean_ctor_set(v___x_1711_, 2, v___x_1693_);
lean_ctor_set(v___x_1711_, 3, v___x_1697_);
lean_ctor_set(v___x_1711_, 4, v___x_1708_);
lean_ctor_set_uint8(v___x_1711_, sizeof(void*)*5, v_val_1663_);
lean_ctor_set_uint8(v___x_1711_, sizeof(void*)*5 + 1, v___x_1710_);
lean_ctor_set_uint8(v___x_1711_, sizeof(void*)*5 + 2, v_val_1663_);
v___x_1712_ = l_Lean_MessageLog_add(v___x_1711_, v___x_1688_);
v___y_1674_ = v___y_1681_;
v_msgLog_1675_ = v___x_1712_;
goto v___jp_1673_;
}
else
{
lean_dec_ref_known(v___x_1694_, 1);
lean_dec(v___x_1667_);
v___y_1674_ = v___y_1681_;
v_msgLog_1675_ = v___x_1688_;
goto v___jp_1673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v_val_1721_, lean_object* v_val_1722_, lean_object* v_val_1723_, lean_object* v___x_1724_, lean_object* v___x_1725_, lean_object* v___x_1726_, lean_object* v_a_1727_, lean_object* v_pos_1728_, lean_object* v_infoSt_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v_val_45206__boxed_1731_; uint8_t v___x_45211__boxed_1732_; lean_object* v_res_1733_; 
v_val_45206__boxed_1731_ = lean_unbox(v_val_1721_);
v___x_45211__boxed_1732_ = lean_unbox(v___x_1726_);
v_res_1733_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1719_, v___x_1720_, v_val_45206__boxed_1731_, v_val_1722_, v_val_1723_, v___x_1724_, v___x_1725_, v___x_45211__boxed_1732_, v_a_1727_, v_pos_1728_, v_infoSt_1729_);
lean_dec_ref(v_infoSt_1729_);
lean_dec(v_pos_1728_);
lean_dec_ref(v_a_1727_);
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_val_1723_);
lean_dec(v_val_1722_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1735_, size_t v_i_1736_, size_t v_stop_1737_, lean_object* v_b_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_eq(v_i_1736_, v_stop_1737_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; 
v___x_1741_ = lean_array_uget_borrowed(v_as_1735_, v_i_1736_);
v___f_1742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1741_);
v___x_1743_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1742_, v___x_1741_);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1736_, v___x_1744_);
v_i_1736_ = v___x_1745_;
v_b_1738_ = v___x_1743_;
goto _start;
}
else
{
return v_b_1738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1747_, lean_object* v_i_1748_, lean_object* v_stop_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_){
_start:
{
size_t v_i_boxed_1752_; size_t v_stop_boxed_1753_; lean_object* v_res_1754_; 
v_i_boxed_1752_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_stop_boxed_1753_ = lean_unbox_usize(v_stop_1749_);
lean_dec(v_stop_1749_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1747_, v_i_boxed_1752_, v_stop_boxed_1753_, v_b_1750_);
lean_dec_ref(v_as_1747_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1755_, lean_object* v_cmds_1756_, lean_object* v_stx_1757_, lean_object* v_newParserState_1758_, lean_object* v_val_1759_, lean_object* v_sync_1760_, lean_object* v_val_1761_, lean_object* v_a_1762_, lean_object* v_oldNext_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v_sync_boxed_1765_; lean_object* v_res_1766_; 
v_sync_boxed_1765_ = lean_unbox(v_sync_1760_);
v_res_1766_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1755_, v_cmds_1756_, v_stx_1757_, v_newParserState_1758_, v_val_1759_, v_sync_boxed_1765_, v_val_1761_, v_a_1762_, v_oldNext_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1767_, lean_object* v_cmds_1768_, lean_object* v_stx_1769_, lean_object* v_newParserState_1770_, lean_object* v_val_1771_, uint8_t v_sync_1772_, lean_object* v_val_1773_, lean_object* v_a_1774_, lean_object* v_oldResult_1775_){
_start:
{
lean_object* v_task_1777_; lean_object* v___x_1778_; lean_object* v___f_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
v_task_1777_ = lean_ctor_get(v_val_1767_, 3);
lean_inc_ref(v_task_1777_);
lean_dec_ref(v_val_1767_);
v___x_1778_ = lean_box(v_sync_1772_);
lean_inc_ref(v_a_1774_);
v___f_1779_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 10, 8);
lean_closure_set(v___f_1779_, 0, v_oldResult_1775_);
lean_closure_set(v___f_1779_, 1, v_cmds_1768_);
lean_closure_set(v___f_1779_, 2, v_stx_1769_);
lean_closure_set(v___f_1779_, 3, v_newParserState_1770_);
lean_closure_set(v___f_1779_, 4, v_val_1771_);
lean_closure_set(v___f_1779_, 5, v___x_1778_);
lean_closure_set(v___f_1779_, 6, v_val_1773_);
lean_closure_set(v___f_1779_, 7, v_a_1774_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = 1;
v___x_1782_ = l_BaseIO_chainTask___redArg(v_task_1777_, v___f_1779_, v___x_1780_, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1783_, lean_object* v_cmds_1784_, lean_object* v_stx_1785_, lean_object* v_newParserState_1786_, lean_object* v_val_1787_, lean_object* v_sync_1788_, lean_object* v_val_1789_, lean_object* v_a_1790_, lean_object* v_oldResult_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v_sync_boxed_1793_; lean_object* v_res_1794_; 
v_sync_boxed_1793_ = lean_unbox(v_sync_1788_);
v_res_1794_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1783_, v_cmds_1784_, v_stx_1785_, v_newParserState_1786_, v_val_1787_, v_sync_boxed_1793_, v_val_1789_, v_a_1790_, v_oldResult_1791_);
lean_dec_ref(v_a_1790_);
return v_res_1794_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1797_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1799_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1808_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1809_ = l_Lean_Name_append(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1810_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1813_, lean_object* v_val_1814_, lean_object* v_cmds_1815_, lean_object* v_fst_1816_, lean_object* v_fst_1817_, uint8_t v_val_1818_, lean_object* v_a_1819_, lean_object* v_snd_1820_, lean_object* v___x_1821_, uint8_t v___x_1822_, lean_object* v_fst_1823_, lean_object* v_val_1824_, lean_object* v_val_1825_, lean_object* v_val_1826_, lean_object* v_snd_1827_, lean_object* v_prom_1828_, lean_object* v___x_1829_, lean_object* v___f_1830_, lean_object* v___f_1831_, lean_object* v___f_1832_, lean_object* v_pos_1833_, lean_object* v_cmdState_1834_, lean_object* v_opts_1835_, lean_object* v___x_1836_, lean_object* v_old_x3f_1837_, lean_object* v_parseCancelTk_1838_, lean_object* v_next_x3f_1839_){
_start:
{
lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v_snapshotTasks_1847_; lean_object* v_traceTask_1848_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; size_t v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v_env_1884_; lean_object* v_messages_1885_; lean_object* v_scopes_1886_; lean_object* v_infoState_1887_; lean_object* v_traceState_1888_; lean_object* v_snapshotTasks_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_reportedCmdState_1898_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; size_t v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v_reportedCmdState_1955_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; size_t v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; size_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_2018_; 
if (lean_obj_tag(v_next_x3f_1839_) == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref(v_parseCancelTk_1838_);
v___x_2071_ = lean_box(0);
v___y_2018_ = v___x_2071_;
goto v___jp_2017_;
}
else
{
lean_object* v_toProcessingContext_2072_; lean_object* v_val_2073_; lean_object* v_pos_2074_; lean_object* v_endPos_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_toProcessingContext_2072_ = lean_ctor_get(v_a_1819_, 0);
v_val_2073_ = lean_ctor_get(v_next_x3f_1839_, 0);
v_pos_2074_ = lean_ctor_get(v_fst_1817_, 0);
v_endPos_2075_ = lean_ctor_get(v_toProcessingContext_2072_, 3);
v___x_2076_ = lean_box(0);
lean_inc(v_endPos_2075_);
lean_inc(v_pos_2074_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_pos_2074_);
lean_ctor_set(v___x_2077_, 1, v_endPos_2075_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_parseCancelTk_1838_);
v___x_2080_ = l_IO_Promise_result_x21___redArg(v_val_2073_);
v___x_2081_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
lean_ctor_set(v___x_2081_, 1, v___x_2078_);
lean_ctor_set(v___x_2081_, 2, v___x_2079_);
lean_ctor_set(v___x_2081_, 3, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___y_2018_ = v___x_2082_;
goto v___jp_2017_;
}
v___jp_1841_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1849_, 0, v___y_1842_);
lean_ctor_set(v___x_1849_, 1, v___x_1813_);
lean_ctor_set(v___x_1849_, 2, v___y_1844_);
lean_ctor_set(v___x_1849_, 3, v_traceTask_1848_);
v___x_1850_ = lean_array_push(v_snapshotTasks_1847_, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___y_1843_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_io_promise_resolve(v___x_1851_, v_val_1814_);
if (lean_obj_tag(v_next_x3f_1839_) == 1)
{
lean_object* v_val_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_val_1853_ = lean_ctor_get(v_next_x3f_1839_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v_next_x3f_1839_, 1);
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_array_push(v_cmds_1815_, v_fst_1816_);
v___x_1856_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1854_, v_fst_1817_, v___y_1846_, v_val_1853_, v_val_1818_, v___y_1845_, v___x_1855_, v_a_1819_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v_next_x3f_1839_);
lean_dec_ref(v_fst_1817_);
lean_dec(v_fst_1816_);
lean_dec_ref(v_cmds_1815_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
}
v___jp_1858_:
{
lean_object* v_snapshotTasks_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_snapshotTasks_1865_ = lean_ctor_get(v___y_1864_, 10);
lean_inc_ref(v_snapshotTasks_1865_);
v___x_1866_ = lean_mk_empty_array_with_capacity(v___y_1862_);
lean_dec(v___y_1862_);
lean_inc_ref(v___y_1861_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___y_1861_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_task_pure(v___x_1867_);
v___y_1842_ = v___y_1859_;
v___y_1843_ = v___y_1861_;
v___y_1844_ = v___y_1860_;
v___y_1845_ = v___y_1863_;
v___y_1846_ = v___y_1864_;
v_snapshotTasks_1847_ = v_snapshotTasks_1865_;
v_traceTask_1848_ = v___x_1868_;
goto v___jp_1841_;
}
v___jp_1869_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_opts_1908_; uint8_t v_hasTrace_1909_; 
v___x_1899_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1885_);
v___x_1900_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1900_, 0, v___y_1895_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
lean_ctor_set(v___x_1900_, 2, v___y_1878_);
lean_ctor_set(v___x_1900_, 3, v_traceState_1888_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*4, v_val_1818_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_reportedCmdState_1898_);
v___x_1902_ = lean_io_promise_resolve(v___x_1901_, v_val_1825_);
v___x_1903_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1887_);
lean_inc(v___y_1893_);
v___x_1904_ = l_BaseIO_chainTask___redArg(v___x_1903_, v___y_1882_, v___y_1893_, v___x_1822_);
v___x_1905_ = l_Lean_inheritedTraceOptions;
v___x_1906_ = lean_st_ref_get(v___x_1905_);
v___x_1907_ = l_List_head_x21___redArg(v___x_1829_, v_scopes_1886_);
lean_dec(v_scopes_1886_);
lean_dec_ref(v___x_1829_);
v_opts_1908_ = lean_ctor_get(v___x_1907_, 1);
lean_inc_ref(v_opts_1908_);
lean_dec(v___x_1907_);
v_hasTrace_1909_ = lean_ctor_get_uint8(v_opts_1908_, sizeof(void*)*1);
if (v_hasTrace_1909_ == 0)
{
lean_dec_ref(v_opts_1908_);
lean_dec(v___x_1906_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_snapshotTasks_1889_);
lean_dec_ref(v_env_1884_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v_pos_1833_);
lean_dec_ref(v___f_1832_);
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec(v___x_1821_);
v___y_1859_ = v___y_1890_;
v___y_1860_ = v___y_1891_;
v___y_1861_ = v___y_1892_;
v___y_1862_ = v___y_1893_;
v___y_1863_ = v___y_1896_;
v___y_1864_ = v___y_1883_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1906_, v_opts_1908_, v___x_1910_);
lean_dec(v___x_1906_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_opts_1908_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_snapshotTasks_1889_);
lean_dec_ref(v_env_1884_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v_pos_1833_);
lean_dec_ref(v___f_1832_);
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec(v___x_1821_);
v___y_1859_ = v___y_1890_;
v___y_1860_ = v___y_1891_;
v___y_1861_ = v___y_1892_;
v___y_1862_ = v___y_1893_;
v___y_1863_ = v___y_1896_;
v___y_1864_ = v___y_1883_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
lean_inc_n(v___y_1893_, 3);
v___x_1912_ = lean_task_map(v___f_1830_, v___y_1894_, v___y_1893_, v___x_1822_);
lean_inc_n(v___y_1891_, 3);
lean_inc_n(v___y_1879_, 2);
lean_inc_n(v___y_1897_, 2);
v___x_1913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1913_, 0, v___y_1897_);
lean_ctor_set(v___x_1913_, 1, v___y_1879_);
lean_ctor_set(v___x_1913_, 2, v___y_1891_);
lean_ctor_set(v___x_1913_, 3, v___x_1912_);
v___x_1914_ = lean_task_map(v___f_1831_, v___y_1881_, v___y_1893_, v___x_1822_);
v___x_1915_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1915_, 0, v___y_1897_);
lean_ctor_set(v___x_1915_, 1, v___y_1879_);
lean_ctor_set(v___x_1915_, 2, v___y_1891_);
lean_ctor_set(v___x_1915_, 3, v___x_1914_);
v___x_1916_ = lean_task_map(v___f_1832_, v___y_1880_, v___y_1893_, v___x_1822_);
v___x_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1917_, 0, v___y_1897_);
lean_ctor_set(v___x_1917_, 1, v___y_1879_);
lean_ctor_set(v___x_1917_, 2, v___y_1891_);
lean_ctor_set(v___x_1917_, 3, v___x_1916_);
v___x_1918_ = lean_unsigned_to_nat(3u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1913_);
v___x_1921_ = lean_array_push(v___x_1920_, v___x_1915_);
v___x_1922_ = lean_array_push(v___x_1921_, v___x_1917_);
v___x_1923_ = l_Array_append___redArg(v___x_1922_, v_snapshotTasks_1889_);
lean_inc_ref(v___y_1892_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___y_1892_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
lean_inc_ref(v___x_1924_);
v___x_1925_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1924_);
v___x_1926_ = lean_box_usize(v___y_1874_);
v___x_1927_ = lean_box(v___x_1822_);
v___x_1928_ = lean_box(v_val_1818_);
v___x_1929_ = lean_box(v___x_1911_);
lean_inc_ref(v_a_1819_);
lean_inc_ref(v___y_1870_);
v___f_1930_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_1930_, 0, v___x_1821_);
lean_closure_set(v___f_1930_, 1, v___y_1876_);
lean_closure_set(v___f_1930_, 2, v___y_1875_);
lean_closure_set(v___f_1930_, 3, v___x_1926_);
lean_closure_set(v___f_1930_, 4, v___x_1927_);
lean_closure_set(v___f_1930_, 5, v_env_1884_);
lean_closure_set(v___f_1930_, 6, v___y_1870_);
lean_closure_set(v___f_1930_, 7, v___x_1905_);
lean_closure_set(v___f_1930_, 8, v_a_1819_);
lean_closure_set(v___f_1930_, 9, v_opts_1908_);
lean_closure_set(v___f_1930_, 10, v___x_1924_);
lean_closure_set(v___f_1930_, 11, v_pos_1833_);
lean_closure_set(v___f_1930_, 12, v___x_1928_);
lean_closure_set(v___f_1930_, 13, v___y_1873_);
lean_closure_set(v___f_1930_, 14, v___y_1877_);
lean_closure_set(v___f_1930_, 15, v___y_1871_);
lean_closure_set(v___f_1930_, 16, v___y_1872_);
lean_closure_set(v___f_1930_, 17, v___x_1929_);
v___x_1931_ = lean_io_bind_task(v___x_1925_, v___f_1930_, v___y_1893_, v_val_1818_);
v___y_1842_ = v___y_1890_;
v___y_1843_ = v___y_1892_;
v___y_1844_ = v___y_1891_;
v___y_1845_ = v___y_1896_;
v___y_1846_ = v___y_1883_;
v_snapshotTasks_1847_ = v_snapshotTasks_1889_;
v_traceTask_1848_ = v___x_1931_;
goto v___jp_1841_;
}
}
}
v___jp_1932_:
{
lean_object* v_env_1956_; lean_object* v_messages_1957_; lean_object* v_scopes_1958_; lean_object* v_infoState_1959_; lean_object* v_traceState_1960_; lean_object* v_snapshotTasks_1961_; 
v_env_1956_ = lean_ctor_get(v___y_1946_, 0);
lean_inc_ref(v_env_1956_);
v_messages_1957_ = lean_ctor_get(v___y_1946_, 1);
lean_inc_ref(v_messages_1957_);
v_scopes_1958_ = lean_ctor_get(v___y_1946_, 2);
lean_inc(v_scopes_1958_);
v_infoState_1959_ = lean_ctor_get(v___y_1946_, 8);
lean_inc_ref(v_infoState_1959_);
v_traceState_1960_ = lean_ctor_get(v___y_1946_, 9);
lean_inc_ref(v_traceState_1960_);
v_snapshotTasks_1961_ = lean_ctor_get(v___y_1946_, 10);
lean_inc_ref(v_snapshotTasks_1961_);
v___y_1870_ = v___y_1933_;
v___y_1871_ = v___y_1934_;
v___y_1872_ = v___y_1935_;
v___y_1873_ = v___y_1936_;
v___y_1874_ = v___y_1938_;
v___y_1875_ = v___y_1937_;
v___y_1876_ = v___y_1939_;
v___y_1877_ = v___y_1940_;
v___y_1878_ = v___y_1941_;
v___y_1879_ = v___y_1942_;
v___y_1880_ = v___y_1943_;
v___y_1881_ = v___y_1944_;
v___y_1882_ = v___y_1945_;
v___y_1883_ = v___y_1946_;
v_env_1884_ = v_env_1956_;
v_messages_1885_ = v_messages_1957_;
v_scopes_1886_ = v_scopes_1958_;
v_infoState_1887_ = v_infoState_1959_;
v_traceState_1888_ = v_traceState_1960_;
v_snapshotTasks_1889_ = v_snapshotTasks_1961_;
v___y_1890_ = v___y_1947_;
v___y_1891_ = v___y_1948_;
v___y_1892_ = v___y_1949_;
v___y_1893_ = v___y_1950_;
v___y_1894_ = v___y_1951_;
v___y_1895_ = v___y_1952_;
v___y_1896_ = v___y_1953_;
v___y_1897_ = v___y_1954_;
v_reportedCmdState_1898_ = v_reportedCmdState_1955_;
goto v___jp_1869_;
}
v___jp_1962_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; uint8_t v___x_1992_; 
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___y_1986_);
lean_ctor_set(v___x_1987_, 1, v_val_1824_);
lean_inc_ref(v___y_1983_);
lean_inc_n(v_pos_1833_, 2);
lean_inc_ref(v_cmds_1815_);
lean_inc(v_fst_1816_);
v___x_1988_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1816_, v_cmds_1815_, v_cmdState_1834_, v_pos_1833_, v___x_1987_, v___y_1983_, v_a_1819_);
v___x_1989_ = lean_box(v_val_1818_);
v___x_1990_ = lean_box(v___x_1822_);
lean_inc_ref(v_a_1819_);
lean_inc(v___y_1968_);
lean_inc_ref(v___x_1829_);
lean_inc_ref(v___x_1988_);
lean_inc_ref(v___y_1963_);
lean_inc_ref(v___y_1966_);
v___f_1991_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1991_, 0, v___y_1966_);
lean_closure_set(v___f_1991_, 1, v___y_1963_);
lean_closure_set(v___f_1991_, 2, v___x_1989_);
lean_closure_set(v___f_1991_, 3, v_val_1826_);
lean_closure_set(v___f_1991_, 4, v___x_1988_);
lean_closure_set(v___f_1991_, 5, v___x_1829_);
lean_closure_set(v___f_1991_, 6, v___y_1968_);
lean_closure_set(v___f_1991_, 7, v___x_1990_);
lean_closure_set(v___f_1991_, 8, v_a_1819_);
lean_closure_set(v___f_1991_, 9, v_pos_1833_);
v___x_1992_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1835_, v___x_1836_);
if (v___x_1992_ == 0)
{
lean_dec(v___y_1972_);
lean_inc_ref(v___x_1988_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1966_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1967_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___y_1971_;
v___y_1942_ = v___y_1973_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1975_;
v___y_1945_ = v___f_1991_;
v___y_1946_ = v___x_1988_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1978_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1982_;
v___y_1952_ = v___y_1984_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1985_;
v_reportedCmdState_1955_ = v___x_1988_;
goto v___jp_1932_;
}
else
{
uint8_t v___x_1993_; 
lean_inc(v_fst_1816_);
v___x_1993_ = l_Lean_Parser_isTerminalCommand(v_fst_1816_);
if (v___x_1993_ == 0)
{
if (v___x_1992_ == 0)
{
lean_dec(v___y_1972_);
lean_inc_ref(v___x_1988_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1966_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1967_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___y_1971_;
v___y_1942_ = v___y_1973_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1975_;
v___y_1945_ = v___f_1991_;
v___y_1946_ = v___x_1988_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1978_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1982_;
v___y_1952_ = v___y_1984_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1985_;
v_reportedCmdState_1955_ = v___x_1988_;
goto v___jp_1932_;
}
else
{
lean_object* v_env_1994_; lean_object* v_messages_1995_; lean_object* v_scopes_1996_; lean_object* v_infoState_1997_; lean_object* v_traceState_1998_; lean_object* v_snapshotTasks_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_env_1994_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref_n(v_env_1994_, 2);
v_messages_1995_ = lean_ctor_get(v___x_1988_, 1);
lean_inc_ref(v_messages_1995_);
v_scopes_1996_ = lean_ctor_get(v___x_1988_, 2);
lean_inc(v_scopes_1996_);
v_infoState_1997_ = lean_ctor_get(v___x_1988_, 8);
lean_inc_ref(v_infoState_1997_);
v_traceState_1998_ = lean_ctor_get(v___x_1988_, 9);
lean_inc_ref(v_traceState_1998_);
v_snapshotTasks_1999_ = lean_ctor_get(v___x_1988_, 10);
lean_inc_ref(v_snapshotTasks_1999_);
v___x_2000_ = lean_mk_empty_array_with_capacity(v___y_1972_);
lean_dec(v___y_1972_);
lean_inc_ref(v___x_2000_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_inc_n(v___y_1980_, 3);
v___x_2002_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_2000_);
lean_ctor_set(v___x_2002_, 2, v___y_1980_);
lean_ctor_set(v___x_2002_, 3, v___y_1980_);
lean_ctor_set_usize(v___x_2002_, 4, v___y_1976_);
v___x_2003_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2002_, 2);
v___x_2004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2002_);
lean_ctor_set(v___x_2004_, 2, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2006_ = l_Lean_Options_empty;
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_mk_empty_array_with_capacity(v___y_1980_);
lean_inc_ref_n(v___x_2008_, 2);
lean_inc_n(v___x_1821_, 2);
v___x_2009_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2009_, 0, v___x_2005_);
lean_ctor_set(v___x_2009_, 1, v___x_2006_);
lean_ctor_set(v___x_2009_, 2, v___x_1821_);
lean_ctor_set(v___x_2009_, 3, v___x_2007_);
lean_ctor_set(v___x_2009_, 4, v___x_2007_);
lean_ctor_set(v___x_2009_, 5, v___x_2008_);
lean_ctor_set(v___x_2009_, 6, v___x_2008_);
lean_ctor_set(v___x_2009_, 7, v___x_2007_);
lean_ctor_set(v___x_2009_, 8, v___x_2007_);
lean_ctor_set(v___x_2009_, 9, v___x_2007_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*10, v_val_1818_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*10 + 1, v_val_1818_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*10 + 2, v_val_1818_);
v___x_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v___x_2007_);
v___x_2011_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2012_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2013_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1821_);
v___x_2014_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2015_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
lean_ctor_set(v___x_2015_, 2, v___x_2002_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*3, v___x_1822_);
lean_inc_ref(v___y_1981_);
v___x_2016_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2016_, 0, v_env_1994_);
lean_ctor_set(v___x_2016_, 1, v___x_2004_);
lean_ctor_set(v___x_2016_, 2, v___x_2010_);
lean_ctor_set(v___x_2016_, 3, v___x_2003_);
lean_ctor_set(v___x_2016_, 4, v___x_2011_);
lean_ctor_set(v___x_2016_, 5, v___y_1980_);
lean_ctor_set(v___x_2016_, 6, v___x_2012_);
lean_ctor_set(v___x_2016_, 7, v___x_2013_);
lean_ctor_set(v___x_2016_, 8, v___x_2015_);
lean_ctor_set(v___x_2016_, 9, v___y_1981_);
lean_ctor_set(v___x_2016_, 10, v___x_2008_);
v___y_1870_ = v___y_1963_;
v___y_1871_ = v___y_1964_;
v___y_1872_ = v___y_1965_;
v___y_1873_ = v___y_1966_;
v___y_1874_ = v___y_1967_;
v___y_1875_ = v___y_1968_;
v___y_1876_ = v___y_1969_;
v___y_1877_ = v___y_1970_;
v___y_1878_ = v___y_1971_;
v___y_1879_ = v___y_1973_;
v___y_1880_ = v___y_1974_;
v___y_1881_ = v___y_1975_;
v___y_1882_ = v___f_1991_;
v___y_1883_ = v___x_1988_;
v_env_1884_ = v_env_1994_;
v_messages_1885_ = v_messages_1995_;
v_scopes_1886_ = v_scopes_1996_;
v_infoState_1887_ = v_infoState_1997_;
v_traceState_1888_ = v_traceState_1998_;
v_snapshotTasks_1889_ = v_snapshotTasks_1999_;
v___y_1890_ = v___y_1977_;
v___y_1891_ = v___y_1979_;
v___y_1892_ = v___y_1978_;
v___y_1893_ = v___y_1980_;
v___y_1894_ = v___y_1982_;
v___y_1895_ = v___y_1984_;
v___y_1896_ = v___y_1983_;
v___y_1897_ = v___y_1985_;
v_reportedCmdState_1898_ = v___x_2016_;
goto v___jp_1869_;
}
}
else
{
lean_dec(v___y_1972_);
lean_inc_ref(v___x_1988_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1966_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1967_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___y_1971_;
v___y_1942_ = v___y_1973_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1975_;
v___y_1945_ = v___f_1991_;
v___y_1946_ = v___x_1988_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1978_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1982_;
v___y_1952_ = v___y_1984_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1985_;
v_reportedCmdState_1955_ = v___x_1988_;
goto v___jp_1932_;
}
}
}
v___jp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2019_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1820_);
v___x_2020_ = l_IO_CancelToken_new();
v___x_2021_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1821_);
v___x_2022_ = l_Lean_Name_str___override(v___x_1821_, v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2024_ = l_Lean_Name_str___override(v___x_2022_, v___x_2023_);
v___x_2025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2026_ = l_Lean_Name_str___override(v___x_2024_, v___x_2025_);
v___x_2027_ = l_Lean_Name_str___override(v___x_2026_, v___x_2023_);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = l_Lean_Name_num___override(v___x_2027_, v___x_2028_);
v___x_2030_ = l_Lean_Name_str___override(v___x_2029_, v___x_2023_);
v___x_2031_ = l_Lean_Name_str___override(v___x_2030_, v___x_2025_);
v___x_2032_ = l_Lean_Name_str___override(v___x_2031_, v___x_2023_);
v___x_2033_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2034_ = l_Lean_Name_str___override(v___x_2032_, v___x_2033_);
v___x_2035_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2036_ = l_Lean_Name_str___override(v___x_2034_, v___x_2035_);
v___x_2037_ = l_Lean_Name_toString(v___x_2036_, v___x_1822_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_unsigned_to_nat(32u);
v___x_2040_ = ((size_t)5ULL);
v___x_2041_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2037_, 2);
v___x_2042_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2042_, 0, v___x_2037_);
lean_ctor_set(v___x_2042_, 1, v___x_2019_);
lean_ctor_set(v___x_2042_, 2, v___x_2038_);
lean_ctor_set(v___x_2042_, 3, v___x_2041_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*4, v_val_1818_);
v___x_2043_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2044_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2044_, 0, v___x_2037_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_ctor_set(v___x_2044_, 2, v___x_2038_);
lean_ctor_set(v___x_2044_, 3, v___x_2041_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*4, v_val_1818_);
lean_inc(v_fst_1823_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_fst_1823_);
v___x_2046_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2045_);
lean_inc_ref(v___x_2020_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2020_);
v___x_2048_ = l_IO_Promise_result_x21___redArg(v_val_1824_);
lean_inc_ref(v___x_2048_);
lean_inc(v___x_2046_);
lean_inc_ref_n(v___x_2045_, 3);
v___x_2049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2045_);
lean_ctor_set(v___x_2049_, 1, v___x_2046_);
lean_ctor_set(v___x_2049_, 2, v___x_2047_);
lean_ctor_set(v___x_2049_, 3, v___x_2048_);
v___x_2050_ = l_IO_Promise_result_x21___redArg(v_val_1825_);
lean_inc_ref(v___x_2050_);
lean_inc_n(v___x_1813_, 3);
v___x_2051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2045_);
lean_ctor_set(v___x_2051_, 1, v___x_1813_);
lean_ctor_set(v___x_2051_, 2, v___x_2038_);
lean_ctor_set(v___x_2051_, 3, v___x_2050_);
v___x_2052_ = l_IO_Promise_result_x21___redArg(v_val_1826_);
lean_inc_ref(v___x_2052_);
v___x_2053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2045_);
lean_ctor_set(v___x_2053_, 1, v___x_1813_);
lean_ctor_set(v___x_2053_, 2, v___x_2038_);
lean_ctor_set(v___x_2053_, 3, v___x_2052_);
v___x_2054_ = l_IO_Promise_result_x21___redArg(v_val_1814_);
v___x_2055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2038_);
lean_ctor_set(v___x_2055_, 1, v___x_1813_);
lean_ctor_set(v___x_2055_, 2, v___x_2038_);
lean_ctor_set(v___x_2055_, 3, v___x_2054_);
lean_inc_ref(v___x_2044_);
v___x_2056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2044_);
lean_ctor_set(v___x_2056_, 1, v___x_2049_);
lean_ctor_set(v___x_2056_, 2, v___x_2051_);
lean_ctor_set(v___x_2056_, 3, v___x_2053_);
lean_ctor_set(v___x_2056_, 4, v___x_2055_);
v___x_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2042_);
lean_ctor_set(v___x_2057_, 1, v_fst_1823_);
lean_ctor_set(v___x_2057_, 2, v_snd_1827_);
lean_ctor_set(v___x_2057_, 3, v___x_2056_);
lean_ctor_set(v___x_2057_, 4, v___y_2018_);
v___x_2058_ = lean_io_promise_resolve(v___x_2057_, v_prom_1828_);
if (lean_obj_tag(v_old_x3f_1837_) == 0)
{
lean_inc_ref(v___x_2037_);
lean_inc_ref(v___x_2044_);
v___y_1963_ = v___x_2041_;
v___y_1964_ = v___x_2044_;
v___y_1965_ = v___x_2038_;
v___y_1966_ = v___x_2037_;
v___y_1967_ = v___x_2040_;
v___y_1968_ = v___x_2028_;
v___y_1969_ = v___x_2039_;
v___y_1970_ = v___x_2038_;
v___y_1971_ = v___x_2038_;
v___y_1972_ = v___x_2039_;
v___y_1973_ = v___x_2046_;
v___y_1974_ = v___x_2052_;
v___y_1975_ = v___x_2050_;
v___y_1976_ = v___x_2040_;
v___y_1977_ = v___x_2038_;
v___y_1978_ = v___x_2044_;
v___y_1979_ = v___x_2038_;
v___y_1980_ = v___x_2028_;
v___y_1981_ = v___x_2041_;
v___y_1982_ = v___x_2048_;
v___y_1983_ = v___x_2020_;
v___y_1984_ = v___x_2037_;
v___y_1985_ = v___x_2045_;
v___y_1986_ = v___x_2038_;
goto v___jp_1962_;
}
else
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2070_; 
v_val_2059_ = lean_ctor_get(v_old_x3f_1837_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_old_x3f_1837_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2061_ = v_old_x3f_1837_;
v_isShared_2062_ = v_isSharedCheck_2070_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v_old_x3f_1837_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2070_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_elabSnap_2063_; lean_object* v_stx_2064_; lean_object* v_elabSnap_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v_elabSnap_2063_ = lean_ctor_get(v_val_2059_, 3);
lean_inc_ref(v_elabSnap_2063_);
v_stx_2064_ = lean_ctor_get(v_val_2059_, 1);
lean_inc(v_stx_2064_);
lean_dec(v_val_2059_);
v_elabSnap_2065_ = lean_ctor_get(v_elabSnap_2063_, 1);
lean_inc_ref(v_elabSnap_2065_);
lean_dec_ref(v_elabSnap_2063_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_stx_2064_);
lean_ctor_set(v___x_2066_, 1, v_elabSnap_2065_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2066_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_inc_ref(v___x_2037_);
lean_inc_ref(v___x_2044_);
v___y_1963_ = v___x_2041_;
v___y_1964_ = v___x_2044_;
v___y_1965_ = v___x_2038_;
v___y_1966_ = v___x_2037_;
v___y_1967_ = v___x_2040_;
v___y_1968_ = v___x_2028_;
v___y_1969_ = v___x_2039_;
v___y_1970_ = v___x_2038_;
v___y_1971_ = v___x_2038_;
v___y_1972_ = v___x_2039_;
v___y_1973_ = v___x_2046_;
v___y_1974_ = v___x_2052_;
v___y_1975_ = v___x_2050_;
v___y_1976_ = v___x_2040_;
v___y_1977_ = v___x_2038_;
v___y_1978_ = v___x_2044_;
v___y_1979_ = v___x_2038_;
v___y_1980_ = v___x_2028_;
v___y_1981_ = v___x_2041_;
v___y_1982_ = v___x_2048_;
v___y_1983_ = v___x_2020_;
v___y_1984_ = v___x_2037_;
v___y_1985_ = v___x_2045_;
v___y_1986_ = v___x_2068_;
goto v___jp_1962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_cmds_2083_, lean_object* v_fst_2084_, lean_object* v_fst_2085_, uint8_t v_val_2086_, lean_object* v_a_2087_, lean_object* v_snd_2088_, lean_object* v___x_2089_, uint8_t v___x_2090_, lean_object* v_prom_2091_, lean_object* v___x_2092_, lean_object* v___f_2093_, lean_object* v___f_2094_, lean_object* v___f_2095_, lean_object* v_pos_2096_, lean_object* v_cmdState_2097_, lean_object* v_opts_2098_, lean_object* v_old_x3f_2099_, lean_object* v_parseCancelTk_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v_snapshotTasks_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v_traceTask_2115_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; size_t v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v_env_2159_; lean_object* v_messages_2160_; lean_object* v_scopes_2161_; lean_object* v_infoState_2162_; lean_object* v_traceState_2163_; lean_object* v_snapshotTasks_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v_reportedCmdState_2169_; size_t v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v_reportedCmdState_2228_; lean_object* v___x_2235_; size_t v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; size_t v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v_fst_2372_; lean_object* v_snd_2373_; uint8_t v___y_2386_; uint8_t v___x_2389_; 
v___x_2102_ = lean_io_promise_new();
v___x_2103_ = lean_io_promise_new();
v___x_2104_ = lean_io_promise_new();
v___x_2105_ = lean_io_promise_new();
v___x_2235_ = l_Lean_internal_cmdlineSnapshots;
v___x_2389_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2098_, v___x_2235_);
if (v___x_2389_ == 0)
{
v___y_2386_ = v___x_2389_;
goto v___jp_2385_;
}
else
{
uint8_t v___x_2390_; 
lean_inc(v_fst_2084_);
v___x_2390_ = l_Lean_Parser_isTerminalCommand(v_fst_2084_);
if (v___x_2390_ == 0)
{
v___y_2386_ = v___x_2389_;
goto v___jp_2385_;
}
else
{
lean_inc_ref(v_fst_2085_);
lean_inc(v_fst_2084_);
v_fst_2372_ = v_fst_2084_;
v_snd_2373_ = v_fst_2085_;
goto v___jp_2371_;
}
}
v___jp_2106_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2116_, 0, v___y_2111_);
lean_ctor_set(v___x_2116_, 1, v___y_2113_);
lean_ctor_set(v___x_2116_, 2, v___y_2108_);
lean_ctor_set(v___x_2116_, 3, v_traceTask_2115_);
v___x_2117_ = lean_array_push(v_snapshotTasks_2110_, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___y_2107_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_io_promise_resolve(v___x_2118_, v___x_2105_);
lean_dec(v___x_2105_);
if (lean_obj_tag(v___y_2112_) == 1)
{
lean_object* v_val_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_val_2120_ = lean_ctor_get(v___y_2112_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v___y_2112_, 1);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_array_push(v_cmds_2083_, v_fst_2084_);
v___x_2123_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2121_, v_fst_2085_, v___y_2109_, v_val_2120_, v_val_2086_, v___y_2114_, v___x_2122_, v_a_2087_);
return v___x_2123_;
}
else
{
lean_object* v___x_2124_; 
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2109_);
lean_dec_ref(v_fst_2085_);
lean_dec(v_fst_2084_);
lean_dec_ref(v_cmds_2083_);
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
}
v___jp_2125_:
{
lean_object* v_snapshotTasks_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_snapshotTasks_2134_ = lean_ctor_get(v___y_2127_, 10);
lean_inc_ref(v_snapshotTasks_2134_);
v___x_2135_ = lean_mk_empty_array_with_capacity(v___y_2131_);
lean_dec(v___y_2131_);
lean_inc_ref(v___y_2126_);
v___x_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___y_2126_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = lean_task_pure(v___x_2136_);
v___y_2107_ = v___y_2126_;
v___y_2108_ = v___y_2128_;
v___y_2109_ = v___y_2127_;
v_snapshotTasks_2110_ = v_snapshotTasks_2134_;
v___y_2111_ = v___y_2129_;
v___y_2112_ = v___y_2130_;
v___y_2113_ = v___y_2132_;
v___y_2114_ = v___y_2133_;
v_traceTask_2115_ = v___x_2137_;
goto v___jp_2106_;
}
v___jp_2138_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_opts_2179_; uint8_t v_hasTrace_2180_; 
v___x_2170_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2160_);
v___x_2171_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2171_, 0, v___y_2152_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
lean_ctor_set(v___x_2171_, 2, v___y_2166_);
lean_ctor_set(v___x_2171_, 3, v_traceState_2163_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*4, v_val_2086_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_reportedCmdState_2169_);
v___x_2173_ = lean_io_promise_resolve(v___x_2172_, v___x_2103_);
lean_dec(v___x_2103_);
v___x_2174_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2162_);
lean_inc(v___y_2151_);
v___x_2175_ = l_BaseIO_chainTask___redArg(v___x_2174_, v___y_2153_, v___y_2151_, v___x_2090_);
v___x_2176_ = l_Lean_inheritedTraceOptions;
v___x_2177_ = lean_st_ref_get(v___x_2176_);
v___x_2178_ = l_List_head_x21___redArg(v___x_2092_, v_scopes_2161_);
lean_dec(v_scopes_2161_);
lean_dec_ref(v___x_2092_);
v_opts_2179_ = lean_ctor_get(v___x_2178_, 1);
lean_inc_ref(v_opts_2179_);
lean_dec(v___x_2178_);
v_hasTrace_2180_ = lean_ctor_get_uint8(v_opts_2179_, sizeof(void*)*1);
if (v_hasTrace_2180_ == 0)
{
lean_dec_ref(v_opts_2179_);
lean_dec(v___x_2177_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_snapshotTasks_2164_);
lean_dec_ref(v_env_2159_);
lean_dec(v___y_2156_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec(v_pos_2096_);
lean_dec_ref(v___f_2095_);
lean_dec_ref(v___f_2094_);
lean_dec_ref(v___f_2093_);
lean_dec(v___x_2089_);
v___y_2126_ = v___y_2157_;
v___y_2127_ = v___y_2158_;
v___y_2128_ = v___y_2165_;
v___y_2129_ = v___y_2149_;
v___y_2130_ = v___y_2150_;
v___y_2131_ = v___y_2151_;
v___y_2132_ = v___y_2168_;
v___y_2133_ = v___y_2155_;
goto v___jp_2125_;
}
else
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2182_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2177_, v_opts_2179_, v___x_2181_);
lean_dec(v___x_2177_);
if (v___x_2182_ == 0)
{
lean_dec_ref(v_opts_2179_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_snapshotTasks_2164_);
lean_dec_ref(v_env_2159_);
lean_dec(v___y_2156_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec(v_pos_2096_);
lean_dec_ref(v___f_2095_);
lean_dec_ref(v___f_2094_);
lean_dec_ref(v___f_2093_);
lean_dec(v___x_2089_);
v___y_2126_ = v___y_2157_;
v___y_2127_ = v___y_2158_;
v___y_2128_ = v___y_2165_;
v___y_2129_ = v___y_2149_;
v___y_2130_ = v___y_2150_;
v___y_2131_ = v___y_2151_;
v___y_2132_ = v___y_2168_;
v___y_2133_ = v___y_2155_;
goto v___jp_2125_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; 
lean_inc_n(v___y_2151_, 3);
v___x_2183_ = lean_task_map(v___f_2093_, v___y_2147_, v___y_2151_, v___x_2090_);
lean_inc_n(v___y_2165_, 3);
lean_inc_n(v___y_2156_, 2);
lean_inc_n(v___y_2154_, 2);
v___x_2184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2184_, 0, v___y_2154_);
lean_ctor_set(v___x_2184_, 1, v___y_2156_);
lean_ctor_set(v___x_2184_, 2, v___y_2165_);
lean_ctor_set(v___x_2184_, 3, v___x_2183_);
v___x_2185_ = lean_task_map(v___f_2094_, v___y_2148_, v___y_2151_, v___x_2090_);
v___x_2186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2154_);
lean_ctor_set(v___x_2186_, 1, v___y_2156_);
lean_ctor_set(v___x_2186_, 2, v___y_2165_);
lean_ctor_set(v___x_2186_, 3, v___x_2185_);
v___x_2187_ = lean_task_map(v___f_2095_, v___y_2167_, v___y_2151_, v___x_2090_);
v___x_2188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2188_, 0, v___y_2154_);
lean_ctor_set(v___x_2188_, 1, v___y_2156_);
lean_ctor_set(v___x_2188_, 2, v___y_2165_);
lean_ctor_set(v___x_2188_, 3, v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(3u);
v___x_2190_ = lean_mk_empty_array_with_capacity(v___x_2189_);
v___x_2191_ = lean_array_push(v___x_2190_, v___x_2184_);
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2186_);
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2188_);
v___x_2194_ = l_Array_append___redArg(v___x_2193_, v_snapshotTasks_2164_);
lean_inc_ref(v___y_2157_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___y_2157_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
lean_inc_ref(v___x_2195_);
v___x_2196_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2195_);
v___x_2197_ = lean_box_usize(v___y_2139_);
v___x_2198_ = lean_box(v___x_2090_);
v___x_2199_ = lean_box(v_val_2086_);
v___x_2200_ = lean_box(v___x_2182_);
lean_inc_ref(v_a_2087_);
lean_inc_ref(v___y_2145_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2201_, 0, v___x_2089_);
lean_closure_set(v___f_2201_, 1, v___y_2141_);
lean_closure_set(v___f_2201_, 2, v___y_2146_);
lean_closure_set(v___f_2201_, 3, v___x_2197_);
lean_closure_set(v___f_2201_, 4, v___x_2198_);
lean_closure_set(v___f_2201_, 5, v_env_2159_);
lean_closure_set(v___f_2201_, 6, v___y_2145_);
lean_closure_set(v___f_2201_, 7, v___x_2176_);
lean_closure_set(v___f_2201_, 8, v_a_2087_);
lean_closure_set(v___f_2201_, 9, v_opts_2179_);
lean_closure_set(v___f_2201_, 10, v___x_2195_);
lean_closure_set(v___f_2201_, 11, v_pos_2096_);
lean_closure_set(v___f_2201_, 12, v___x_2199_);
lean_closure_set(v___f_2201_, 13, v___y_2142_);
lean_closure_set(v___f_2201_, 14, v___y_2144_);
lean_closure_set(v___f_2201_, 15, v___y_2143_);
lean_closure_set(v___f_2201_, 16, v___y_2140_);
lean_closure_set(v___f_2201_, 17, v___x_2200_);
v___x_2202_ = lean_io_bind_task(v___x_2196_, v___f_2201_, v___y_2151_, v_val_2086_);
v___y_2107_ = v___y_2157_;
v___y_2108_ = v___y_2165_;
v___y_2109_ = v___y_2158_;
v_snapshotTasks_2110_ = v_snapshotTasks_2164_;
v___y_2111_ = v___y_2149_;
v___y_2112_ = v___y_2150_;
v___y_2113_ = v___y_2168_;
v___y_2114_ = v___y_2155_;
v_traceTask_2115_ = v___x_2202_;
goto v___jp_2106_;
}
}
}
v___jp_2203_:
{
lean_object* v_env_2229_; lean_object* v_messages_2230_; lean_object* v_scopes_2231_; lean_object* v_infoState_2232_; lean_object* v_traceState_2233_; lean_object* v_snapshotTasks_2234_; 
v_env_2229_ = lean_ctor_get(v___y_2223_, 0);
lean_inc_ref(v_env_2229_);
v_messages_2230_ = lean_ctor_get(v___y_2223_, 1);
lean_inc_ref(v_messages_2230_);
v_scopes_2231_ = lean_ctor_get(v___y_2223_, 2);
lean_inc(v_scopes_2231_);
v_infoState_2232_ = lean_ctor_get(v___y_2223_, 8);
lean_inc_ref(v_infoState_2232_);
v_traceState_2233_ = lean_ctor_get(v___y_2223_, 9);
lean_inc_ref(v_traceState_2233_);
v_snapshotTasks_2234_ = lean_ctor_get(v___y_2223_, 10);
lean_inc_ref(v_snapshotTasks_2234_);
v___y_2139_ = v___y_2204_;
v___y_2140_ = v___y_2205_;
v___y_2141_ = v___y_2206_;
v___y_2142_ = v___y_2207_;
v___y_2143_ = v___y_2209_;
v___y_2144_ = v___y_2208_;
v___y_2145_ = v___y_2210_;
v___y_2146_ = v___y_2211_;
v___y_2147_ = v___y_2212_;
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
v_env_2159_ = v_env_2229_;
v_messages_2160_ = v_messages_2230_;
v_scopes_2161_ = v_scopes_2231_;
v_infoState_2162_ = v_infoState_2232_;
v_traceState_2163_ = v_traceState_2233_;
v_snapshotTasks_2164_ = v_snapshotTasks_2234_;
v___y_2165_ = v___y_2224_;
v___y_2166_ = v___y_2225_;
v___y_2167_ = v___y_2226_;
v___y_2168_ = v___y_2227_;
v_reportedCmdState_2169_ = v_reportedCmdState_2228_;
goto v___jp_2138_;
}
v___jp_2236_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___f_2267_; uint8_t v___x_2268_; 
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___y_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2102_);
lean_inc_ref(v___y_2254_);
lean_inc_n(v_pos_2096_, 2);
lean_inc_ref(v_cmds_2083_);
lean_inc(v_fst_2084_);
v___x_2264_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2084_, v_cmds_2083_, v_cmdState_2097_, v_pos_2096_, v___x_2263_, v___y_2254_, v_a_2087_);
v___x_2265_ = lean_box(v_val_2086_);
v___x_2266_ = lean_box(v___x_2090_);
lean_inc_ref(v_a_2087_);
lean_inc(v___y_2244_);
lean_inc_ref(v___x_2092_);
lean_inc_ref(v___x_2264_);
lean_inc_ref(v___y_2243_);
lean_inc_ref(v___y_2240_);
v___f_2267_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2267_, 0, v___y_2240_);
lean_closure_set(v___f_2267_, 1, v___y_2243_);
lean_closure_set(v___f_2267_, 2, v___x_2265_);
lean_closure_set(v___f_2267_, 3, v___x_2104_);
lean_closure_set(v___f_2267_, 4, v___x_2264_);
lean_closure_set(v___f_2267_, 5, v___x_2092_);
lean_closure_set(v___f_2267_, 6, v___y_2244_);
lean_closure_set(v___f_2267_, 7, v___x_2266_);
lean_closure_set(v___f_2267_, 8, v_a_2087_);
lean_closure_set(v___f_2267_, 9, v_pos_2096_);
v___x_2268_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2098_, v___x_2235_);
if (v___x_2268_ == 0)
{
lean_dec(v___y_2260_);
lean_inc_ref(v___x_2264_);
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___y_2242_;
v___y_2209_ = v___y_2241_;
v___y_2210_ = v___y_2243_;
v___y_2211_ = v___y_2244_;
v___y_2212_ = v___y_2245_;
v___y_2213_ = v___y_2247_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___f_2267_;
v___y_2219_ = v___y_2253_;
v___y_2220_ = v___y_2254_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___x_2264_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2261_;
v_reportedCmdState_2228_ = v___x_2264_;
goto v___jp_2203_;
}
else
{
uint8_t v___x_2269_; 
lean_inc(v_fst_2084_);
v___x_2269_ = l_Lean_Parser_isTerminalCommand(v_fst_2084_);
if (v___x_2269_ == 0)
{
if (v___x_2268_ == 0)
{
lean_dec(v___y_2260_);
lean_inc_ref(v___x_2264_);
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___y_2242_;
v___y_2209_ = v___y_2241_;
v___y_2210_ = v___y_2243_;
v___y_2211_ = v___y_2244_;
v___y_2212_ = v___y_2245_;
v___y_2213_ = v___y_2247_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___f_2267_;
v___y_2219_ = v___y_2253_;
v___y_2220_ = v___y_2254_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___x_2264_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2261_;
v_reportedCmdState_2228_ = v___x_2264_;
goto v___jp_2203_;
}
else
{
lean_object* v_env_2270_; lean_object* v_messages_2271_; lean_object* v_scopes_2272_; lean_object* v_infoState_2273_; lean_object* v_traceState_2274_; lean_object* v_snapshotTasks_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_env_2270_ = lean_ctor_get(v___x_2264_, 0);
lean_inc_ref_n(v_env_2270_, 2);
v_messages_2271_ = lean_ctor_get(v___x_2264_, 1);
lean_inc_ref(v_messages_2271_);
v_scopes_2272_ = lean_ctor_get(v___x_2264_, 2);
lean_inc(v_scopes_2272_);
v_infoState_2273_ = lean_ctor_get(v___x_2264_, 8);
lean_inc_ref(v_infoState_2273_);
v_traceState_2274_ = lean_ctor_get(v___x_2264_, 9);
lean_inc_ref(v_traceState_2274_);
v_snapshotTasks_2275_ = lean_ctor_get(v___x_2264_, 10);
lean_inc_ref(v_snapshotTasks_2275_);
v___x_2276_ = lean_mk_empty_array_with_capacity(v___y_2260_);
lean_dec(v___y_2260_);
lean_inc_ref(v___x_2276_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_inc_n(v___y_2249_, 3);
v___x_2278_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___y_2249_);
lean_ctor_set(v___x_2278_, 3, v___y_2249_);
lean_ctor_set_usize(v___x_2278_, 4, v___y_2252_);
v___x_2279_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2278_, 2);
v___x_2280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2278_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2282_ = l_Lean_Options_empty;
v___x_2283_ = lean_box(0);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___y_2249_);
lean_inc_ref_n(v___x_2284_, 2);
lean_inc_n(v___x_2089_, 2);
v___x_2285_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2285_, 0, v___x_2281_);
lean_ctor_set(v___x_2285_, 1, v___x_2282_);
lean_ctor_set(v___x_2285_, 2, v___x_2089_);
lean_ctor_set(v___x_2285_, 3, v___x_2283_);
lean_ctor_set(v___x_2285_, 4, v___x_2283_);
lean_ctor_set(v___x_2285_, 5, v___x_2284_);
lean_ctor_set(v___x_2285_, 6, v___x_2284_);
lean_ctor_set(v___x_2285_, 7, v___x_2283_);
lean_ctor_set(v___x_2285_, 8, v___x_2283_);
lean_ctor_set(v___x_2285_, 9, v___x_2283_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*10, v_val_2086_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*10 + 1, v_val_2086_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*10 + 2, v_val_2086_);
v___x_2286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2283_);
v___x_2287_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2288_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2289_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2089_);
v___x_2290_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2291_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
lean_ctor_set(v___x_2291_, 2, v___x_2278_);
lean_ctor_set_uint8(v___x_2291_, sizeof(void*)*3, v___x_2090_);
lean_inc_ref(v___y_2251_);
v___x_2292_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2292_, 0, v_env_2270_);
lean_ctor_set(v___x_2292_, 1, v___x_2280_);
lean_ctor_set(v___x_2292_, 2, v___x_2286_);
lean_ctor_set(v___x_2292_, 3, v___x_2279_);
lean_ctor_set(v___x_2292_, 4, v___x_2287_);
lean_ctor_set(v___x_2292_, 5, v___y_2249_);
lean_ctor_set(v___x_2292_, 6, v___x_2288_);
lean_ctor_set(v___x_2292_, 7, v___x_2289_);
lean_ctor_set(v___x_2292_, 8, v___x_2291_);
lean_ctor_set(v___x_2292_, 9, v___y_2251_);
lean_ctor_set(v___x_2292_, 10, v___x_2284_);
v___y_2139_ = v___y_2237_;
v___y_2140_ = v___y_2238_;
v___y_2141_ = v___y_2239_;
v___y_2142_ = v___y_2240_;
v___y_2143_ = v___y_2241_;
v___y_2144_ = v___y_2242_;
v___y_2145_ = v___y_2243_;
v___y_2146_ = v___y_2244_;
v___y_2147_ = v___y_2245_;
v___y_2148_ = v___y_2247_;
v___y_2149_ = v___y_2246_;
v___y_2150_ = v___y_2248_;
v___y_2151_ = v___y_2249_;
v___y_2152_ = v___y_2250_;
v___y_2153_ = v___f_2267_;
v___y_2154_ = v___y_2253_;
v___y_2155_ = v___y_2254_;
v___y_2156_ = v___y_2255_;
v___y_2157_ = v___y_2256_;
v___y_2158_ = v___x_2264_;
v_env_2159_ = v_env_2270_;
v_messages_2160_ = v_messages_2271_;
v_scopes_2161_ = v_scopes_2272_;
v_infoState_2162_ = v_infoState_2273_;
v_traceState_2163_ = v_traceState_2274_;
v_snapshotTasks_2164_ = v_snapshotTasks_2275_;
v___y_2165_ = v___y_2257_;
v___y_2166_ = v___y_2258_;
v___y_2167_ = v___y_2259_;
v___y_2168_ = v___y_2261_;
v_reportedCmdState_2169_ = v___x_2292_;
goto v___jp_2138_;
}
}
else
{
lean_dec(v___y_2260_);
lean_inc_ref(v___x_2264_);
v___y_2204_ = v___y_2237_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2240_;
v___y_2208_ = v___y_2242_;
v___y_2209_ = v___y_2241_;
v___y_2210_ = v___y_2243_;
v___y_2211_ = v___y_2244_;
v___y_2212_ = v___y_2245_;
v___y_2213_ = v___y_2247_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___f_2267_;
v___y_2219_ = v___y_2253_;
v___y_2220_ = v___y_2254_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___x_2264_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2261_;
v_reportedCmdState_2228_ = v___x_2264_;
goto v___jp_2203_;
}
}
}
v___jp_2293_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; size_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2299_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2088_);
v___x_2300_ = l_IO_CancelToken_new();
v___x_2301_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2089_);
v___x_2302_ = l_Lean_Name_str___override(v___x_2089_, v___x_2301_);
v___x_2303_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2304_ = l_Lean_Name_str___override(v___x_2302_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2306_ = l_Lean_Name_str___override(v___x_2304_, v___x_2305_);
v___x_2307_ = l_Lean_Name_str___override(v___x_2306_, v___x_2303_);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = l_Lean_Name_num___override(v___x_2307_, v___x_2308_);
v___x_2310_ = l_Lean_Name_str___override(v___x_2309_, v___x_2303_);
v___x_2311_ = l_Lean_Name_str___override(v___x_2310_, v___x_2305_);
v___x_2312_ = l_Lean_Name_str___override(v___x_2311_, v___x_2303_);
v___x_2313_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2314_ = l_Lean_Name_str___override(v___x_2312_, v___x_2313_);
v___x_2315_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2316_ = l_Lean_Name_str___override(v___x_2314_, v___x_2315_);
v___x_2317_ = l_Lean_Name_toString(v___x_2316_, v___x_2090_);
v___x_2318_ = lean_box(0);
v___x_2319_ = lean_unsigned_to_nat(32u);
v___x_2320_ = lean_mk_empty_array_with_capacity(v___x_2319_);
lean_dec_ref(v___x_2320_);
v___x_2321_ = ((size_t)5ULL);
v___x_2322_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2317_, 2);
v___x_2323_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2317_);
lean_ctor_set(v___x_2323_, 1, v___x_2299_);
lean_ctor_set(v___x_2323_, 2, v___x_2318_);
lean_ctor_set(v___x_2323_, 3, v___x_2322_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*4, v_val_2086_);
v___x_2324_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2325_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2325_, 0, v___x_2317_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
lean_ctor_set(v___x_2325_, 2, v___x_2318_);
lean_ctor_set(v___x_2325_, 3, v___x_2322_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*4, v_val_2086_);
lean_inc(v___y_2295_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___y_2295_);
v___x_2327_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2326_);
lean_inc_ref(v___x_2300_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2300_);
v___x_2329_ = l_IO_Promise_result_x21___redArg(v___x_2102_);
lean_inc_ref(v___x_2329_);
lean_inc(v___x_2327_);
lean_inc_ref_n(v___x_2326_, 3);
v___x_2330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2326_);
lean_ctor_set(v___x_2330_, 1, v___x_2327_);
lean_ctor_set(v___x_2330_, 2, v___x_2328_);
lean_ctor_set(v___x_2330_, 3, v___x_2329_);
v___x_2331_ = l_IO_Promise_result_x21___redArg(v___x_2103_);
lean_inc_ref(v___x_2331_);
lean_inc_n(v___y_2297_, 3);
v___x_2332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2326_);
lean_ctor_set(v___x_2332_, 1, v___y_2297_);
lean_ctor_set(v___x_2332_, 2, v___x_2318_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
v___x_2333_ = l_IO_Promise_result_x21___redArg(v___x_2104_);
lean_inc_ref(v___x_2333_);
v___x_2334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2326_);
lean_ctor_set(v___x_2334_, 1, v___y_2297_);
lean_ctor_set(v___x_2334_, 2, v___x_2318_);
lean_ctor_set(v___x_2334_, 3, v___x_2333_);
v___x_2335_ = l_IO_Promise_result_x21___redArg(v___x_2105_);
v___x_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2318_);
lean_ctor_set(v___x_2336_, 1, v___y_2297_);
lean_ctor_set(v___x_2336_, 2, v___x_2318_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
lean_inc_ref(v___x_2325_);
v___x_2337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2325_);
lean_ctor_set(v___x_2337_, 1, v___x_2330_);
lean_ctor_set(v___x_2337_, 2, v___x_2332_);
lean_ctor_set(v___x_2337_, 3, v___x_2334_);
lean_ctor_set(v___x_2337_, 4, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2323_);
lean_ctor_set(v___x_2338_, 1, v___y_2295_);
lean_ctor_set(v___x_2338_, 2, v___y_2296_);
lean_ctor_set(v___x_2338_, 3, v___x_2337_);
lean_ctor_set(v___x_2338_, 4, v___y_2298_);
v___x_2339_ = lean_io_promise_resolve(v___x_2338_, v_prom_2091_);
if (lean_obj_tag(v_old_x3f_2099_) == 0)
{
lean_inc_ref(v___x_2325_);
lean_inc_ref(v___x_2317_);
v___y_2237_ = v___x_2321_;
v___y_2238_ = v___x_2318_;
v___y_2239_ = v___x_2319_;
v___y_2240_ = v___x_2317_;
v___y_2241_ = v___x_2325_;
v___y_2242_ = v___x_2318_;
v___y_2243_ = v___x_2322_;
v___y_2244_ = v___x_2308_;
v___y_2245_ = v___x_2329_;
v___y_2246_ = v___x_2318_;
v___y_2247_ = v___x_2331_;
v___y_2248_ = v___y_2294_;
v___y_2249_ = v___x_2308_;
v___y_2250_ = v___x_2317_;
v___y_2251_ = v___x_2322_;
v___y_2252_ = v___x_2321_;
v___y_2253_ = v___x_2326_;
v___y_2254_ = v___x_2300_;
v___y_2255_ = v___x_2327_;
v___y_2256_ = v___x_2325_;
v___y_2257_ = v___x_2318_;
v___y_2258_ = v___x_2318_;
v___y_2259_ = v___x_2333_;
v___y_2260_ = v___x_2319_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___x_2318_;
goto v___jp_2236_;
}
else
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2351_; 
v_val_2340_ = lean_ctor_get(v_old_x3f_2099_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_old_x3f_2099_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2342_ = v_old_x3f_2099_;
v_isShared_2343_ = v_isSharedCheck_2351_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v_old_x3f_2099_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2351_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_elabSnap_2344_; lean_object* v_stx_2345_; lean_object* v_elabSnap_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v_elabSnap_2344_ = lean_ctor_get(v_val_2340_, 3);
lean_inc_ref(v_elabSnap_2344_);
v_stx_2345_ = lean_ctor_get(v_val_2340_, 1);
lean_inc(v_stx_2345_);
lean_dec(v_val_2340_);
v_elabSnap_2346_ = lean_ctor_get(v_elabSnap_2344_, 1);
lean_inc_ref(v_elabSnap_2346_);
lean_dec_ref(v_elabSnap_2344_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_stx_2345_);
lean_ctor_set(v___x_2347_, 1, v_elabSnap_2346_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2347_);
v___x_2349_ = v___x_2342_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_inc_ref(v___x_2325_);
lean_inc_ref(v___x_2317_);
v___y_2237_ = v___x_2321_;
v___y_2238_ = v___x_2318_;
v___y_2239_ = v___x_2319_;
v___y_2240_ = v___x_2317_;
v___y_2241_ = v___x_2325_;
v___y_2242_ = v___x_2318_;
v___y_2243_ = v___x_2322_;
v___y_2244_ = v___x_2308_;
v___y_2245_ = v___x_2329_;
v___y_2246_ = v___x_2318_;
v___y_2247_ = v___x_2331_;
v___y_2248_ = v___y_2294_;
v___y_2249_ = v___x_2308_;
v___y_2250_ = v___x_2317_;
v___y_2251_ = v___x_2322_;
v___y_2252_ = v___x_2321_;
v___y_2253_ = v___x_2326_;
v___y_2254_ = v___x_2300_;
v___y_2255_ = v___x_2327_;
v___y_2256_ = v___x_2325_;
v___y_2257_ = v___x_2318_;
v___y_2258_ = v___x_2318_;
v___y_2259_ = v___x_2333_;
v___y_2260_ = v___x_2319_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___x_2349_;
goto v___jp_2236_;
}
}
}
}
v___jp_2352_:
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2355_);
lean_inc(v_fst_2084_);
v___x_2357_ = l_Lean_Parser_isTerminalCommand(v_fst_2084_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v_toProcessingContext_2359_; lean_object* v_pos_2360_; lean_object* v_endPos_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2358_ = lean_io_promise_new();
v_toProcessingContext_2359_ = lean_ctor_get(v_a_2087_, 0);
v_pos_2360_ = lean_ctor_get(v_fst_2085_, 0);
v_endPos_2361_ = lean_ctor_get(v_toProcessingContext_2359_, 3);
lean_inc(v___x_2358_);
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2358_);
v___x_2363_ = lean_box(0);
lean_inc(v_endPos_2361_);
lean_inc(v_pos_2360_);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_pos_2360_);
lean_ctor_set(v___x_2364_, 1, v_endPos_2361_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v_parseCancelTk_2100_);
v___x_2367_ = l_IO_Promise_result_x21___redArg(v___x_2358_);
lean_dec(v___x_2358_);
v___x_2368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2363_);
lean_ctor_set(v___x_2368_, 1, v___x_2365_);
lean_ctor_set(v___x_2368_, 2, v___x_2366_);
lean_ctor_set(v___x_2368_, 3, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
v___y_2294_ = v___x_2362_;
v___y_2295_ = v___y_2353_;
v___y_2296_ = v___y_2354_;
v___y_2297_ = v___x_2356_;
v___y_2298_ = v___x_2369_;
goto v___jp_2293_;
}
else
{
lean_object* v___x_2370_; 
lean_dec_ref(v_parseCancelTk_2100_);
v___x_2370_ = lean_box(0);
v___y_2294_ = v___x_2370_;
v___y_2295_ = v___y_2353_;
v___y_2296_ = v___y_2354_;
v___y_2297_ = v___x_2356_;
v___y_2298_ = v___x_2370_;
goto v___jp_2293_;
}
}
v___jp_2371_:
{
lean_object* v___x_2374_; 
lean_inc(v_fst_2084_);
v___x_2374_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2084_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_box(0);
v___y_2353_ = v_fst_2372_;
v___y_2354_ = v_snd_2373_;
v___y_2355_ = v___x_2375_;
goto v___jp_2352_;
}
else
{
lean_object* v_val_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2384_; 
v_val_2376_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2378_ = v___x_2374_;
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_val_2376_);
lean_dec(v___x_2374_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
lean_inc(v_val_2376_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_val_2376_);
lean_ctor_set(v___x_2380_, 1, v_val_2376_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
v___y_2353_ = v_fst_2372_;
v___y_2354_ = v_snd_2373_;
v___y_2355_ = v___x_2382_;
goto v___jp_2352_;
}
}
}
}
v___jp_2385_:
{
if (v___y_2386_ == 0)
{
lean_inc_ref(v_fst_2085_);
lean_inc(v_fst_2084_);
v_fst_2372_ = v_fst_2084_;
v_snd_2373_ = v_fst_2085_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2372_ = v___x_2387_;
v_snd_2373_ = v___x_2388_;
goto v___jp_2371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_cmds_2391_ = _args[0];
lean_object* v_fst_2392_ = _args[1];
lean_object* v_fst_2393_ = _args[2];
lean_object* v_val_2394_ = _args[3];
lean_object* v_a_2395_ = _args[4];
lean_object* v_snd_2396_ = _args[5];
lean_object* v___x_2397_ = _args[6];
lean_object* v___x_2398_ = _args[7];
lean_object* v_prom_2399_ = _args[8];
lean_object* v___x_2400_ = _args[9];
lean_object* v___f_2401_ = _args[10];
lean_object* v___f_2402_ = _args[11];
lean_object* v___f_2403_ = _args[12];
lean_object* v_pos_2404_ = _args[13];
lean_object* v_cmdState_2405_ = _args[14];
lean_object* v_opts_2406_ = _args[15];
lean_object* v_old_x3f_2407_ = _args[16];
lean_object* v_parseCancelTk_2408_ = _args[17];
lean_object* v___y_2409_ = _args[18];
_start:
{
uint8_t v_val_45790__boxed_2410_; uint8_t v___x_45793__boxed_2411_; lean_object* v_res_2412_; 
v_val_45790__boxed_2410_ = lean_unbox(v_val_2394_);
v___x_45793__boxed_2411_ = lean_unbox(v___x_2398_);
v_res_2412_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_cmds_2391_, v_fst_2392_, v_fst_2393_, v_val_45790__boxed_2410_, v_a_2395_, v_snd_2396_, v___x_2397_, v___x_45793__boxed_2411_, v_prom_2399_, v___x_2400_, v___f_2401_, v___f_2402_, v___f_2403_, v_pos_2404_, v_cmdState_2405_, v_opts_2406_, v_old_x3f_2407_, v_parseCancelTk_2408_);
lean_dec_ref(v_opts_2406_);
lean_dec(v_prom_2399_);
lean_dec_ref(v_a_2395_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2415_, lean_object* v_parserState_2416_, lean_object* v_cmdState_2417_, lean_object* v_prom_2418_, uint8_t v_sync_2419_, lean_object* v_parseCancelTk_2420_, lean_object* v_cmds_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_toSnapshot_2425_; lean_object* v_stx_2426_; lean_object* v_parserState_2427_; lean_object* v_elabSnap_2428_; lean_object* v_val_2429_; lean_object* v_newParserState_2430_; lean_object* v___y_2464_; uint8_t v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2502_; uint8_t v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; uint8_t v___y_2515_; lean_object* v___y_2516_; uint8_t v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2539_; lean_object* v___y_2540_; uint8_t v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2568_; uint8_t v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; uint8_t v___y_2579_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; 
v___f_2506_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2507_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2508_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2509_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2415_) == 1)
{
lean_object* v_val_2654_; lean_object* v_nextCmdSnap_x3f_2655_; 
v_val_2654_ = lean_ctor_get(v_old_x3f_2415_, 0);
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
lean_dec_ref_known(v___x_2661_, 1);
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
lean_dec_ref_known(v_nextCmdSnap_x3f_2663_, 1);
v___x_2665_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2664_);
if (lean_obj_tag(v___x_2665_) == 1)
{
lean_object* v_val_2666_; lean_object* v_parserState_2667_; lean_object* v_pos_2668_; uint8_t v___x_2669_; 
v_val_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v___x_2665_, 1);
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
lean_dec_ref_known(v_old_x3f_2415_, 1);
lean_dec_ref(v_parseCancelTk_2420_);
lean_dec_ref(v_cmdState_2417_);
lean_dec_ref(v_parserState_2416_);
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
v___x_2438_ = lean_box(v_sync_2419_);
lean_inc_ref(v_a_2422_);
lean_inc_ref(v___x_2432_);
lean_inc(v___x_2431_);
lean_inc_ref(v_newParserState_2430_);
lean_inc(v_stx_2426_);
v___f_2439_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2439_, 0, v_val_2429_);
lean_closure_set(v___f_2439_, 1, v_cmds_2421_);
lean_closure_set(v___f_2439_, 2, v_stx_2426_);
lean_closure_set(v___f_2439_, 3, v_newParserState_2430_);
lean_closure_set(v___f_2439_, 4, v___x_2431_);
lean_closure_set(v___f_2439_, 5, v___x_2438_);
lean_closure_set(v___f_2439_, 6, v___x_2432_);
lean_closure_set(v___f_2439_, 7, v_a_2422_);
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
v___x_2455_ = lean_io_promise_resolve(v___x_2454_, v_prom_2418_);
lean_dec(v_prom_2418_);
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
v___x_2485_ = l_Lean_Name_toString(v___x_2484_, v___y_2466_);
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
lean_ctor_set(v___x_2493_, 1, v_cmdState_2417_);
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
lean_ctor_set(v___x_2498_, 2, v___y_2468_);
lean_ctor_set(v___x_2498_, 3, v___x_2497_);
lean_ctor_set(v___x_2498_, 4, v___x_2487_);
v___x_2499_ = lean_io_promise_resolve(v___x_2498_, v_prom_2418_);
lean_dec(v_prom_2418_);
v___x_2500_ = lean_box(0);
return v___x_2500_;
}
v___jp_2501_:
{
v___y_2466_ = v___y_2503_;
v___y_2467_ = v___y_2502_;
v___y_2468_ = v___y_2504_;
goto v___jp_2465_;
}
v___jp_2510_:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2527_);
v___x_2529_ = l_Lean_Parser_isTerminalCommand(v___y_2512_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_io_promise_new();
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
v___x_2532_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2528_, v___y_2514_, v_cmds_2421_, v___y_2513_, v___y_2524_, v___y_2517_, v_a_2422_, v___y_2520_, v___y_2522_, v___y_2515_, v___y_2526_, v___y_2523_, v___y_2511_, v___y_2519_, v___y_2521_, v_prom_2418_, v___x_2509_, v___f_2508_, v___f_2507_, v___f_2506_, v___y_2518_, v_cmdState_2417_, v___y_2516_, v___y_2525_, v_old_x3f_2415_, v_parseCancelTk_2420_, v___x_2531_);
lean_dec_ref(v___y_2516_);
lean_dec(v_prom_2418_);
lean_dec(v___y_2511_);
lean_dec(v___y_2514_);
v___y_2464_ = v___x_2532_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2528_, v___y_2514_, v_cmds_2421_, v___y_2513_, v___y_2524_, v___y_2517_, v_a_2422_, v___y_2520_, v___y_2522_, v___y_2515_, v___y_2526_, v___y_2523_, v___y_2511_, v___y_2519_, v___y_2521_, v_prom_2418_, v___x_2509_, v___f_2508_, v___f_2507_, v___f_2506_, v___y_2518_, v_cmdState_2417_, v___y_2516_, v___y_2525_, v_old_x3f_2415_, v_parseCancelTk_2420_, v___x_2533_);
lean_dec_ref(v___y_2516_);
lean_dec(v_prom_2418_);
lean_dec(v___y_2511_);
lean_dec(v___y_2514_);
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
v___y_2512_ = v___y_2549_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v___y_2541_;
v___y_2518_ = v___y_2542_;
v___y_2519_ = v___y_2543_;
v___y_2520_ = v___y_2544_;
v___y_2521_ = v_snd_2551_;
v___y_2522_ = v___y_2545_;
v___y_2523_ = v___y_2546_;
v___y_2524_ = v___y_2547_;
v___y_2525_ = v___y_2548_;
v___y_2526_ = v_fst_2550_;
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
v___y_2512_ = v___y_2549_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v___y_2541_;
v___y_2518_ = v___y_2542_;
v___y_2519_ = v___y_2543_;
v___y_2520_ = v___y_2544_;
v___y_2521_ = v_snd_2551_;
v___y_2522_ = v___y_2545_;
v___y_2523_ = v___y_2546_;
v___y_2524_ = v___y_2547_;
v___y_2525_ = v___y_2548_;
v___y_2526_ = v_fst_2550_;
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
v___x_2593_ = l_IO_CancelToken_isSet(v_parseCancelTk_2420_);
v___x_2594_ = 1;
if (v___x_2593_ == 0)
{
lean_dec(v___y_2590_);
if (v_sync_2419_ == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2595_ = lean_io_promise_new();
v___x_2596_ = lean_io_promise_new();
v___x_2597_ = lean_io_promise_new();
v___x_2598_ = lean_io_promise_new();
v___x_2599_ = l_Lean_internal_cmdlineSnapshots;
v___x_2600_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2592_, v___x_2599_);
lean_dec_ref(v___y_2592_);
if (v___x_2600_ == 0)
{
v___y_2564_ = v___x_2596_;
v___y_2565_ = v___y_2584_;
v___y_2566_ = v___x_2598_;
v___y_2567_ = v___x_2594_;
v___y_2568_ = v___y_2588_;
v___y_2569_ = v___x_2593_;
v___y_2570_ = v___y_2587_;
v___y_2571_ = v___x_2597_;
v___y_2572_ = v___y_2583_;
v___y_2573_ = v___y_2585_;
v___y_2574_ = v___x_2595_;
v___y_2575_ = v___y_2586_;
v___y_2576_ = v___x_2599_;
v___y_2577_ = v___y_2589_;
v___y_2578_ = v___y_2591_;
v___y_2579_ = v___x_2600_;
goto v___jp_2563_;
}
else
{
uint8_t v___x_2601_; 
lean_inc(v___y_2589_);
v___x_2601_ = l_Lean_Parser_isTerminalCommand(v___y_2589_);
if (v___x_2601_ == 0)
{
v___y_2564_ = v___x_2596_;
v___y_2565_ = v___y_2584_;
v___y_2566_ = v___x_2598_;
v___y_2567_ = v___x_2594_;
v___y_2568_ = v___y_2588_;
v___y_2569_ = v___x_2593_;
v___y_2570_ = v___y_2587_;
v___y_2571_ = v___x_2597_;
v___y_2572_ = v___y_2583_;
v___y_2573_ = v___y_2585_;
v___y_2574_ = v___x_2595_;
v___y_2575_ = v___y_2586_;
v___y_2576_ = v___x_2599_;
v___y_2577_ = v___y_2589_;
v___y_2578_ = v___y_2591_;
v___y_2579_ = v___x_2600_;
goto v___jp_2563_;
}
else
{
lean_inc(v___y_2589_);
v___y_2536_ = v___x_2596_;
v___y_2537_ = v___y_2584_;
v___y_2538_ = v___x_2598_;
v___y_2539_ = v___x_2594_;
v___y_2540_ = v___y_2588_;
v___y_2541_ = v___x_2593_;
v___y_2542_ = v___y_2587_;
v___y_2543_ = v___x_2597_;
v___y_2544_ = v___y_2583_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___x_2595_;
v___y_2547_ = v___y_2586_;
v___y_2548_ = v___x_2599_;
v___y_2549_ = v___y_2589_;
v_fst_2550_ = v___y_2589_;
v_snd_2551_ = v___y_2591_;
goto v___jp_2535_;
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2589_);
v___x_2602_ = lean_box(v___x_2593_);
v___x_2603_ = lean_box(v___x_2594_);
lean_inc_ref(v_a_2422_);
v___f_2604_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 19, 18);
lean_closure_set(v___f_2604_, 0, v_cmds_2421_);
lean_closure_set(v___f_2604_, 1, v___y_2584_);
lean_closure_set(v___f_2604_, 2, v___y_2586_);
lean_closure_set(v___f_2604_, 3, v___x_2602_);
lean_closure_set(v___f_2604_, 4, v_a_2422_);
lean_closure_set(v___f_2604_, 5, v___y_2583_);
lean_closure_set(v___f_2604_, 6, v___y_2585_);
lean_closure_set(v___f_2604_, 7, v___x_2603_);
lean_closure_set(v___f_2604_, 8, v_prom_2418_);
lean_closure_set(v___f_2604_, 9, v___x_2509_);
lean_closure_set(v___f_2604_, 10, v___f_2508_);
lean_closure_set(v___f_2604_, 11, v___f_2507_);
lean_closure_set(v___f_2604_, 12, v___f_2506_);
lean_closure_set(v___f_2604_, 13, v___y_2587_);
lean_closure_set(v___f_2604_, 14, v_cmdState_2417_);
lean_closure_set(v___f_2604_, 15, v___y_2588_);
lean_closure_set(v___f_2604_, 16, v_old_x3f_2415_);
lean_closure_set(v___f_2604_, 17, v_parseCancelTk_2420_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_io_as_task(v___f_2604_, v___x_2605_);
lean_dec_ref(v___x_2606_);
goto v___jp_2461_;
}
}
else
{
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_cmds_2421_);
lean_dec_ref(v_parseCancelTk_2420_);
if (lean_obj_tag(v_old_x3f_2415_) == 1)
{
lean_object* v_val_2607_; lean_object* v___x_2608_; lean_object* v_children_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_val_2607_ = lean_ctor_get(v_old_x3f_2415_, 0);
lean_inc(v_val_2607_);
lean_dec_ref_known(v_old_x3f_2415_, 1);
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
v___y_2466_ = v___x_2594_;
v___y_2467_ = v___y_2590_;
v___y_2468_ = v___y_2591_;
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
v___y_2466_ = v___x_2594_;
v___y_2467_ = v___y_2590_;
v___y_2468_ = v___y_2591_;
goto v___jp_2465_;
}
else
{
size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = ((size_t)0ULL);
v___x_2616_ = lean_usize_of_nat(v___x_2611_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2609_, v___x_2615_, v___x_2616_, v___x_2613_);
lean_dec_ref(v_children_2609_);
v___y_2502_ = v___y_2590_;
v___y_2503_ = v___x_2594_;
v___y_2504_ = v___y_2591_;
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
v___y_2502_ = v___y_2590_;
v___y_2503_ = v___x_2594_;
v___y_2504_ = v___y_2591_;
v___y_2505_ = v___x_2620_;
goto v___jp_2501_;
}
}
}
else
{
lean_dec(v_old_x3f_2415_);
v___y_2466_ = v___x_2594_;
v___y_2467_ = v___y_2590_;
v___y_2468_ = v___y_2591_;
goto v___jp_2465_;
}
}
}
v___jp_2621_:
{
lean_object* v_env_2622_; lean_object* v_scopes_2623_; lean_object* v___x_2624_; lean_object* v_opts_2625_; lean_object* v_currNamespace_2626_; lean_object* v_openDecls_2627_; lean_object* v___x_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_snd_2633_; 
v_env_2622_ = lean_ctor_get(v_cmdState_2417_, 0);
v_scopes_2623_ = lean_ctor_get(v_cmdState_2417_, 2);
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
lean_inc_ref(v_parserState_2416_);
lean_inc_ref(v_a_2422_);
v___f_2629_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2629_, 0, v_a_2422_);
lean_closure_set(v___f_2629_, 1, v___x_2628_);
lean_closure_set(v___f_2629_, 2, v_parserState_2416_);
v___x_2630_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_profileit(v___x_2630_, v_opts_2625_, v___f_2629_, v___x_2631_);
v_snd_2633_ = lean_ctor_get(v___x_2632_, 1);
lean_inc(v_snd_2633_);
if (lean_obj_tag(v_old_x3f_2415_) == 1)
{
lean_object* v_val_2634_; lean_object* v_fst_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v_pos_2638_; lean_object* v_toSnapshot_2639_; lean_object* v_stx_2640_; lean_object* v_parserState_2641_; lean_object* v_elabSnap_2642_; lean_object* v_nextCmdSnap_x3f_2643_; uint8_t v___x_2644_; 
v_val_2634_ = lean_ctor_get(v_old_x3f_2415_, 0);
v_fst_2635_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_n(v_fst_2635_, 2);
lean_dec(v___x_2632_);
v_fst_2636_ = lean_ctor_get(v_snd_2633_, 0);
lean_inc(v_fst_2636_);
v_snd_2637_ = lean_ctor_get(v_snd_2633_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_snd_2633_);
v_pos_2638_ = lean_ctor_get(v_parserState_2416_, 0);
lean_inc(v_pos_2638_);
lean_dec_ref(v_parserState_2416_);
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
lean_inc_ref(v_opts_2625_);
lean_inc(v_fst_2636_);
lean_inc(v_fst_2635_);
v___y_2583_ = v_snd_2637_;
v___y_2584_ = v_fst_2635_;
v___y_2585_ = v___x_2631_;
v___y_2586_ = v_fst_2636_;
v___y_2587_ = v_pos_2638_;
v___y_2588_ = v_opts_2625_;
v___y_2589_ = v_fst_2635_;
v___y_2590_ = v___x_2631_;
v___y_2591_ = v_fst_2636_;
v___y_2592_ = v_opts_2625_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_val_2645_ = lean_ctor_get(v_nextCmdSnap_x3f_2643_, 0);
v___x_2646_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2645_);
v___x_2647_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2646_, v_val_2645_);
lean_inc_ref(v_opts_2625_);
lean_inc(v_fst_2636_);
lean_inc(v_fst_2635_);
v___y_2583_ = v_snd_2637_;
v___y_2584_ = v_fst_2635_;
v___y_2585_ = v___x_2631_;
v___y_2586_ = v_fst_2636_;
v___y_2587_ = v_pos_2638_;
v___y_2588_ = v_opts_2625_;
v___y_2589_ = v_fst_2635_;
v___y_2590_ = v___x_2631_;
v___y_2591_ = v_fst_2636_;
v___y_2592_ = v_opts_2625_;
goto v___jp_2582_;
}
}
else
{
lean_inc(v_val_2634_);
lean_dec(v_pos_2638_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2635_);
lean_dec_ref_known(v_old_x3f_2415_, 1);
lean_dec_ref(v_opts_2625_);
lean_dec_ref(v_parseCancelTk_2420_);
lean_dec_ref(v_cmdState_2417_);
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
lean_dec_ref_known(v_nextCmdSnap_x3f_2643_, 1);
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
lean_dec_ref(v_cmds_2421_);
v___x_2649_ = lean_io_promise_resolve(v_val_2634_, v_prom_2418_);
lean_dec(v_prom_2418_);
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
v_pos_2653_ = lean_ctor_get(v_parserState_2416_, 0);
lean_inc(v_pos_2653_);
lean_dec_ref(v_parserState_2416_);
lean_inc_ref(v_opts_2625_);
v___y_2583_ = v_snd_2652_;
v___y_2584_ = v_fst_2650_;
v___y_2585_ = v___x_2631_;
v___y_2586_ = v_fst_2651_;
v___y_2587_ = v_pos_2653_;
v___y_2588_ = v_opts_2625_;
v___y_2589_ = v_fst_2650_;
v___y_2590_ = v___x_2631_;
v___y_2591_ = v_fst_2651_;
v___y_2592_ = v_opts_2625_;
goto v___jp_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2670_, lean_object* v_cmds_2671_, lean_object* v_stx_2672_, lean_object* v_newParserState_2673_, lean_object* v_val_2674_, uint8_t v_sync_2675_, lean_object* v_val_2676_, lean_object* v_a_2677_, lean_object* v_oldNext_2678_){
_start:
{
lean_object* v_cmdState_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_cmdState_2680_ = lean_ctor_get(v_oldResult_2670_, 1);
lean_inc_ref(v_cmdState_2680_);
lean_dec_ref(v_oldResult_2670_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_oldNext_2678_);
v___x_2682_ = lean_array_push(v_cmds_2671_, v_stx_2672_);
v___x_2683_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2681_, v_newParserState_2673_, v_cmdState_2680_, v_val_2674_, v_sync_2675_, v_val_2676_, v___x_2682_, v_a_2677_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2684_ = _args[0];
lean_object* v_val_2685_ = _args[1];
lean_object* v_cmds_2686_ = _args[2];
lean_object* v_fst_2687_ = _args[3];
lean_object* v_fst_2688_ = _args[4];
lean_object* v_val_2689_ = _args[5];
lean_object* v_a_2690_ = _args[6];
lean_object* v_snd_2691_ = _args[7];
lean_object* v___x_2692_ = _args[8];
lean_object* v___x_2693_ = _args[9];
lean_object* v_fst_2694_ = _args[10];
lean_object* v_val_2695_ = _args[11];
lean_object* v_val_2696_ = _args[12];
lean_object* v_val_2697_ = _args[13];
lean_object* v_snd_2698_ = _args[14];
lean_object* v_prom_2699_ = _args[15];
lean_object* v___x_2700_ = _args[16];
lean_object* v___f_2701_ = _args[17];
lean_object* v___f_2702_ = _args[18];
lean_object* v___f_2703_ = _args[19];
lean_object* v_pos_2704_ = _args[20];
lean_object* v_cmdState_2705_ = _args[21];
lean_object* v_opts_2706_ = _args[22];
lean_object* v___x_2707_ = _args[23];
lean_object* v_old_x3f_2708_ = _args[24];
lean_object* v_parseCancelTk_2709_ = _args[25];
lean_object* v_next_x3f_2710_ = _args[26];
lean_object* v___y_2711_ = _args[27];
_start:
{
uint8_t v_val_45574__boxed_2712_; uint8_t v___x_45577__boxed_2713_; lean_object* v_res_2714_; 
v_val_45574__boxed_2712_ = lean_unbox(v_val_2689_);
v___x_45577__boxed_2713_ = lean_unbox(v___x_2693_);
v_res_2714_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2684_, v_val_2685_, v_cmds_2686_, v_fst_2687_, v_fst_2688_, v_val_45574__boxed_2712_, v_a_2690_, v_snd_2691_, v___x_2692_, v___x_45577__boxed_2713_, v_fst_2694_, v_val_2695_, v_val_2696_, v_val_2697_, v_snd_2698_, v_prom_2699_, v___x_2700_, v___f_2701_, v___f_2702_, v___f_2703_, v_pos_2704_, v_cmdState_2705_, v_opts_2706_, v___x_2707_, v_old_x3f_2708_, v_parseCancelTk_2709_, v_next_x3f_2710_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v_opts_2706_);
lean_dec(v_prom_2699_);
lean_dec(v_val_2696_);
lean_dec_ref(v_a_2690_);
lean_dec(v_val_2685_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2715_, lean_object* v_parserState_2716_, lean_object* v_cmdState_2717_, lean_object* v_prom_2718_, lean_object* v_sync_2719_, lean_object* v_parseCancelTk_2720_, lean_object* v_cmds_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
uint8_t v_sync_boxed_2724_; lean_object* v_res_2725_; 
v_sync_boxed_2724_ = lean_unbox(v_sync_2719_);
v_res_2725_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2715_, v_parserState_2716_, v_cmdState_2717_, v_prom_2718_, v_sync_boxed_2724_, v_parseCancelTk_2720_, v_cmds_2721_, v_a_2722_);
lean_dec_ref(v_a_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2726_, size_t v_i_2727_, size_t v_stop_2728_, lean_object* v_b_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2726_, v_i_2727_, v_stop_2728_, v_b_2729_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2733_, lean_object* v_i_2734_, lean_object* v_stop_2735_, lean_object* v_b_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
size_t v_i_boxed_2739_; size_t v_stop_boxed_2740_; lean_object* v_res_2741_; 
v_i_boxed_2739_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_stop_boxed_2740_ = lean_unbox_usize(v_stop_2735_);
lean_dec(v_stop_2735_);
v_res_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2733_, v_i_boxed_2739_, v_stop_boxed_2740_, v_b_2736_, v___y_2737_);
lean_dec_ref(v___y_2737_);
lean_dec_ref(v_as_2733_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2742_, lean_object* v_opt_2743_){
_start:
{
lean_object* v_name_2744_; lean_object* v_map_2745_; lean_object* v___x_2746_; 
v_name_2744_ = lean_ctor_get(v_opt_2743_, 0);
v_map_2745_ = lean_ctor_get(v_opts_2742_, 0);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2745_, v_name_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_box(0);
return v___x_2747_;
}
else
{
lean_object* v_val_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2757_; 
v_val_2748_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2750_ = v___x_2746_;
v_isShared_2751_ = v_isSharedCheck_2757_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_val_2748_);
lean_dec(v___x_2746_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2757_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
if (lean_obj_tag(v_val_2748_) == 0)
{
lean_object* v_v_2752_; lean_object* v___x_2754_; 
v_v_2752_ = lean_ctor_get(v_val_2748_, 0);
lean_inc_ref(v_v_2752_);
lean_dec_ref_known(v_val_2748_, 1);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_v_2752_);
v___x_2754_ = v___x_2750_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_v_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
else
{
lean_object* v___x_2756_; 
lean_del_object(v___x_2750_);
lean_dec(v_val_2748_);
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2758_, lean_object* v_opt_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2758_, v_opt_2759_);
lean_dec_ref(v_opt_2759_);
lean_dec_ref(v_opts_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2761_, lean_object* v_x_2762_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2761_);
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2765_, 0, v_x_2762_);
lean_ctor_set(v___x_2765_, 1, v___x_2763_);
lean_ctor_set(v___x_2765_, 2, v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2772_ = l_Array_toPArray_x27___redArg(v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
if (lean_obj_tag(v_a_2773_) == 0)
{
lean_object* v___x_2775_; 
v___x_2775_ = l_List_reverse___redArg(v_a_2774_);
return v___x_2775_;
}
else
{
lean_object* v_head_2776_; lean_object* v_tail_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2790_; 
v_head_2776_ = lean_ctor_get(v_a_2773_, 0);
v_tail_2777_ = lean_ctor_get(v_a_2773_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_a_2773_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2779_ = v_a_2773_;
v_isShared_2780_ = v_isSharedCheck_2790_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_tail_2777_);
lean_inc(v_head_2776_);
lean_dec(v_a_2773_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2790_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2781_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v_head_2776_);
v___x_2783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
v___x_2784_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v_a_2774_);
lean_ctor_set(v___x_2779_, 0, v___x_2785_);
v___x_2787_ = v___x_2779_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_a_2774_);
v___x_2787_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
v_a_2773_ = v_tail_2777_;
v_a_2774_ = v___x_2787_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2801_; double v___x_2802_; 
v___x_2801_ = lean_unsigned_to_nat(1000000000u);
v___x_2802_ = lean_float_of_nat(v___x_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2810_ = l_Lean_MessageData_ofFormat(v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2811_, lean_object* v_stx_2812_, lean_object* v_origStx_2813_, lean_object* v_toProcessingContext_2814_, lean_object* v___x_2815_, lean_object* v_fileMap_2816_, lean_object* v_parserState_2817_, lean_object* v_a_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_toProcessingContext_2823_; lean_object* v___x_2824_; 
v_toProcessingContext_2823_ = lean_ctor_get(v___y_2821_, 0);
lean_inc_ref(v_toProcessingContext_2823_);
lean_inc(v_stx_2812_);
v___x_2824_ = lean_apply_3(v_setupImports_2811_, v_stx_2812_, v_toProcessingContext_2823_, lean_box(0));
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_3037_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_3037_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_3037_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
if (lean_obj_tag(v_a_2825_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; 
lean_dec_ref(v___x_2820_);
lean_dec(v___x_2819_);
lean_dec_ref(v_parserState_2817_);
lean_dec_ref(v_fileMap_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v_toProcessingContext_2814_);
lean_dec(v_origStx_2813_);
lean_dec(v_stx_2812_);
v_a_2829_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v_a_2825_, 1);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v_a_2829_);
v___x_2831_ = v___x_2827_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_3036_; 
v_a_2833_ = lean_ctor_get(v_a_2825_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2835_ = v_a_2825_;
v_isShared_2836_ = v_isSharedCheck_3036_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v_a_2825_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_3036_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v_mainModuleName_2838_; lean_object* v_package_x3f_2839_; uint8_t v_isModule_2840_; lean_object* v_imports_2841_; lean_object* v_opts_2842_; uint32_t v_trustLevel_2843_; lean_object* v_importArts_2844_; lean_object* v_plugins_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; lean_object* v___x_2850_; 
v___x_2837_ = lean_io_mono_nanos_now();
v_mainModuleName_2838_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_mainModuleName_2838_);
v_package_x3f_2839_ = lean_ctor_get(v_a_2833_, 1);
lean_inc(v_package_x3f_2839_);
v_isModule_2840_ = lean_ctor_get_uint8(v_a_2833_, sizeof(void*)*6 + 4);
v_imports_2841_ = lean_ctor_get(v_a_2833_, 2);
lean_inc_ref(v_imports_2841_);
v_opts_2842_ = lean_ctor_get(v_a_2833_, 3);
lean_inc_ref(v_opts_2842_);
v_trustLevel_2843_ = lean_ctor_get_uint32(v_a_2833_, sizeof(void*)*6);
v_importArts_2844_ = lean_ctor_get(v_a_2833_, 4);
lean_inc(v_importArts_2844_);
v_plugins_2845_ = lean_ctor_get(v_a_2833_, 5);
lean_inc_ref(v_plugins_2845_);
lean_dec(v_a_2833_);
v___x_2846_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2812_);
v___x_2847_ = l_Lean_MessageLog_empty;
v___x_2848_ = 1;
lean_inc(v_stx_2812_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v_stx_2812_);
v___x_2850_ = v___x_2835_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_stx_2812_);
v___x_2850_ = v_reuseFailAlloc_3035_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_origStx_2813_);
lean_inc_ref(v___x_2850_);
lean_inc_ref(v_opts_2842_);
v___x_2852_ = l_Lean_Elab_processHeaderCore(v___x_2846_, v_imports_2841_, v_isModule_2840_, v_opts_2842_, v___x_2847_, v_toProcessingContext_2814_, v_trustLevel_2843_, v_plugins_2845_, v___x_2848_, v_mainModuleName_2838_, v_package_x3f_2839_, v_importArts_2844_, v___x_2850_, v___x_2851_);
lean_dec(v___x_2846_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_3026_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_3026_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_3026_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_fst_2857_; lean_object* v_snd_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_3025_; 
v_fst_2857_ = lean_ctor_get(v_a_2853_, 0);
v_snd_2858_ = lean_ctor_get(v_a_2853_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2860_ = v_a_2853_;
v_isShared_2861_ = v_isSharedCheck_3025_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_snd_2858_);
lean_inc(v_fst_2857_);
lean_dec(v_a_2853_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_3025_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v_traceState_2880_; 
v___x_2862_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2858_);
v___x_2863_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2858_);
v___x_2864_ = l_Lean_MessageLog_hasErrors(v_snd_2858_);
if (v___x_2864_ == 0)
{
double v___x_2973_; double v___x_2974_; double v___x_2975_; double v___x_2976_; double v___x_2977_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_del_object(v___x_2827_);
lean_dec_ref(v___x_2820_);
v___x_2973_ = lean_float_of_nat(v___x_2837_);
v___x_2974_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2975_ = lean_float_div(v___x_2973_, v___x_2974_);
v___x_2976_ = lean_float_of_nat(v___x_2862_);
v___x_2977_ = lean_float_div(v___x_2976_, v___x_2974_);
v___x_2994_ = l_Lean_trace_profiler_output;
v___x_2995_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2842_, v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = l_Lean_trace_profiler_serve;
v___x_2997_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2842_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2880_ = v___x_2998_;
goto v___jp_2879_;
}
else
{
goto v___jp_2978_;
}
}
else
{
lean_dec_ref_known(v___x_2995_, 1);
goto v___jp_2978_;
}
v___jp_2978_:
{
uint64_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2979_ = 0ULL;
v___x_2980_ = lean_box(0);
v___x_2981_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2982_ = lean_box(0);
v___x_2983_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2984_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2984_, 0, v___x_2981_);
lean_ctor_set(v___x_2984_, 1, v___x_2982_);
lean_ctor_set(v___x_2984_, 2, v___x_2983_);
lean_ctor_set_float(v___x_2984_, sizeof(void*)*3, v___x_2975_);
lean_ctor_set_float(v___x_2984_, sizeof(void*)*3 + 8, v___x_2977_);
lean_ctor_set_uint8(v___x_2984_, sizeof(void*)*3 + 16, v___x_2848_);
v___x_2985_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2986_ = lean_mk_empty_array_with_capacity(v___x_2815_);
v___x_2987_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2984_);
lean_ctor_set(v___x_2987_, 1, v___x_2985_);
lean_ctor_set(v___x_2987_, 2, v___x_2986_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2980_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_mk_empty_array_with_capacity(v___x_2989_);
v___x_2991_ = lean_array_push(v___x_2990_, v___x_2988_);
v___x_2992_ = l_Array_toPArray_x27___redArg(v___x_2991_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set_uint64(v___x_2993_, sizeof(void*)*1, v___x_2979_);
v_traceState_2880_ = v___x_2993_;
goto v___jp_2879_;
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint64_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_dec(v___x_2862_);
lean_del_object(v___x_2860_);
lean_dec(v_snd_2858_);
lean_dec(v_fst_2857_);
lean_del_object(v___x_2855_);
lean_dec_ref(v___x_2850_);
lean_dec_ref(v_opts_2842_);
lean_dec(v___x_2837_);
lean_dec(v___x_2819_);
lean_dec_ref(v_parserState_2817_);
lean_dec_ref(v_fileMap_2816_);
lean_dec(v_stx_2812_);
v___x_2999_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3000_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3001_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2815_, 2);
v___x_3002_ = l_Lean_Name_num___override(v___x_3001_, v___x_2815_);
v___x_3003_ = l_Lean_Name_str___override(v___x_3002_, v___x_2999_);
v___x_3004_ = l_Lean_Name_str___override(v___x_3003_, v___x_3000_);
v___x_3005_ = l_Lean_Name_str___override(v___x_3004_, v___x_2999_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3007_ = l_Lean_Name_str___override(v___x_3005_, v___x_3006_);
v___x_3008_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3009_ = l_Lean_Name_str___override(v___x_3007_, v___x_3008_);
v___x_3010_ = l_Lean_Name_toString(v___x_3009_, v___x_2848_);
v___x_3011_ = lean_box(0);
v___x_3012_ = 0ULL;
v___x_3013_ = lean_unsigned_to_nat(32u);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_3013_);
v___x_3015_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3016_ = ((size_t)5ULL);
v___x_3017_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3014_);
lean_ctor_set(v___x_3017_, 2, v___x_2815_);
lean_ctor_set(v___x_3017_, 3, v___x_2815_);
lean_ctor_set_usize(v___x_3017_, 4, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set_uint64(v___x_3018_, sizeof(void*)*1, v___x_3012_);
v___x_3019_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3019_, 0, v___x_3010_);
lean_ctor_set(v___x_3019_, 1, v___x_2863_);
lean_ctor_set(v___x_3019_, 2, v___x_3011_);
lean_ctor_set(v___x_3019_, 3, v___x_3018_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*4, v___x_2864_);
v___x_3020_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2820_);
v___x_3021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
lean_ctor_set(v___x_3021_, 2, v___x_3011_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_3021_);
v___x_3023_ = v___x_2827_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
v___jp_2865_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2871_);
v___x_2873_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2873_, 0, v___y_2866_);
lean_ctor_set(v___x_2873_, 1, v___x_2863_);
lean_ctor_set(v___x_2873_, 2, v___x_2872_);
lean_ctor_set(v___x_2873_, 3, v___y_2869_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*4, v___x_2864_);
v___x_2874_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2870_, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v___y_2868_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
lean_ctor_set(v___x_2875_, 2, v___y_2867_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2875_);
v___x_2877_ = v___x_2855_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
v___jp_2879_:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_Language_Lean_reparseOptions(v_opts_2842_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v_env_2888_; lean_object* v_messages_2889_; lean_object* v_scopes_2890_; lean_object* v_usedQuotCtxts_2891_; lean_object* v_nextMacroScope_2892_; lean_object* v_maxRecDepth_2893_; lean_object* v_ngen_2894_; lean_object* v_auxDeclNGen_2895_; lean_object* v_snapshotTasks_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2962_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2815_, 4);
v___x_2884_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2815_);
lean_ctor_set(v___x_2884_, 1, v___x_2815_);
lean_ctor_set(v___x_2884_, 2, v___x_2815_);
lean_ctor_set(v___x_2884_, 3, v___x_2815_);
lean_ctor_set(v___x_2884_, 4, v___x_2883_);
lean_ctor_set(v___x_2884_, 5, v___x_2883_);
lean_ctor_set(v___x_2884_, 6, v___x_2883_);
lean_ctor_set(v___x_2884_, 7, v___x_2883_);
lean_ctor_set(v___x_2884_, 8, v___x_2883_);
lean_ctor_set(v___x_2884_, 9, v___x_2883_);
v___x_2885_ = lean_io_promise_new();
v___x_2886_ = l_IO_CancelToken_new();
lean_inc(v_fst_2857_);
v___x_2887_ = l_Lean_Elab_Command_mkState(v_fst_2857_, v_snd_2858_, v_a_2882_);
v_env_2888_ = lean_ctor_get(v___x_2887_, 0);
v_messages_2889_ = lean_ctor_get(v___x_2887_, 1);
v_scopes_2890_ = lean_ctor_get(v___x_2887_, 2);
v_usedQuotCtxts_2891_ = lean_ctor_get(v___x_2887_, 3);
v_nextMacroScope_2892_ = lean_ctor_get(v___x_2887_, 4);
v_maxRecDepth_2893_ = lean_ctor_get(v___x_2887_, 5);
v_ngen_2894_ = lean_ctor_get(v___x_2887_, 6);
v_auxDeclNGen_2895_ = lean_ctor_get(v___x_2887_, 7);
v_snapshotTasks_2896_ = lean_ctor_get(v___x_2887_, 10);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2963_ = lean_ctor_get(v___x_2887_, 9);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v___x_2887_, 8);
lean_dec(v_unused_2964_);
v___x_2898_ = v___x_2887_;
v_isShared_2899_ = v_isSharedCheck_2962_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_snapshotTasks_2896_);
lean_inc(v_auxDeclNGen_2895_);
lean_inc(v_ngen_2894_);
lean_inc(v_maxRecDepth_2893_);
lean_inc(v_nextMacroScope_2892_);
lean_inc(v_usedQuotCtxts_2891_);
lean_inc(v_scopes_2890_);
lean_inc(v_messages_2889_);
lean_inc(v_env_2888_);
lean_dec(v___x_2887_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2962_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2900_ = lean_box(0);
v___x_2901_ = l_Lean_Options_empty;
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_box(0);
v___x_2904_ = lean_unsigned_to_nat(1u);
v___x_2905_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2906_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2906_, 0, v_fst_2857_);
lean_ctor_set(v___x_2906_, 1, v___x_2900_);
lean_ctor_set(v___x_2906_, 2, v_fileMap_2816_);
lean_ctor_set(v___x_2906_, 3, v___x_2884_);
lean_ctor_set(v___x_2906_, 4, v___x_2901_);
lean_ctor_set(v___x_2906_, 5, v___x_2902_);
lean_ctor_set(v___x_2906_, 6, v___x_2903_);
lean_ctor_set(v___x_2906_, 7, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
v___x_2908_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2812_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v_stx_2812_);
lean_ctor_set(v___x_2860_, 0, v___x_2908_);
v___x_2910_ = v___x_2860_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_stx_2812_);
v___x_2910_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
v___x_2912_ = lean_unsigned_to_nat(2u);
v___x_2913_ = l_Lean_Syntax_getArg(v_stx_2812_, v___x_2912_);
lean_dec(v_stx_2812_);
v___x_2914_ = l_Lean_Syntax_getArgs(v___x_2913_);
lean_dec(v___x_2913_);
v___x_2915_ = lean_array_to_list(v___x_2914_);
v___x_2916_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2915_, v___x_2903_);
v___x_2917_ = l_List_toPArray_x27___redArg(v___x_2916_);
v___x_2918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2911_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2907_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___x_2921_ = lean_array_push(v___x_2920_, v___x_2919_);
v___x_2922_ = l_Array_toPArray_x27___redArg(v___x_2921_);
lean_dec_ref(v___x_2921_);
lean_inc_ref(v___x_2922_);
v___x_2923_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2923_, 0, v___x_2883_);
lean_ctor_set(v___x_2923_, 1, v___x_2883_);
lean_ctor_set(v___x_2923_, 2, v___x_2922_);
lean_ctor_set_uint8(v___x_2923_, sizeof(void*)*3, v___x_2848_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 9, v_traceState_2880_);
lean_ctor_set(v___x_2898_, 8, v___x_2923_);
v___x_2925_ = v___x_2898_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_env_2888_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_messages_2889_);
lean_ctor_set(v_reuseFailAlloc_2960_, 2, v_scopes_2890_);
lean_ctor_set(v_reuseFailAlloc_2960_, 3, v_usedQuotCtxts_2891_);
lean_ctor_set(v_reuseFailAlloc_2960_, 4, v_nextMacroScope_2892_);
lean_ctor_set(v_reuseFailAlloc_2960_, 5, v_maxRecDepth_2893_);
lean_ctor_set(v_reuseFailAlloc_2960_, 6, v_ngen_2894_);
lean_ctor_set(v_reuseFailAlloc_2960_, 7, v_auxDeclNGen_2895_);
lean_ctor_set(v_reuseFailAlloc_2960_, 8, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2960_, 9, v_traceState_2880_);
lean_ctor_set(v_reuseFailAlloc_2960_, 10, v_snapshotTasks_2896_);
v___x_2925_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; lean_object* v_size_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint64_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2926_ = lean_mk_empty_array_with_capacity(v___x_2815_);
lean_inc_ref(v___x_2886_);
lean_inc(v___x_2885_);
lean_inc_ref(v___x_2925_);
v___x_2927_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2900_, v_parserState_2817_, v___x_2925_, v___x_2885_, v___x_2848_, v___x_2886_, v___x_2926_, v_a_2818_);
v___x_2928_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2929_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2930_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2815_, 3);
v___x_2931_ = l_Lean_Name_num___override(v___x_2930_, v___x_2815_);
v___x_2932_ = lean_unsigned_to_nat(32u);
v___x_2933_ = lean_mk_empty_array_with_capacity(v___x_2932_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2935_ = ((size_t)5ULL);
v___x_2936_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2933_);
lean_ctor_set(v___x_2936_, 2, v___x_2815_);
lean_ctor_set(v___x_2936_, 3, v___x_2815_);
lean_ctor_set_usize(v___x_2936_, 4, v___x_2935_);
v_size_2937_ = lean_ctor_get(v___x_2922_, 2);
lean_inc(v_size_2937_);
v___x_2938_ = l_Lean_Name_str___override(v___x_2931_, v___x_2928_);
v___x_2939_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2819_);
v___x_2940_ = l_Lean_Name_str___override(v___x_2938_, v___x_2929_);
v___x_2941_ = l_Lean_Name_str___override(v___x_2940_, v___x_2928_);
v___x_2942_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2943_ = l_Lean_Name_str___override(v___x_2941_, v___x_2942_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2945_ = l_Lean_Name_str___override(v___x_2943_, v___x_2944_);
v___x_2946_ = l_Lean_Name_toString(v___x_2945_, v___x_2848_);
v___x_2947_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2948_ = 0ULL;
v___x_2949_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2949_, 0, v___x_2936_);
lean_ctor_set_uint64(v___x_2949_, sizeof(void*)*1, v___x_2948_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2886_);
v___x_2951_ = l_IO_Promise_result_x21___redArg(v___x_2885_);
lean_dec(v___x_2885_);
v___x_2952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2819_);
lean_ctor_set(v___x_2952_, 1, v___x_2939_);
lean_ctor_set(v___x_2952_, 2, v___x_2950_);
lean_ctor_set(v___x_2952_, 3, v___x_2951_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2925_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_inc_ref(v___x_2949_);
lean_inc_ref(v___x_2946_);
v___x_2955_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2955_, 0, v___x_2946_);
lean_ctor_set(v___x_2955_, 1, v___x_2947_);
lean_ctor_set(v___x_2955_, 2, v___x_2900_);
lean_ctor_set(v___x_2955_, 3, v___x_2949_);
lean_ctor_set_uint8(v___x_2955_, sizeof(void*)*4, v___x_2864_);
v___x_2956_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2957_ = lean_nat_dec_lt(v___x_2815_, v_size_2937_);
lean_dec(v_size_2937_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec_ref(v___x_2922_);
lean_dec(v___x_2815_);
v___x_2958_ = l_outOfBounds___redArg(v___x_2956_);
v___y_2866_ = v___x_2946_;
v___y_2867_ = v___x_2954_;
v___y_2868_ = v___x_2955_;
v___y_2869_ = v___x_2949_;
v___y_2870_ = v___x_2850_;
v___y_2871_ = v___x_2958_;
goto v___jp_2865_;
}
else
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2956_, v___x_2922_, v___x_2815_);
lean_dec(v___x_2815_);
lean_dec_ref(v___x_2922_);
v___y_2866_ = v___x_2946_;
v___y_2867_ = v___x_2954_;
v___y_2868_ = v___x_2955_;
v___y_2869_ = v___x_2949_;
v___y_2870_ = v___x_2850_;
v___y_2871_ = v___x_2959_;
goto v___jp_2865_;
}
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v_traceState_2880_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2860_);
lean_dec(v_snd_2858_);
lean_dec(v_fst_2857_);
lean_del_object(v___x_2855_);
lean_dec_ref(v___x_2850_);
lean_dec(v___x_2819_);
lean_dec_ref(v_parserState_2817_);
lean_dec_ref(v_fileMap_2816_);
lean_dec(v___x_2815_);
lean_dec(v_stx_2812_);
v_a_2965_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2881_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2881_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v___x_2850_);
lean_dec_ref(v_opts_2842_);
lean_dec(v___x_2837_);
lean_del_object(v___x_2827_);
lean_dec_ref(v___x_2820_);
lean_dec(v___x_2819_);
lean_dec_ref(v_parserState_2817_);
lean_dec_ref(v_fileMap_2816_);
lean_dec(v___x_2815_);
lean_dec(v_stx_2812_);
v_a_3027_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2852_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2852_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
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
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_2820_);
lean_dec(v___x_2819_);
lean_dec_ref(v_parserState_2817_);
lean_dec_ref(v_fileMap_2816_);
lean_dec(v___x_2815_);
lean_dec_ref(v_toProcessingContext_2814_);
lean_dec(v_origStx_2813_);
lean_dec(v_stx_2812_);
v_a_3038_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2824_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2824_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3046_, lean_object* v_stx_3047_, lean_object* v_origStx_3048_, lean_object* v_toProcessingContext_3049_, lean_object* v___x_3050_, lean_object* v_fileMap_3051_, lean_object* v_parserState_3052_, lean_object* v_a_3053_, lean_object* v___x_3054_, lean_object* v___x_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3046_, v_stx_3047_, v_origStx_3048_, v_toProcessingContext_3049_, v___x_3050_, v_fileMap_3051_, v_parserState_3052_, v_a_3053_, v___x_3054_, v___x_3055_, v___y_3056_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v_a_3053_);
return v_res_3058_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___f_3060_; 
v___x_3059_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3060_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3060_, 0, v___x_3059_);
return v___f_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3061_, lean_object* v_stx_3062_, lean_object* v_origStx_3063_, lean_object* v_parserState_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_toProcessingContext_3067_; lean_object* v_fileMap_3068_; lean_object* v_endPos_3069_; lean_object* v___x_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_toProcessingContext_3067_ = lean_ctor_get(v_a_3065_, 0);
v_fileMap_3068_ = lean_ctor_get(v_toProcessingContext_3067_, 2);
v_endPos_3069_ = lean_ctor_get(v_toProcessingContext_3067_, 3);
v___x_3070_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3071_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3072_ = lean_box(0);
v___x_3073_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3065_, 2);
lean_inc_ref(v_fileMap_3068_);
lean_inc_ref(v_toProcessingContext_3067_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3074_, 0, v_setupImports_3061_);
lean_closure_set(v___f_3074_, 1, v_stx_3062_);
lean_closure_set(v___f_3074_, 2, v_origStx_3063_);
lean_closure_set(v___f_3074_, 3, v_toProcessingContext_3067_);
lean_closure_set(v___f_3074_, 4, v___x_3073_);
lean_closure_set(v___f_3074_, 5, v_fileMap_3068_);
lean_closure_set(v___f_3074_, 6, v_parserState_3064_);
lean_closure_set(v___f_3074_, 7, v_a_3065_);
lean_closure_set(v___f_3074_, 8, v___x_3072_);
lean_closure_set(v___f_3074_, 9, v___x_3070_);
lean_inc(v_endPos_3069_);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v_endPos_3069_);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
v___x_3077_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3077_, 0, lean_box(0));
lean_closure_set(v___x_3077_, 1, v___f_3071_);
lean_closure_set(v___x_3077_, 2, v___f_3074_);
lean_closure_set(v___x_3077_, 3, v_a_3065_);
v___x_3078_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3072_, v___x_3072_, v___x_3076_, v___x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3079_, lean_object* v_stx_3080_, lean_object* v_origStx_3081_, lean_object* v_parserState_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3079_, v_stx_3080_, v_origStx_3081_, v_parserState_3082_, v_a_3083_);
lean_dec_ref(v_a_3083_);
return v_res_3085_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_box(0);
v___x_3089_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3088_);
return v___x_3089_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = 1;
v___x_3095_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3096_ = l_Lean_Name_toString(v___x_3095_, v___x_3094_);
return v___x_3096_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3097_ = 0;
v___x_3098_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3099_ = lean_box(0);
v___x_3100_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3101_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3102_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
lean_ctor_set(v___x_3102_, 1, v___x_3100_);
lean_ctor_set(v___x_3102_, 2, v___x_3099_);
lean_ctor_set(v___x_3102_, 3, v___x_3098_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*4, v___x_3097_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3103_, lean_object* v_cmdState_3104_, lean_object* v_a_3105_, lean_object* v_toSnapshot_3106_, lean_object* v_newStx_3107_, lean_object* v_oldCmd_3108_){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_diagnostics_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3138_; 
v___x_3110_ = lean_io_promise_new();
v___x_3111_ = l_IO_CancelToken_new();
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_oldCmd_3108_);
v___x_3113_ = 1;
v___x_3114_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3111_);
lean_inc(v___x_3110_);
lean_inc_ref(v_cmdState_3104_);
v___x_3115_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3112_, v_newParserState_3103_, v_cmdState_3104_, v___x_3110_, v___x_3113_, v___x_3111_, v___x_3114_, v_a_3105_);
v_diagnostics_3116_ = lean_ctor_get(v_toSnapshot_3106_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_toSnapshot_3106_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; lean_object* v_unused_3140_; lean_object* v_unused_3141_; 
v_unused_3139_ = lean_ctor_get(v_toSnapshot_3106_, 3);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_toSnapshot_3106_, 2);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_toSnapshot_3106_, 0);
lean_dec(v_unused_3141_);
v___x_3118_ = v_toSnapshot_3106_;
v_isShared_3119_ = v_isSharedCheck_3138_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_diagnostics_3116_);
lean_dec(v_toSnapshot_3106_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3138_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3120_ = lean_box(0);
v___x_3121_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3122_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3123_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3111_);
v___x_3125_ = l_IO_Promise_result_x21___redArg(v___x_3110_);
lean_dec(v___x_3110_);
v___x_3126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3120_);
lean_ctor_set(v___x_3126_, 1, v___x_3121_);
lean_ctor_set(v___x_3126_, 2, v___x_3124_);
lean_ctor_set(v___x_3126_, 3, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v_cmdState_3104_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
v___x_3129_ = 0;
v___x_3130_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_newStx_3107_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 3, v___x_3123_);
lean_ctor_set(v___x_3118_, 2, v___x_3120_);
lean_ctor_set(v___x_3118_, 0, v___x_3122_);
v___x_3133_ = v___x_3118_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_diagnostics_3116_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v___x_3123_);
v___x_3133_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*4, v___x_3129_);
v___x_3134_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3131_, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3130_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
lean_ctor_set(v___x_3135_, 2, v___x_3128_);
v___x_3136_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3120_, v___x_3135_);
return v___x_3136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3142_, lean_object* v_cmdState_3143_, lean_object* v_a_3144_, lean_object* v_toSnapshot_3145_, lean_object* v_newStx_3146_, lean_object* v_oldCmd_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3142_, v_cmdState_3143_, v_a_3144_, v_toSnapshot_3145_, v_newStx_3146_, v_oldCmd_3147_);
lean_dec_ref(v_a_3144_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3150_, lean_object* v_a_3151_, lean_object* v_newStx_3152_, lean_object* v___x_3153_, lean_object* v_oldProcessed_3154_){
_start:
{
lean_object* v_result_x3f_3156_; 
v_result_x3f_3156_ = lean_ctor_get(v_oldProcessed_3154_, 2);
if (lean_obj_tag(v_result_x3f_3156_) == 1)
{
lean_object* v_val_3157_; lean_object* v_firstCmdSnap_3158_; lean_object* v_toSnapshot_3159_; lean_object* v_cmdState_3160_; lean_object* v_stx_x3f_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; 
v_val_3157_ = lean_ctor_get(v_result_x3f_3156_, 0);
lean_inc(v_val_3157_);
v_firstCmdSnap_3158_ = lean_ctor_get(v_val_3157_, 1);
lean_inc_ref(v_firstCmdSnap_3158_);
v_toSnapshot_3159_ = lean_ctor_get(v_oldProcessed_3154_, 0);
lean_inc_ref(v_toSnapshot_3159_);
lean_dec_ref(v_oldProcessed_3154_);
v_cmdState_3160_ = lean_ctor_get(v_val_3157_, 0);
lean_inc_ref(v_cmdState_3160_);
lean_dec(v_val_3157_);
v_stx_x3f_3161_ = lean_ctor_get(v_firstCmdSnap_3158_, 0);
lean_inc(v_stx_x3f_3161_);
lean_inc_ref(v_a_3151_);
v___f_3162_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3162_, 0, v_newParserState_3150_);
lean_closure_set(v___f_3162_, 1, v_cmdState_3160_);
lean_closure_set(v___f_3162_, 2, v_a_3151_);
lean_closure_set(v___f_3162_, 3, v_toSnapshot_3159_);
lean_closure_set(v___f_3162_, 4, v_newStx_3152_);
v___x_3163_ = lean_box(0);
v___x_3164_ = 1;
v___x_3165_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3158_, v___f_3162_, v_stx_x3f_3161_, v___x_3153_, v___x_3163_, v___x_3164_);
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec(v___x_3153_);
lean_dec_ref(v_newParserState_3150_);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_newStx_3152_);
v___x_3167_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3166_, v_oldProcessed_3154_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3168_, lean_object* v_a_3169_, lean_object* v_newStx_3170_, lean_object* v___x_3171_, lean_object* v_oldProcessed_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3168_, v_a_3169_, v_newStx_3170_, v___x_3171_, v_oldProcessed_3172_);
lean_dec_ref(v_a_3169_);
return v_res_3174_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3175_ = 0;
v___x_3176_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3177_ = lean_box(0);
v___x_3178_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3179_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3180_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v___x_3178_);
lean_ctor_set(v___x_3180_, 2, v___x_3177_);
lean_ctor_set(v___x_3180_, 3, v___x_3176_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*4, v___x_3175_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3181_, lean_object* v_a_3182_, lean_object* v_old_3183_, lean_object* v_newStx_3184_, lean_object* v_newParserState_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_result_x3f_3188_; 
v_result_x3f_3188_ = lean_ctor_get(v_old_3183_, 4);
lean_inc(v_result_x3f_3188_);
if (lean_obj_tag(v_result_x3f_3188_) == 1)
{
lean_object* v_val_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3243_; 
v_val_3189_ = lean_ctor_get(v_result_x3f_3188_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_result_x3f_3188_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3191_ = v_result_x3f_3188_;
v_isShared_3192_ = v_isSharedCheck_3243_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_val_3189_);
lean_dec(v_result_x3f_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3243_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v_processedSnap_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3241_; 
v_processedSnap_3193_ = lean_ctor_get(v_val_3189_, 1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_val_3189_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v_val_3189_, 0);
lean_dec(v_unused_3242_);
v___x_3195_ = v_val_3189_;
v_isShared_3196_ = v_isSharedCheck_3241_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_processedSnap_3193_);
lean_dec(v_val_3189_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3241_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_toSnapshot_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3236_; 
v_toSnapshot_3197_ = lean_ctor_get(v_old_3183_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_old_3183_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; lean_object* v_unused_3238_; lean_object* v_unused_3239_; lean_object* v_unused_3240_; 
v_unused_3237_ = lean_ctor_get(v_old_3183_, 4);
lean_dec(v_unused_3237_);
v_unused_3238_ = lean_ctor_get(v_old_3183_, 3);
lean_dec(v_unused_3238_);
v_unused_3239_ = lean_ctor_get(v_old_3183_, 2);
lean_dec(v_unused_3239_);
v_unused_3240_ = lean_ctor_get(v_old_3183_, 1);
lean_dec(v_unused_3240_);
v___x_3199_ = v_old_3183_;
v_isShared_3200_ = v_isSharedCheck_3236_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_toSnapshot_3197_);
lean_dec(v_old_3183_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3236_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_pos_3201_; lean_object* v_endPos_3202_; lean_object* v_stx_x3f_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v_diagnostics_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3232_; 
v_pos_3201_ = lean_ctor_get(v_newParserState_3185_, 0);
v_endPos_3202_ = lean_ctor_get(v_toProcessingContext_3181_, 3);
v_stx_x3f_3203_ = lean_ctor_get(v_processedSnap_3193_, 0);
lean_inc(v_stx_x3f_3203_);
lean_inc(v_endPos_3202_);
lean_inc(v_pos_3201_);
v___x_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3204_, 0, v_pos_3201_);
lean_ctor_set(v___x_3204_, 1, v_endPos_3202_);
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_inc_ref(v___x_3205_);
lean_inc(v_newStx_3184_);
lean_inc_ref(v_a_3182_);
lean_inc_ref(v_newParserState_3185_);
v___f_3206_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3206_, 0, v_newParserState_3185_);
lean_closure_set(v___f_3206_, 1, v_a_3182_);
lean_closure_set(v___f_3206_, 2, v_newStx_3184_);
lean_closure_set(v___f_3206_, 3, v___x_3205_);
v___x_3207_ = lean_box(0);
v___x_3208_ = 1;
v___x_3209_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3193_, v___f_3206_, v_stx_x3f_3203_, v___x_3205_, v___x_3207_, v___x_3208_);
v_diagnostics_3210_ = lean_ctor_get(v_toSnapshot_3197_, 1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_toSnapshot_3197_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; lean_object* v_unused_3235_; 
v_unused_3233_ = lean_ctor_get(v_toSnapshot_3197_, 3);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_toSnapshot_3197_, 2);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_toSnapshot_3197_, 0);
lean_dec(v_unused_3235_);
v___x_3212_ = v_toSnapshot_3197_;
v_isShared_3213_ = v_isSharedCheck_3232_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_diagnostics_3210_);
lean_dec(v_toSnapshot_3197_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3232_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3215_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v___x_3209_);
lean_ctor_set(v___x_3195_, 0, v_newParserState_3185_);
v___x_3217_ = v___x_3195_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_newParserState_3185_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3209_);
v___x_3217_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3217_);
v___x_3219_ = v___x_3191_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3220_ = 0;
v___x_3221_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3184_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_newStx_3184_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 3, v___x_3215_);
lean_ctor_set(v___x_3212_, 2, v___x_3207_);
lean_ctor_set(v___x_3212_, 0, v___x_3214_);
v___x_3224_ = v___x_3212_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_diagnostics_3210_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v___x_3215_);
v___x_3224_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*4, v___x_3220_);
v___x_3225_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3222_, v___x_3224_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 4, v___x_3219_);
lean_ctor_set(v___x_3199_, 3, v_newStx_3184_);
lean_ctor_set(v___x_3199_, 2, v_toProcessingContext_3181_);
lean_ctor_set(v___x_3199_, 1, v___x_3225_);
lean_ctor_set(v___x_3199_, 0, v___x_3221_);
v___x_3227_ = v___x_3199_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_toProcessingContext_3181_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_newStx_3184_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v___x_3219_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
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
lean_dec(v_result_x3f_3188_);
lean_dec_ref(v_newParserState_3185_);
lean_dec(v_newStx_3184_);
lean_dec_ref(v_toProcessingContext_3181_);
return v_old_3183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3244_, lean_object* v_a_3245_, lean_object* v_old_3246_, lean_object* v_newStx_3247_, lean_object* v_newParserState_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3244_, v_a_3245_, v_old_3246_, v_newStx_3247_, v_newParserState_3248_, v___y_3249_);
lean_dec_ref(v___y_3249_);
lean_dec_ref(v_a_3245_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3252_, lean_object* v_setupImports_3253_, lean_object* v_old_x3f_3254_, lean_object* v___f_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___x_3258_; 
lean_inc_ref(v_toProcessingContext_3252_);
v___x_3258_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3252_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3328_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3328_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3328_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v_snd_3263_; lean_object* v_fst_3264_; lean_object* v_fst_3265_; lean_object* v_snd_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3327_; 
v_snd_3263_ = lean_ctor_get(v_a_3259_, 1);
lean_inc(v_snd_3263_);
v_fst_3264_ = lean_ctor_get(v_a_3259_, 0);
lean_inc(v_fst_3264_);
lean_dec(v_a_3259_);
v_fst_3265_ = lean_ctor_get(v_snd_3263_, 0);
v_snd_3266_ = lean_ctor_get(v_snd_3263_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_snd_3263_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3268_ = v_snd_3263_;
v_isShared_3269_ = v_isSharedCheck_3327_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_snd_3266_);
lean_inc(v_fst_3265_);
lean_dec(v_snd_3263_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3327_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
uint8_t v___x_3270_; 
v___x_3270_ = l_Lean_MessageLog_hasErrors(v_snd_3266_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___y_3273_; 
lean_inc(v_fst_3264_);
v___x_3271_ = l_Lean_Syntax_unsetTrailing(v_fst_3264_);
if (lean_obj_tag(v_old_x3f_3254_) == 1)
{
lean_object* v_val_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3310_; 
v_val_3294_ = lean_ctor_get(v_old_x3f_3254_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_old_x3f_3254_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3296_ = v_old_x3f_3254_;
v_isShared_3297_ = v_isSharedCheck_3310_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_val_3294_);
lean_dec(v_old_x3f_3254_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3310_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_stx_3298_; lean_object* v_result_x3f_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v_stx_3298_ = lean_ctor_get(v_val_3294_, 3);
v_result_x3f_3299_ = lean_ctor_get(v_val_3294_, 4);
lean_inc(v_stx_3298_);
v___x_3300_ = l_Lean_Syntax_unsetTrailing(v_stx_3298_);
lean_inc(v___x_3271_);
v___x_3301_ = l_Lean_Syntax_eqWithInfo(v___x_3271_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_inc(v_result_x3f_3299_);
lean_del_object(v___x_3296_);
lean_dec(v_val_3294_);
lean_dec_ref(v___f_3255_);
if (lean_obj_tag(v_result_x3f_3299_) == 0)
{
v___y_3273_ = v___y_3256_;
goto v___jp_3272_;
}
else
{
lean_object* v_val_3302_; lean_object* v_processedSnap_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_val_3302_ = lean_ctor_get(v_result_x3f_3299_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v_result_x3f_3299_, 1);
v_processedSnap_3303_ = lean_ctor_get(v_val_3302_, 1);
lean_inc_ref(v_processedSnap_3303_);
lean_dec(v_val_3302_);
v___x_3304_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3305_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3304_, v_processedSnap_3303_);
v___y_3273_ = v___y_3256_;
goto v___jp_3272_;
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_dec(v___x_3271_);
lean_del_object(v___x_3268_);
lean_dec(v_snd_3266_);
lean_del_object(v___x_3261_);
lean_dec_ref(v_setupImports_3253_);
lean_dec_ref(v_toProcessingContext_3252_);
lean_inc_ref(v___y_3256_);
v___x_3306_ = lean_apply_5(v___f_3255_, v_val_3294_, v_fst_3264_, v_fst_3265_, v___y_3256_, lean_box(0));
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3306_);
v___x_3308_ = v___x_3296_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_dec_ref(v___f_3255_);
lean_dec(v_old_x3f_3254_);
v___y_3273_ = v___y_3256_;
goto v___jp_3272_;
}
v___jp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3274_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3266_);
lean_inc(v_fst_3265_);
lean_inc(v_fst_3264_);
v___x_3275_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3253_, v___x_3271_, v_fst_3264_, v_fst_3265_, v___y_3273_);
v___x_3276_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3277_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_unsigned_to_nat(32u);
v___x_3280_ = lean_mk_empty_array_with_capacity(v___x_3279_);
lean_dec_ref(v___x_3280_);
v___x_3281_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 1, v___x_3275_);
v___x_3283_ = v___x_3268_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_fst_3265_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3275_);
v___x_3283_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3285_, 0, v___x_3276_);
lean_ctor_set(v___x_3285_, 1, v___x_3277_);
lean_ctor_set(v___x_3285_, 2, v___x_3278_);
lean_ctor_set(v___x_3285_, 3, v___x_3281_);
lean_ctor_set_uint8(v___x_3285_, sizeof(void*)*4, v___x_3270_);
lean_inc(v_fst_3264_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_fst_3264_);
v___x_3287_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3287_, 0, v___x_3276_);
lean_ctor_set(v___x_3287_, 1, v___x_3274_);
lean_ctor_set(v___x_3287_, 2, v___x_3278_);
lean_ctor_set(v___x_3287_, 3, v___x_3281_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*4, v___x_3270_);
v___x_3288_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3286_, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3285_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
lean_ctor_set(v___x_3289_, 2, v_toProcessingContext_3252_);
lean_ctor_set(v___x_3289_, 3, v_fst_3264_);
lean_ctor_set(v___x_3289_, 4, v___x_3284_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3289_);
v___x_3291_ = v___x_3261_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3325_; 
lean_del_object(v___x_3268_);
lean_dec(v_fst_3265_);
lean_dec_ref(v___f_3255_);
lean_dec(v_old_x3f_3254_);
lean_dec_ref(v_setupImports_3253_);
v___x_3311_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3266_);
v___x_3312_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3313_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3314_ = lean_box(0);
v___x_3315_ = lean_unsigned_to_nat(32u);
v___x_3316_ = lean_mk_empty_array_with_capacity(v___x_3315_);
lean_dec_ref(v___x_3316_);
v___x_3317_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3318_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3318_, 0, v___x_3312_);
lean_ctor_set(v___x_3318_, 1, v___x_3313_);
lean_ctor_set(v___x_3318_, 2, v___x_3314_);
lean_ctor_set(v___x_3318_, 3, v___x_3317_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*4, v___x_3270_);
lean_inc(v_fst_3264_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_fst_3264_);
v___x_3320_ = 0;
v___x_3321_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3321_, 0, v___x_3312_);
lean_ctor_set(v___x_3321_, 1, v___x_3311_);
lean_ctor_set(v___x_3321_, 2, v___x_3314_);
lean_ctor_set(v___x_3321_, 3, v___x_3317_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*4, v___x_3320_);
v___x_3322_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3319_, v___x_3321_);
v___x_3323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3318_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
lean_ctor_set(v___x_3323_, 2, v_toProcessingContext_3252_);
lean_ctor_set(v___x_3323_, 3, v_fst_3264_);
lean_ctor_set(v___x_3323_, 4, v___x_3314_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3323_);
v___x_3325_ = v___x_3261_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v___f_3255_);
lean_dec(v_old_x3f_3254_);
lean_dec_ref(v_setupImports_3253_);
lean_dec_ref(v_toProcessingContext_3252_);
v_a_3329_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3258_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3258_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3337_, lean_object* v_setupImports_3338_, lean_object* v_old_x3f_3339_, lean_object* v___f_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3337_, v_setupImports_3338_, v_old_x3f_3339_, v___f_3340_, v___y_3341_);
lean_dec_ref(v___y_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3344_, lean_object* v_toProcessingContext_3345_, lean_object* v_x_3346_){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3347_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3344_);
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3350_, 0, v_x_3346_);
lean_ctor_set(v___x_3350_, 1, v___x_3347_);
lean_ctor_set(v___x_3350_, 2, v_toProcessingContext_3345_);
lean_ctor_set(v___x_3350_, 3, v___x_3348_);
lean_ctor_set(v___x_3350_, 4, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3351_, lean_object* v_old_x3f_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_toProcessingContext_3355_; lean_object* v___x_3356_; lean_object* v___f_3357_; lean_object* v___f_3358_; lean_object* v___f_3359_; 
v_toProcessingContext_3355_ = lean_ctor_get(v_a_3353_, 0);
v___x_3356_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3353_);
lean_inc_ref_n(v_toProcessingContext_3355_, 3);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3357_, 0, v_toProcessingContext_3355_);
lean_closure_set(v___f_3357_, 1, v_a_3353_);
lean_inc(v_old_x3f_3352_);
v___f_3358_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3358_, 0, v_toProcessingContext_3355_);
lean_closure_set(v___f_3358_, 1, v_setupImports_3351_);
lean_closure_set(v___f_3358_, 2, v_old_x3f_3352_);
lean_closure_set(v___f_3358_, 3, v___f_3357_);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3359_, 0, v___x_3356_);
lean_closure_set(v___f_3359_, 1, v_toProcessingContext_3355_);
if (lean_obj_tag(v_old_x3f_3352_) == 1)
{
lean_object* v_val_3360_; lean_object* v_result_x3f_3361_; 
v_val_3360_ = lean_ctor_get(v_old_x3f_3352_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v_old_x3f_3352_, 1);
v_result_x3f_3361_ = lean_ctor_get(v_val_3360_, 4);
if (lean_obj_tag(v_result_x3f_3361_) == 1)
{
lean_object* v_stx_3362_; lean_object* v_val_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_stx_3362_ = lean_ctor_get(v_val_3360_, 3);
lean_inc(v_stx_3362_);
v_val_3363_ = lean_ctor_get(v_result_x3f_3361_, 0);
lean_inc(v_val_3360_);
v___x_3364_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3360_);
v___x_3365_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3364_);
if (lean_obj_tag(v___x_3365_) == 1)
{
lean_object* v_val_3366_; 
v_val_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3366_);
lean_dec_ref_known(v___x_3365_, 1);
if (lean_obj_tag(v_val_3366_) == 1)
{
lean_object* v_val_3367_; lean_object* v_firstCmdSnap_3368_; lean_object* v___x_3369_; 
v_val_3367_ = lean_ctor_get(v_val_3366_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v_val_3366_, 1);
v_firstCmdSnap_3368_ = lean_ctor_get(v_val_3367_, 1);
lean_inc_ref(v_firstCmdSnap_3368_);
lean_dec(v_val_3367_);
v___x_3369_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3368_);
if (lean_obj_tag(v___x_3369_) == 1)
{
lean_object* v_val_3370_; lean_object* v_nextCmdSnap_x3f_3371_; 
v_val_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v_nextCmdSnap_x3f_3371_ = lean_ctor_get(v_val_3370_, 4);
lean_inc(v_nextCmdSnap_x3f_3371_);
lean_dec(v_val_3370_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3372_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3374_; 
v_val_3373_ = lean_ctor_get(v_nextCmdSnap_x3f_3371_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3371_, 1);
v___x_3374_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3373_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; lean_object* v_parserState_3376_; lean_object* v_pos_3377_; uint8_t v___x_3378_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v_parserState_3376_ = lean_ctor_get(v_val_3375_, 2);
lean_inc_ref(v_parserState_3376_);
lean_dec(v_val_3375_);
v_pos_3377_ = lean_ctor_get(v_parserState_3376_, 0);
lean_inc(v_pos_3377_);
lean_dec_ref(v_parserState_3376_);
v___x_3378_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3377_, v_a_3353_);
lean_dec(v_pos_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3379_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3379_;
}
else
{
lean_object* v_parserState_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v___f_3359_);
lean_dec_ref(v___f_3358_);
v_parserState_3380_ = lean_ctor_get(v_val_3363_, 0);
lean_inc_ref(v_parserState_3380_);
lean_inc_ref(v_toProcessingContext_3355_);
v___x_3381_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3355_, v_a_3353_, v_val_3360_, v_stx_3362_, v_parserState_3380_, v_a_3353_);
return v___x_3381_;
}
}
else
{
lean_object* v___x_3382_; 
lean_dec(v___x_3374_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3382_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3382_;
}
}
}
else
{
lean_object* v___x_3383_; 
lean_dec(v___x_3369_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3383_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3383_;
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v_val_3366_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3384_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3384_;
}
}
else
{
lean_object* v___x_3385_; 
lean_dec(v___x_3365_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3385_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3385_;
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v_val_3360_);
v___x_3386_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3386_;
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v_old_x3f_3352_);
v___x_3387_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3353_);
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3388_, lean_object* v_old_x3f_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3388_, v_old_x3f_3389_, v_a_3390_);
lean_dec_ref(v_a_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3393_, lean_object* v_old_x3f_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3397_; 
lean_inc(v_old_x3f_3394_);
v___x_3397_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3397_, 0, v_setupImports_3393_);
lean_closure_set(v___x_3397_, 1, v_old_x3f_3394_);
if (lean_obj_tag(v_old_x3f_3394_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_box(0);
v___x_3399_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3397_, v___x_3398_, v_a_3395_);
return v___x_3399_;
}
else
{
lean_object* v_val_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3409_; 
v_val_3400_ = lean_ctor_get(v_old_x3f_3394_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_old_x3f_3394_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3402_ = v_old_x3f_3394_;
v_isShared_3403_ = v_isSharedCheck_3409_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_val_3400_);
lean_dec(v_old_x3f_3394_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3409_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v_ictx_3404_; lean_object* v___x_3406_; 
v_ictx_3404_ = lean_ctor_get(v_val_3400_, 2);
lean_inc_ref(v_ictx_3404_);
lean_dec(v_val_3400_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v_ictx_3404_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_ictx_3404_);
v___x_3406_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3397_, v___x_3406_, v_a_3395_);
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3410_, lean_object* v_old_x3f_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_Language_Lean_process(v_setupImports_3410_, v_old_x3f_3411_, v_a_3412_);
lean_dec_ref(v_a_3412_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3415_, lean_object* v_parserState_3416_, lean_object* v_commandState_3417_, lean_object* v_old_x3f_3418_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3428_; 
v___x_3420_ = lean_io_promise_new();
v___x_3421_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3418_) == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_box(0);
v___y_3428_ = v___x_3443_;
goto v___jp_3427_;
}
else
{
lean_object* v_val_3444_; lean_object* v_snd_3445_; lean_object* v___x_3446_; 
v_val_3444_ = lean_ctor_get(v_old_x3f_3418_, 0);
v_snd_3445_ = lean_ctor_get(v_val_3444_, 1);
lean_inc(v_snd_3445_);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_snd_3445_);
v___y_3428_ = v___x_3446_;
goto v___jp_3427_;
}
v___jp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3423_, v___y_3424_, v_inputCtx_3415_);
lean_dec(v___x_3425_);
v___x_3426_ = l_IO_Promise_result_x21___redArg(v___x_3420_);
lean_dec(v___x_3420_);
return v___x_3426_;
}
v___jp_3427_:
{
uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3429_ = 1;
v___x_3430_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
v___x_3431_ = lean_box(v___x_3429_);
lean_inc(v___x_3420_);
v___x_3432_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3432_, 0, v___y_3428_);
lean_closure_set(v___x_3432_, 1, v_parserState_3416_);
lean_closure_set(v___x_3432_, 2, v_commandState_3417_);
lean_closure_set(v___x_3432_, 3, v___x_3420_);
lean_closure_set(v___x_3432_, 4, v___x_3431_);
lean_closure_set(v___x_3432_, 5, v___x_3421_);
lean_closure_set(v___x_3432_, 6, v___x_3430_);
if (lean_obj_tag(v_old_x3f_3418_) == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_box(0);
v___y_3423_ = v___x_3432_;
v___y_3424_ = v___x_3433_;
goto v___jp_3422_;
}
else
{
lean_object* v_val_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3442_; 
v_val_3434_ = lean_ctor_get(v_old_x3f_3418_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_old_x3f_3418_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3436_ = v_old_x3f_3418_;
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_val_3434_);
lean_dec(v_old_x3f_3418_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_fst_3438_; lean_object* v___x_3440_; 
v_fst_3438_ = lean_ctor_get(v_val_3434_, 0);
lean_inc(v_fst_3438_);
lean_dec(v_val_3434_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v_fst_3438_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_fst_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
v___y_3423_ = v___x_3432_;
v___y_3424_ = v___x_3440_;
goto v___jp_3422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3447_, lean_object* v_parserState_3448_, lean_object* v_commandState_3449_, lean_object* v_old_x3f_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3447_, v_parserState_3448_, v_commandState_3449_, v_old_x3f_3450_);
lean_dec_ref(v_inputCtx_3447_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3453_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3454_; 
v_nextCmdSnap_x3f_3454_ = lean_ctor_get(v_snap_3453_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3454_) == 1)
{
lean_object* v_val_3455_; lean_object* v___x_3456_; 
lean_inc_ref(v_nextCmdSnap_x3f_3454_);
lean_dec_ref(v_snap_3453_);
v_val_3455_ = lean_ctor_get(v_nextCmdSnap_x3f_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3454_, 1);
v___x_3456_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3455_);
v_snap_3453_ = v___x_3456_;
goto _start;
}
else
{
lean_object* v_elabSnap_3458_; lean_object* v_resultSnap_3459_; lean_object* v___x_3460_; lean_object* v_cmdState_3461_; lean_object* v___x_3462_; 
v_elabSnap_3458_ = lean_ctor_get(v_snap_3453_, 3);
lean_inc_ref(v_elabSnap_3458_);
lean_dec_ref(v_snap_3453_);
v_resultSnap_3459_ = lean_ctor_get(v_elabSnap_3458_, 2);
lean_inc_ref(v_resultSnap_3459_);
lean_dec_ref(v_elabSnap_3458_);
v___x_3460_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3459_);
v_cmdState_3461_ = lean_ctor_get(v___x_3460_, 1);
lean_inc_ref(v_cmdState_3461_);
lean_dec(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_cmdState_3461_);
return v___x_3462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3463_){
_start:
{
lean_object* v_result_x3f_3464_; 
v_result_x3f_3464_ = lean_ctor_get(v_snap_3463_, 4);
lean_inc(v_result_x3f_3464_);
lean_dec_ref(v_snap_3463_);
if (lean_obj_tag(v_result_x3f_3464_) == 0)
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_box(0);
return v___x_3465_;
}
else
{
lean_object* v_val_3466_; lean_object* v_processedSnap_3467_; lean_object* v___x_3468_; lean_object* v_result_x3f_3469_; 
v_val_3466_ = lean_ctor_get(v_result_x3f_3464_, 0);
lean_inc(v_val_3466_);
lean_dec_ref_known(v_result_x3f_3464_, 1);
v_processedSnap_3467_ = lean_ctor_get(v_val_3466_, 1);
lean_inc_ref(v_processedSnap_3467_);
lean_dec(v_val_3466_);
v___x_3468_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3467_);
v_result_x3f_3469_ = lean_ctor_get(v___x_3468_, 2);
lean_inc(v_result_x3f_3469_);
lean_dec(v___x_3468_);
if (lean_obj_tag(v_result_x3f_3469_) == 0)
{
lean_object* v___x_3470_; 
v___x_3470_ = lean_box(0);
return v___x_3470_;
}
else
{
lean_object* v_val_3471_; lean_object* v_firstCmdSnap_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_val_3471_ = lean_ctor_get(v_result_x3f_3469_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v_result_x3f_3469_, 1);
v_firstCmdSnap_3472_ = lean_ctor_get(v_val_3471_, 1);
lean_inc_ref(v_firstCmdSnap_3472_);
lean_dec(v_val_3471_);
v___x_3473_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3472_);
v___x_3474_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3473_);
return v___x_3474_;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = 1;
v___x_3481_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3482_ = l_Lean_Name_toString(v___x_3481_, v___x_3480_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3483_ = 0;
v___x_3484_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3485_ = lean_box(0);
v___x_3486_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3487_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3488_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3486_);
lean_ctor_set(v___x_3488_, 2, v___x_3485_);
lean_ctor_set(v___x_3488_, 3, v___x_3484_);
lean_ctor_set_uint8(v___x_3488_, sizeof(void*)*4, v___x_3483_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3490_ = lean_box(0);
v___x_3491_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3490_, v___x_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3492_){
_start:
{
lean_object* v_result_x3f_3493_; 
v_result_x3f_3493_ = lean_ctor_get(v_snap_3492_, 4);
lean_inc(v_result_x3f_3493_);
if (lean_obj_tag(v_result_x3f_3493_) == 1)
{
lean_object* v_val_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3568_; 
v_val_3494_ = lean_ctor_get(v_result_x3f_3493_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_result_x3f_3493_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3496_ = v_result_x3f_3493_;
v_isShared_3497_ = v_isSharedCheck_3568_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_val_3494_);
lean_dec(v_result_x3f_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3568_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v_toSnapshot_3498_; lean_object* v_metaSnap_3499_; lean_object* v_ictx_3500_; lean_object* v_stx_3501_; lean_object* v_parserState_3502_; lean_object* v_processedSnap_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3567_; 
v_toSnapshot_3498_ = lean_ctor_get(v_snap_3492_, 0);
v_metaSnap_3499_ = lean_ctor_get(v_snap_3492_, 1);
v_ictx_3500_ = lean_ctor_get(v_snap_3492_, 2);
v_stx_3501_ = lean_ctor_get(v_snap_3492_, 3);
v_parserState_3502_ = lean_ctor_get(v_val_3494_, 0);
v_processedSnap_3503_ = lean_ctor_get(v_val_3494_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_val_3494_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3505_ = v_val_3494_;
v_isShared_3506_ = v_isSharedCheck_3567_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_processedSnap_3503_);
lean_inc(v_parserState_3502_);
lean_dec(v_val_3494_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3567_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_processed_3507_; lean_object* v_result_x3f_3508_; 
v_processed_3507_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3503_);
v_result_x3f_3508_ = lean_ctor_get(v_processed_3507_, 2);
lean_inc(v_result_x3f_3508_);
if (lean_obj_tag(v_result_x3f_3508_) == 1)
{
lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3561_; 
lean_inc(v_stx_3501_);
lean_inc_ref(v_ictx_3500_);
lean_inc_ref(v_metaSnap_3499_);
lean_inc_ref(v_toSnapshot_3498_);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_snap_3492_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; lean_object* v_unused_3566_; 
v_unused_3562_ = lean_ctor_get(v_snap_3492_, 4);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_snap_3492_, 3);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_snap_3492_, 2);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_snap_3492_, 1);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_snap_3492_, 0);
lean_dec(v_unused_3566_);
v___x_3510_ = v_snap_3492_;
v_isShared_3511_ = v_isSharedCheck_3561_;
goto v_resetjp_3509_;
}
else
{
lean_dec(v_snap_3492_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3561_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_val_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3560_; 
v_val_3512_ = lean_ctor_get(v_result_x3f_3508_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_result_x3f_3508_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3514_ = v_result_x3f_3508_;
v_isShared_3515_ = v_isSharedCheck_3560_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_val_3512_);
lean_dec(v_result_x3f_3508_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3560_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_toSnapshot_3516_; lean_object* v_metaSnap_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3558_; 
v_toSnapshot_3516_ = lean_ctor_get(v_processed_3507_, 0);
v_metaSnap_3517_ = lean_ctor_get(v_processed_3507_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_processed_3507_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v_processed_3507_, 2);
lean_dec(v_unused_3559_);
v___x_3519_ = v_processed_3507_;
v_isShared_3520_ = v_isSharedCheck_3558_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_metaSnap_3517_);
lean_inc(v_toSnapshot_3516_);
lean_dec(v_processed_3507_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3558_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_cmdState_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3556_; 
v_cmdState_3521_ = lean_ctor_get(v_val_3512_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_val_3512_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v_val_3512_, 1);
lean_dec(v_unused_3557_);
v___x_3523_ = v_val_3512_;
v_isShared_3524_ = v_isSharedCheck_3556_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_cmdState_3521_);
lean_dec(v_val_3512_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3556_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_resultSnap_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v_elabSnap_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v_termCmd_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
lean_inc_ref(v_cmdState_3521_);
v_resultSnap_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_resultSnap_3527_, 0, v___x_3526_);
lean_ctor_set(v_resultSnap_3527_, 1, v_cmdState_3521_);
v___x_3528_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
v___x_3529_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3525_, v_resultSnap_3527_);
v___x_3530_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3531_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v_elabSnap_3532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3532_, 0, v___x_3526_);
lean_ctor_set(v_elabSnap_3532_, 1, v___x_3528_);
lean_ctor_set(v_elabSnap_3532_, 2, v___x_3529_);
lean_ctor_set(v_elabSnap_3532_, 3, v___x_3530_);
lean_ctor_set(v_elabSnap_3532_, 4, v___x_3531_);
v___x_3533_ = lean_box(0);
v___x_3534_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3535_, 0, v___x_3526_);
lean_ctor_set(v_termCmd_3535_, 1, v___x_3533_);
lean_ctor_set(v_termCmd_3535_, 2, v___x_3534_);
lean_ctor_set(v_termCmd_3535_, 3, v_elabSnap_3532_);
lean_ctor_set(v_termCmd_3535_, 4, v___x_3525_);
v___x_3536_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3525_, v_termCmd_3535_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 1, v___x_3536_);
v___x_3538_ = v___x_3523_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_cmdState_3521_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3540_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3538_);
v___x_3540_ = v___x_3514_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v_newProcessed_3542_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 2, v___x_3540_);
v_newProcessed_3542_ = v___x_3519_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_toSnapshot_3516_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_metaSnap_3517_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v___x_3540_);
v_newProcessed_3542_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3525_, v_newProcessed_3542_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3543_);
v___x_3545_ = v___x_3505_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_parserState_3502_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3547_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3545_);
v___x_3547_ = v___x_3496_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3549_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 4, v___x_3547_);
v___x_3549_ = v___x_3510_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_toSnapshot_3498_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_metaSnap_3499_);
lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_ictx_3500_);
lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_stx_3501_);
lean_ctor_set(v_reuseFailAlloc_3550_, 4, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
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
lean_dec(v_result_x3f_3508_);
lean_dec(v_processed_3507_);
lean_del_object(v___x_3505_);
lean_dec_ref(v_parserState_3502_);
lean_del_object(v___x_3496_);
return v_snap_3492_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3493_);
return v_snap_3492_;
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

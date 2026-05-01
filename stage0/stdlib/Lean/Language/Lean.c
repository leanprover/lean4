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
lean_dec_ref(v___x_562_);
if (lean_obj_tag(v_val_564_) == 1)
{
uint8_t v_v_565_; 
v_v_565_ = lean_ctor_get_uint8(v_val_564_, 0);
lean_dec_ref(v_val_564_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_585_);
lean_dec_ref(v___x_587_);
v___x_588_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_583_, v___y_584_, v___y_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_593_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_594_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_ctor_set(v___x_599_, 2, v___x_598_);
lean_ctor_set(v___x_599_, 3, v___x_598_);
lean_ctor_set(v___x_599_, 4, v___x_597_);
lean_ctor_set(v___x_599_, 5, v___x_597_);
lean_ctor_set(v___x_599_, 6, v___x_597_);
lean_ctor_set(v___x_599_, 7, v___x_597_);
lean_ctor_set(v___x_599_, 8, v___x_597_);
lean_ctor_set(v___x_599_, 9, v___x_597_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(32u);
v___x_601_ = lean_mk_empty_array_with_capacity(v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_unsigned_to_nat(32u);
v___x_606_ = lean_mk_empty_array_with_capacity(v___x_605_);
v___x_607_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_608_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
lean_ctor_set(v___x_608_, 2, v___x_604_);
lean_ctor_set(v___x_608_, 3, v___x_604_);
lean_ctor_set_usize(v___x_608_, 4, v___x_603_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_box(1);
v___x_610_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
lean_ctor_set(v___x_612_, 2, v___x_609_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v_env_617_; lean_object* v___x_618_; lean_object* v_scopes_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_opts_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_616_ = lean_st_ref_get(v___y_614_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
v___x_618_ = lean_st_ref_get(v___y_614_);
v_scopes_619_ = lean_ctor_get(v___x_618_, 2);
lean_inc(v_scopes_619_);
lean_dec(v___x_618_);
v___x_620_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_621_ = l_List_head_x21___redArg(v___x_620_, v_scopes_619_);
lean_dec(v_scopes_619_);
v_opts_622_ = lean_ctor_get(v___x_621_, 1);
lean_inc_ref(v_opts_622_);
lean_dec(v___x_621_);
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_625_, 0, v_env_617_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_ctor_set(v___x_625_, 3, v_opts_622_);
v___x_626_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_msgData_613_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_628_, v___y_629_);
lean_dec(v___y_629_);
return v_res_631_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_632_, uint8_t v_suppressElabErrors_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 1)
{
lean_object* v_pre_635_; 
v_pre_635_ = lean_ctor_get(v_x_634_, 0);
if (lean_obj_tag(v_pre_635_) == 0)
{
lean_object* v_str_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_str_636_ = lean_ctor_get(v_x_634_, 1);
v___x_637_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_638_ = lean_string_dec_eq(v_str_636_, v___x_637_);
if (v___x_638_ == 0)
{
return v___y_632_;
}
else
{
return v_suppressElabErrors_633_;
}
}
else
{
return v___y_632_;
}
}
else
{
return v___y_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_639_, lean_object* v_suppressElabErrors_640_, lean_object* v_x_641_){
_start:
{
uint8_t v___y_9164__boxed_642_; uint8_t v_suppressElabErrors_boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v___y_9164__boxed_642_ = lean_unbox(v___y_639_);
v_suppressElabErrors_boxed_643_ = lean_unbox(v_suppressElabErrors_640_);
v_res_644_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9164__boxed_642_, v_suppressElabErrors_boxed_643_, v_x_641_);
lean_dec(v_x_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_647_, lean_object* v_msgData_648_, uint8_t v_severity_649_, uint8_t v_isSilent_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; uint8_t v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; uint8_t v___y_754_; uint8_t v___y_755_; uint8_t v___y_756_; uint8_t v___x_771_; uint8_t v___y_773_; uint8_t v___y_774_; uint8_t v___y_775_; uint8_t v___y_777_; uint8_t v___x_789_; 
v___x_771_ = 2;
v___x_789_ = l_Lean_instBEqMessageSeverity_beq(v_severity_649_, v___x_771_);
if (v___x_789_ == 0)
{
v___y_777_ = v___x_789_;
goto v___jp_776_;
}
else
{
uint8_t v___x_790_; 
lean_inc_ref(v_msgData_648_);
v___x_790_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_648_);
v___y_777_ = v___x_790_;
goto v___jp_776_;
}
v___jp_654_:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Elab_Command_getScope___redArg(v___y_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref(v___x_663_);
v___x_665_ = l_Lean_Elab_Command_getScope___redArg(v___y_662_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_700_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_700_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_700_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_700_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v_currNamespace_671_; lean_object* v_openDecls_672_; lean_object* v_env_673_; lean_object* v_messages_674_; lean_object* v_scopes_675_; lean_object* v_usedQuotCtxts_676_; lean_object* v_nextMacroScope_677_; lean_object* v_maxRecDepth_678_; lean_object* v_ngen_679_; lean_object* v_auxDeclNGen_680_; lean_object* v_infoState_681_; lean_object* v_traceState_682_; lean_object* v_snapshotTasks_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_699_; 
v___x_670_ = lean_st_ref_take(v___y_662_);
v_currNamespace_671_ = lean_ctor_get(v_a_664_, 2);
lean_inc(v_currNamespace_671_);
lean_dec(v_a_664_);
v_openDecls_672_ = lean_ctor_get(v_a_666_, 3);
lean_inc(v_openDecls_672_);
lean_dec(v_a_666_);
v_env_673_ = lean_ctor_get(v___x_670_, 0);
v_messages_674_ = lean_ctor_get(v___x_670_, 1);
v_scopes_675_ = lean_ctor_get(v___x_670_, 2);
v_usedQuotCtxts_676_ = lean_ctor_get(v___x_670_, 3);
v_nextMacroScope_677_ = lean_ctor_get(v___x_670_, 4);
v_maxRecDepth_678_ = lean_ctor_get(v___x_670_, 5);
v_ngen_679_ = lean_ctor_get(v___x_670_, 6);
v_auxDeclNGen_680_ = lean_ctor_get(v___x_670_, 7);
v_infoState_681_ = lean_ctor_get(v___x_670_, 8);
v_traceState_682_ = lean_ctor_get(v___x_670_, 9);
v_snapshotTasks_683_ = lean_ctor_get(v___x_670_, 10);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_699_ == 0)
{
v___x_685_ = v___x_670_;
v_isShared_686_ = v_isSharedCheck_699_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snapshotTasks_683_);
lean_inc(v_traceState_682_);
lean_inc(v_infoState_681_);
lean_inc(v_auxDeclNGen_680_);
lean_inc(v_ngen_679_);
lean_inc(v_maxRecDepth_678_);
lean_inc(v_nextMacroScope_677_);
lean_inc(v_usedQuotCtxts_676_);
lean_inc(v_scopes_675_);
lean_inc(v_messages_674_);
lean_inc(v_env_673_);
lean_dec(v___x_670_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_699_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_currNamespace_671_);
lean_ctor_set(v___x_687_, 1, v_openDecls_672_);
v___x_688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___y_656_);
lean_inc_ref(v___y_659_);
lean_inc_ref(v___y_661_);
v___x_689_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_689_, 0, v___y_661_);
lean_ctor_set(v___x_689_, 1, v___y_658_);
lean_ctor_set(v___x_689_, 2, v___y_655_);
lean_ctor_set(v___x_689_, 3, v___y_659_);
lean_ctor_set(v___x_689_, 4, v___x_688_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*5, v___y_657_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*5 + 1, v___y_660_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*5 + 2, v_isSilent_650_);
v___x_690_ = l_Lean_MessageLog_add(v___x_689_, v_messages_674_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_690_);
v___x_692_ = v___x_685_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_env_673_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_scopes_675_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_usedQuotCtxts_676_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_nextMacroScope_677_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_maxRecDepth_678_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_ngen_679_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_auxDeclNGen_680_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_infoState_681_);
lean_ctor_set(v_reuseFailAlloc_698_, 9, v_traceState_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 10, v_snapshotTasks_683_);
v___x_692_ = v_reuseFailAlloc_698_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_693_ = lean_st_ref_set(v___y_662_, v___x_692_);
v___x_694_ = lean_box(0);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_694_);
v___x_696_ = v___x_668_;
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
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_a_664_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
v_a_701_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_665_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_665_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v___y_658_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
v_a_709_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_663_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_663_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
v___jp_717_:
{
lean_object* v_fileName_723_; lean_object* v_fileMap_724_; uint8_t v_suppressElabErrors_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_744_; 
v_fileName_723_ = lean_ctor_get(v___y_651_, 0);
v_fileMap_724_ = lean_ctor_get(v___y_651_, 1);
v_suppressElabErrors_725_ = lean_ctor_get_uint8(v___y_651_, sizeof(void*)*10);
v___x_726_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_648_);
v___x_727_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_726_, v___y_652_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_744_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_inc_ref_n(v_fileMap_724_, 2);
v___x_732_ = l_Lean_FileMap_toPosition(v_fileMap_724_, v___y_719_);
lean_dec(v___y_719_);
v___x_733_ = l_Lean_FileMap_toPosition(v_fileMap_724_, v___y_722_);
lean_dec(v___y_722_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_725_ == 0)
{
lean_del_object(v___x_730_);
v___y_655_ = v___x_734_;
v___y_656_ = v_a_728_;
v___y_657_ = v___y_720_;
v___y_658_ = v___x_732_;
v___y_659_ = v___x_735_;
v___y_660_ = v___y_721_;
v___y_661_ = v_fileName_723_;
v___y_662_ = v___y_652_;
goto v___jp_654_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___f_738_; uint8_t v___x_739_; 
v___x_736_ = lean_box(v___y_718_);
v___x_737_ = lean_box(v_suppressElabErrors_725_);
v___f_738_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_738_, 0, v___x_736_);
lean_closure_set(v___f_738_, 1, v___x_737_);
lean_inc(v_a_728_);
v___x_739_ = l_Lean_MessageData_hasTag(v___f_738_, v_a_728_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec_ref(v___x_734_);
lean_dec_ref(v___x_732_);
lean_dec(v_a_728_);
v___x_740_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_740_);
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_del_object(v___x_730_);
v___y_655_ = v___x_734_;
v___y_656_ = v_a_728_;
v___y_657_ = v___y_720_;
v___y_658_ = v___x_732_;
v___y_659_ = v___x_735_;
v___y_660_ = v___y_721_;
v___y_661_ = v_fileName_723_;
v___y_662_ = v___y_652_;
goto v___jp_654_;
}
}
}
}
v___jp_745_:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Syntax_getTailPos_x3f(v___y_747_, v___y_748_);
lean_dec(v___y_747_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_inc(v___y_750_);
v___y_718_ = v___y_746_;
v___y_719_ = v___y_750_;
v___y_720_ = v___y_748_;
v___y_721_ = v___y_749_;
v___y_722_ = v___y_750_;
goto v___jp_717_;
}
else
{
lean_object* v_val_752_; 
v_val_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_752_);
lean_dec_ref(v___x_751_);
v___y_718_ = v___y_746_;
v___y_719_ = v___y_750_;
v___y_720_ = v___y_748_;
v___y_721_ = v___y_749_;
v___y_722_ = v_val_752_;
goto v___jp_717_;
}
}
v___jp_753_:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Elab_Command_getRef___redArg(v___y_651_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v_ref_759_; lean_object* v___x_760_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_757_);
v_ref_759_ = l_Lean_replaceRef(v_ref_647_, v_a_758_);
lean_dec(v_a_758_);
v___x_760_ = l_Lean_Syntax_getPos_x3f(v_ref_759_, v___y_755_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___y_746_ = v___y_754_;
v___y_747_ = v_ref_759_;
v___y_748_ = v___y_755_;
v___y_749_ = v___y_756_;
v___y_750_ = v___x_761_;
goto v___jp_745_;
}
else
{
lean_object* v_val_762_; 
v_val_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_762_);
lean_dec_ref(v___x_760_);
v___y_746_ = v___y_754_;
v___y_747_ = v_ref_759_;
v___y_748_ = v___y_755_;
v___y_749_ = v___y_756_;
v___y_750_ = v_val_762_;
goto v___jp_745_;
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v_msgData_648_);
v_a_763_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_757_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_757_);
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
v___jp_772_:
{
if (v___y_775_ == 0)
{
v___y_754_ = v___y_773_;
v___y_755_ = v___y_774_;
v___y_756_ = v_severity_649_;
goto v___jp_753_;
}
else
{
v___y_754_ = v___y_773_;
v___y_755_ = v___y_774_;
v___y_756_ = v___x_771_;
goto v___jp_753_;
}
}
v___jp_776_:
{
if (v___y_777_ == 0)
{
lean_object* v___x_778_; lean_object* v_scopes_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_opts_782_; uint8_t v___x_783_; uint8_t v___x_784_; 
v___x_778_ = lean_st_ref_get(v___y_652_);
v_scopes_779_ = lean_ctor_get(v___x_778_, 2);
lean_inc(v_scopes_779_);
lean_dec(v___x_778_);
v___x_780_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_781_ = l_List_head_x21___redArg(v___x_780_, v_scopes_779_);
lean_dec(v_scopes_779_);
v_opts_782_ = lean_ctor_get(v___x_781_, 1);
lean_inc_ref(v_opts_782_);
lean_dec(v___x_781_);
v___x_783_ = 1;
v___x_784_ = l_Lean_instBEqMessageSeverity_beq(v_severity_649_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec_ref(v_opts_782_);
v___y_773_ = v___y_777_;
v___y_774_ = v___y_777_;
v___y_775_ = v___x_784_;
goto v___jp_772_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = l_Lean_warningAsError;
v___x_786_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_782_, v___x_785_);
lean_dec_ref(v_opts_782_);
v___y_773_ = v___y_777_;
v___y_774_ = v___y_777_;
v___y_775_ = v___x_786_;
goto v___jp_772_;
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_msgData_648_);
v___x_787_ = lean_box(0);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_791_, lean_object* v_msgData_792_, lean_object* v_severity_793_, lean_object* v_isSilent_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_severity_boxed_798_; uint8_t v_isSilent_boxed_799_; lean_object* v_res_800_; 
v_severity_boxed_798_ = lean_unbox(v_severity_793_);
v_isSilent_boxed_799_ = lean_unbox(v_isSilent_794_);
v_res_800_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_791_, v_msgData_792_, v_severity_boxed_798_, v_isSilent_boxed_799_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v_ref_791_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_801_, uint8_t v_severity_802_, uint8_t v_isSilent_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Elab_Command_getRef___redArg(v___y_804_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v___x_809_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_808_, v_msgData_801_, v_severity_802_, v_isSilent_803_, v___y_804_, v___y_805_);
lean_dec(v_a_808_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_msgData_801_);
v_a_810_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_807_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_807_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_818_, lean_object* v_severity_819_, lean_object* v_isSilent_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v_severity_boxed_824_; uint8_t v_isSilent_boxed_825_; lean_object* v_res_826_; 
v_severity_boxed_824_ = lean_unbox(v_severity_819_);
v_isSilent_boxed_825_ = lean_unbox(v_isSilent_820_);
v_res_826_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_818_, v_severity_boxed_824_, v_isSilent_boxed_825_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_831_; uint8_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = 2;
v___x_832_ = 0;
v___x_833_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_827_, v___x_831_, v___x_832_, v___y_828_, v___y_829_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_839_, lean_object* v_msgData_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = 2;
v___x_845_ = 0;
v___x_846_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_839_, v_msgData_840_, v___x_844_, v___x_845_, v___y_841_, v___y_842_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_847_, lean_object* v_msgData_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_847_, v_msgData_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v_ref_847_);
return v_res_852_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
if (lean_obj_tag(v_ex_856_) == 0)
{
lean_object* v_ref_860_; lean_object* v_msg_861_; lean_object* v___x_862_; 
v_ref_860_ = lean_ctor_get(v_ex_856_, 0);
lean_inc(v_ref_860_);
v_msg_861_ = lean_ctor_get(v_ex_856_, 1);
lean_inc_ref(v_msg_861_);
lean_dec_ref(v_ex_856_);
v___x_862_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_860_, v_msg_861_, v___y_857_, v___y_858_);
lean_dec(v_ref_860_);
return v___x_862_;
}
else
{
lean_object* v_id_863_; uint8_t v___y_865_; uint8_t v___x_887_; 
v_id_863_ = lean_ctor_get(v_ex_856_, 0);
lean_inc(v_id_863_);
v___x_887_ = l_Lean_Elab_isAbortExceptionId(v_id_863_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_Exception_isInterrupt(v_ex_856_);
lean_dec_ref(v_ex_856_);
v___y_865_ = v___x_888_;
goto v___jp_864_;
}
else
{
lean_dec_ref(v_ex_856_);
v___y_865_ = v___x_887_;
goto v___jp_864_;
}
v___jp_864_:
{
if (v___y_865_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_InternalExceptionId_getName(v_id_863_);
lean_dec(v_id_863_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_869_ = l_Lean_MessageData_ofName(v_a_867_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_870_, v___y_857_, v___y_858_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_884_; 
v_a_872_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_884_ == 0)
{
v___x_874_ = v___x_866_;
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_866_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_ref_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v_ref_876_ = lean_ctor_get(v___y_857_, 7);
v___x_877_ = lean_io_error_to_string(v_a_872_);
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = l_Lean_MessageData_ofFormat(v___x_878_);
lean_inc(v_ref_876_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_ref_876_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_880_);
v___x_882_ = v___x_874_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v_id_863_);
v___x_885_ = lean_box(0);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
v___x_898_ = lean_apply_3(v_x_894_, v___y_895_, v___y_896_, lean_box(0));
if (lean_obj_tag(v___x_898_) == 0)
{
return v___x_898_;
}
else
{
lean_object* v_a_899_; uint8_t v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
v___x_900_ = l_Lean_Exception_isInterrupt(v_a_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v___x_898_);
v___x_901_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_899_, v___y_895_, v___y_896_);
return v___x_901_;
}
else
{
lean_dec(v_a_899_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_907_, lean_object* v___x_908_, lean_object* v_val_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_a_913_; lean_object* v___x_915_; 
v___x_915_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_907_, v___x_908_, v_val_909_);
if (lean_obj_tag(v___x_915_) == 0)
{
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref(v___x_915_);
v_a_913_ = v_a_916_;
goto v___jp_912_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
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
else
{
lean_object* v___x_925_; 
lean_dec_ref(v___x_915_);
v___x_925_ = lean_box(0);
v_a_913_ = v___x_925_;
goto v___jp_912_;
}
v___jp_912_:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_a_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_926_, lean_object* v___x_927_, lean_object* v_val_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_926_, v___x_927_, v_val_928_, v___y_929_);
lean_dec_ref(v___y_929_);
lean_dec(v_val_928_);
lean_dec_ref(v___x_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_932_, lean_object* v_x_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_get_set_stderr(v_h_932_);
lean_inc_ref(v___y_934_);
v___x_937_ = lean_apply_2(v_x_933_, v___y_934_, lean_box(0));
v___x_938_ = lean_get_set_stderr(v___x_936_);
lean_dec_ref(v___x_938_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_939_, lean_object* v_x_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_939_, v_x_940_, v___y_941_);
lean_dec_ref(v___y_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_944_, lean_object* v_h_945_, lean_object* v_x_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_945_, v_x_946_, v___y_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_950_, lean_object* v_h_951_, lean_object* v_x_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_950_, v_h_951_, v_x_952_, v___y_953_);
lean_dec_ref(v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_956_, lean_object* v_x_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_get_set_stdin(v_h_956_);
lean_inc_ref(v___y_958_);
v___x_961_ = lean_apply_2(v_x_957_, v___y_958_, lean_box(0));
v___x_962_ = lean_get_set_stdin(v___x_960_);
lean_dec_ref(v___x_962_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_963_, v_x_964_, v___y_965_);
lean_dec_ref(v___y_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_968_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_970_ = lean_panic_fn_borrowed(v___x_969_, v_msg_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_971_, lean_object* v_x_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_get_set_stdout(v_h_971_);
lean_inc_ref(v___y_973_);
v___x_976_ = lean_apply_2(v_x_972_, v___y_973_, lean_box(0));
v___x_977_ = lean_get_set_stdout(v___x_975_);
lean_dec_ref(v___x_977_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_978_, lean_object* v_x_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_978_, v_x_979_, v___y_980_);
lean_dec_ref(v___y_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_983_, lean_object* v_h_984_, lean_object* v_x_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_984_, v_x_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_989_, lean_object* v_h_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_989_, v_h_990_, v_x_991_, v___y_992_);
lean_dec_ref(v___y_992_);
return v_res_994_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = l_ByteArray_empty;
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
return v___x_997_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1002_ = lean_unsigned_to_nat(46u);
v___x_1003_ = lean_unsigned_to_nat(193u);
v___x_1004_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1005_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1006_ = l_mkPanicMessageWithDecl(v___x_1005_, v___x_1004_, v___x_1003_, v___x_1002_, v___x_1001_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1007_, uint8_t v_isolateStderr_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___y_1021_; 
v___x_1015_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1016_ = lean_st_mk_ref(v___x_1015_);
v___x_1017_ = lean_st_mk_ref(v___x_1015_);
v___x_1018_ = l_IO_FS_Stream_ofBuffer(v___x_1016_);
lean_inc(v___x_1017_);
v___x_1019_ = l_IO_FS_Stream_ofBuffer(v___x_1017_);
if (v_isolateStderr_1008_ == 0)
{
v___y_1021_ = v_x_1007_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1030_; 
lean_inc_ref(v___x_1019_);
v___x_1030_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1030_, 0, lean_box(0));
lean_closure_set(v___x_1030_, 1, v___x_1019_);
lean_closure_set(v___x_1030_, 2, v_x_1007_);
v___y_1021_ = v___x_1030_;
goto v___jp_1020_;
}
v___jp_1011_:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___y_1013_);
lean_ctor_set(v___x_1014_, 1, v___y_1012_);
return v___x_1014_;
}
v___jp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_data_1025_; uint8_t v___x_1026_; 
v___x_1022_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1022_, 0, lean_box(0));
lean_closure_set(v___x_1022_, 1, v___x_1019_);
lean_closure_set(v___x_1022_, 2, v___y_1021_);
v___x_1023_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1018_, v___x_1022_, v___y_1009_);
v___x_1024_ = lean_st_ref_get(v___x_1017_);
lean_dec(v___x_1017_);
v_data_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc_ref(v_data_1025_);
lean_dec(v___x_1024_);
v___x_1026_ = lean_string_validate_utf8(v_data_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_data_1025_);
v___x_1027_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1028_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1027_);
v___y_1012_ = v___x_1023_;
v___y_1013_ = v___x_1028_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_string_from_utf8_unchecked(v_data_1025_);
v___y_1012_ = v___x_1023_;
v___y_1013_ = v___x_1029_;
goto v___jp_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1031_, lean_object* v_isolateStderr_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v_isolateStderr_boxed_1035_; lean_object* v_res_1036_; 
v_isolateStderr_boxed_1035_ = lean_unbox(v_isolateStderr_1032_);
v_res_1036_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1031_, v_isolateStderr_boxed_1035_, v___y_1033_);
lean_dec_ref(v___y_1033_);
return v_res_1036_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = 1;
v___x_1046_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1047_ = l_Lean_Name_toString(v___x_1046_, v___x_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1048_, lean_object* v_cmdState_1049_, lean_object* v_beginPos_1050_, lean_object* v_snap_1051_, lean_object* v_cancelTk_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_env_1055_; lean_object* v_scopes_1056_; lean_object* v_usedQuotCtxts_1057_; lean_object* v_nextMacroScope_1058_; lean_object* v_maxRecDepth_1059_; lean_object* v_ngen_1060_; lean_object* v_auxDeclNGen_1061_; lean_object* v_infoState_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1138_; 
v_env_1055_ = lean_ctor_get(v_cmdState_1049_, 0);
v_scopes_1056_ = lean_ctor_get(v_cmdState_1049_, 2);
v_usedQuotCtxts_1057_ = lean_ctor_get(v_cmdState_1049_, 3);
v_nextMacroScope_1058_ = lean_ctor_get(v_cmdState_1049_, 4);
v_maxRecDepth_1059_ = lean_ctor_get(v_cmdState_1049_, 5);
v_ngen_1060_ = lean_ctor_get(v_cmdState_1049_, 6);
v_auxDeclNGen_1061_ = lean_ctor_get(v_cmdState_1049_, 7);
v_infoState_1062_ = lean_ctor_get(v_cmdState_1049_, 8);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_cmdState_1049_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; 
v_unused_1139_ = lean_ctor_get(v_cmdState_1049_, 10);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_cmdState_1049_, 9);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_cmdState_1049_, 1);
lean_dec(v_unused_1141_);
v___x_1064_ = v_cmdState_1049_;
v_isShared_1065_ = v_isSharedCheck_1138_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_infoState_1062_);
lean_inc(v_auxDeclNGen_1061_);
lean_inc(v_ngen_1060_);
lean_inc(v_maxRecDepth_1059_);
lean_inc(v_nextMacroScope_1058_);
lean_inc(v_usedQuotCtxts_1057_);
lean_inc(v_scopes_1056_);
lean_inc(v_env_1055_);
lean_dec(v_cmdState_1049_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1138_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1066_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1067_ = l_List_head_x21___redArg(v___x_1066_, v_scopes_1056_);
v___x_1068_ = l_Lean_MessageLog_empty;
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1071_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 10, v___x_1071_);
lean_ctor_set(v___x_1064_, 9, v___x_1070_);
lean_ctor_set(v___x_1064_, 1, v___x_1068_);
v___x_1073_ = v___x_1064_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_env_1055_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_scopes_1056_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_usedQuotCtxts_1057_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_nextMacroScope_1058_);
lean_ctor_set(v_reuseFailAlloc_1137_, 5, v_maxRecDepth_1059_);
lean_ctor_set(v_reuseFailAlloc_1137_, 6, v_ngen_1060_);
lean_ctor_set(v_reuseFailAlloc_1137_, 7, v_auxDeclNGen_1061_);
lean_ctor_set(v_reuseFailAlloc_1137_, 8, v_infoState_1062_);
lean_ctor_set(v_reuseFailAlloc_1137_, 9, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1137_, 10, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v_toProcessingContext_1075_; lean_object* v_fileName_1076_; lean_object* v_fileMap_1077_; lean_object* v_opts_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___y_1088_; uint8_t v___y_1089_; lean_object* v_messages_1090_; lean_object* v___y_1116_; 
v___x_1074_ = lean_st_mk_ref(v___x_1073_);
v_toProcessingContext_1075_ = lean_ctor_get(v_a_1053_, 0);
v_fileName_1076_ = lean_ctor_get(v_toProcessingContext_1075_, 1);
v_fileMap_1077_ = lean_ctor_get(v_toProcessingContext_1075_, 2);
v_opts_1078_ = lean_ctor_get(v___x_1067_, 1);
lean_inc_ref(v_opts_1078_);
lean_dec(v___x_1067_);
v___f_1079_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1079_, 0, v_stx_1048_);
v___x_1080_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_box(0);
v___x_1083_ = l_Lean_firstFrontendMacroScope;
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_internal_cmdlineSnapshots;
v___x_1086_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1078_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1136_; 
lean_inc_ref(v_snap_1051_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_snap_1051_);
v___y_1116_ = v___x_1136_;
goto v___jp_1115_;
}
else
{
v___y_1116_ = v___x_1082_;
goto v___jp_1115_;
}
v___jp_1087_:
{
lean_object* v_new_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_env_1097_; lean_object* v_scopes_1098_; lean_object* v_usedQuotCtxts_1099_; lean_object* v_nextMacroScope_1100_; lean_object* v_maxRecDepth_1101_; lean_object* v_ngen_1102_; lean_object* v_auxDeclNGen_1103_; lean_object* v_infoState_1104_; lean_object* v_traceState_1105_; lean_object* v_snapshotTasks_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_new_1091_ = lean_ctor_get(v_snap_1051_, 1);
lean_inc(v_new_1091_);
lean_dec_ref(v_snap_1051_);
v___x_1092_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1093_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1094_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_ctor_set(v___x_1094_, 2, v___x_1082_);
lean_ctor_set(v___x_1094_, 3, v___x_1070_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*4, v___y_1089_);
v___x_1095_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1080_, v___x_1094_);
v___x_1096_ = lean_io_promise_resolve(v___x_1095_, v_new_1091_);
lean_dec(v_new_1091_);
v_env_1097_ = lean_ctor_get(v___y_1088_, 0);
v_scopes_1098_ = lean_ctor_get(v___y_1088_, 2);
v_usedQuotCtxts_1099_ = lean_ctor_get(v___y_1088_, 3);
v_nextMacroScope_1100_ = lean_ctor_get(v___y_1088_, 4);
v_maxRecDepth_1101_ = lean_ctor_get(v___y_1088_, 5);
v_ngen_1102_ = lean_ctor_get(v___y_1088_, 6);
v_auxDeclNGen_1103_ = lean_ctor_get(v___y_1088_, 7);
v_infoState_1104_ = lean_ctor_get(v___y_1088_, 8);
v_traceState_1105_ = lean_ctor_get(v___y_1088_, 9);
v_snapshotTasks_1106_ = lean_ctor_get(v___y_1088_, 10);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___y_1088_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___y_1088_, 1);
lean_dec(v_unused_1114_);
v___x_1108_ = v___y_1088_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_snapshotTasks_1106_);
lean_inc(v_traceState_1105_);
lean_inc(v_infoState_1104_);
lean_inc(v_auxDeclNGen_1103_);
lean_inc(v_ngen_1102_);
lean_inc(v_maxRecDepth_1101_);
lean_inc(v_nextMacroScope_1100_);
lean_inc(v_usedQuotCtxts_1099_);
lean_inc(v_scopes_1098_);
lean_inc(v_env_1097_);
lean_dec(v___y_1088_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 1, v_messages_1090_);
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_env_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_messages_1090_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_scopes_1098_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_usedQuotCtxts_1099_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_nextMacroScope_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 5, v_maxRecDepth_1101_);
lean_ctor_set(v_reuseFailAlloc_1112_, 6, v_ngen_1102_);
lean_ctor_set(v_reuseFailAlloc_1112_, 7, v_auxDeclNGen_1103_);
lean_ctor_set(v_reuseFailAlloc_1112_, 8, v_infoState_1104_);
lean_ctor_set(v_reuseFailAlloc_1112_, 9, v_traceState_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 10, v_snapshotTasks_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
v___jp_1115_:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v_fst_1124_; lean_object* v___x_1125_; lean_object* v_messages_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_cancelTk_1052_);
v___x_1118_ = 0;
lean_inc(v_beginPos_1050_);
lean_inc_ref(v_fileMap_1077_);
lean_inc_ref(v_fileName_1076_);
v___x_1119_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1119_, 0, v_fileName_1076_);
lean_ctor_set(v___x_1119_, 1, v_fileMap_1077_);
lean_ctor_set(v___x_1119_, 2, v___x_1069_);
lean_ctor_set(v___x_1119_, 3, v_beginPos_1050_);
lean_ctor_set(v___x_1119_, 4, v___x_1081_);
lean_ctor_set(v___x_1119_, 5, v___x_1082_);
lean_ctor_set(v___x_1119_, 6, v___x_1083_);
lean_ctor_set(v___x_1119_, 7, v___x_1084_);
lean_ctor_set(v___x_1119_, 8, v___y_1116_);
lean_ctor_set(v___x_1119_, 9, v___x_1117_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*10, v___x_1118_);
lean_inc(v___x_1074_);
v___f_1120_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1120_, 0, v___f_1079_);
lean_closure_set(v___f_1120_, 1, v___x_1119_);
lean_closure_set(v___f_1120_, 2, v___x_1074_);
v___x_1121_ = l_Lean_Core_stderrAsMessages;
v___x_1122_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1078_, v___x_1121_);
lean_dec_ref(v_opts_1078_);
v___x_1123_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1120_, v___x_1122_, v_a_1053_);
v_fst_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_fst_1124_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = lean_st_ref_get(v___x_1074_);
lean_dec(v___x_1074_);
v_messages_1126_ = lean_ctor_get(v___x_1125_, 1);
lean_inc_ref(v_messages_1126_);
v___x_1127_ = lean_string_utf8_byte_size(v_fst_1124_);
v___x_1128_ = lean_nat_dec_eq(v___x_1127_, v___x_1069_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc_ref(v_fileMap_1077_);
v___x_1129_ = l_Lean_FileMap_toPosition(v_fileMap_1077_, v_beginPos_1050_);
lean_dec(v_beginPos_1050_);
v___x_1130_ = 0;
v___x_1131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_fst_1124_);
v___x_1133_ = l_Lean_MessageData_ofFormat(v___x_1132_);
lean_inc_ref(v_fileName_1076_);
v___x_1134_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1134_, 0, v_fileName_1076_);
lean_ctor_set(v___x_1134_, 1, v___x_1129_);
lean_ctor_set(v___x_1134_, 2, v___x_1082_);
lean_ctor_set(v___x_1134_, 3, v___x_1131_);
lean_ctor_set(v___x_1134_, 4, v___x_1133_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*5, v___x_1118_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*5 + 1, v___x_1130_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*5 + 2, v___x_1118_);
v___x_1135_ = l_Lean_MessageLog_add(v___x_1134_, v_messages_1126_);
v___y_1088_ = v___x_1125_;
v___y_1089_ = v___x_1118_;
v_messages_1090_ = v___x_1135_;
goto v___jp_1087_;
}
else
{
lean_dec(v_fst_1124_);
lean_dec(v_beginPos_1050_);
v___y_1088_ = v___x_1125_;
v___y_1089_ = v___x_1118_;
v_messages_1090_ = v_messages_1126_;
goto v___jp_1087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1142_, lean_object* v_cmdState_1143_, lean_object* v_beginPos_1144_, lean_object* v_snap_1145_, lean_object* v_cancelTk_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1142_, v_cmdState_1143_, v_beginPos_1144_, v_snap_1145_, v_cancelTk_1146_, v_a_1147_);
lean_dec_ref(v_a_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1150_, lean_object* v_h_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1151_, v_x_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_h_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1156_, v_h_1157_, v_x_1158_, v___y_1159_);
lean_dec_ref(v___y_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1162_, lean_object* v_x_1163_, uint8_t v_isolateStderr_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1163_, v_isolateStderr_1164_, v___y_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1168_, lean_object* v_x_1169_, lean_object* v_isolateStderr_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v_isolateStderr_boxed_1173_; lean_object* v_res_1174_; 
v_isolateStderr_boxed_1173_ = lean_unbox(v_isolateStderr_1170_);
v_res_1174_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1168_, v_x_1169_, v_isolateStderr_boxed_1173_, v___y_1171_);
lean_dec_ref(v___y_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1175_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_opts_1185_, lean_object* v_opt_1186_){
_start:
{
lean_object* v_name_1187_; lean_object* v_defValue_1188_; lean_object* v_map_1189_; lean_object* v___x_1190_; 
v_name_1187_ = lean_ctor_get(v_opt_1186_, 0);
v_defValue_1188_ = lean_ctor_get(v_opt_1186_, 1);
v_map_1189_ = lean_ctor_get(v_opts_1185_, 0);
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1189_, v_name_1187_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_inc(v_defValue_1188_);
return v_defValue_1188_;
}
else
{
lean_object* v_val_1191_; 
v_val_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_val_1191_);
lean_dec_ref(v___x_1190_);
if (lean_obj_tag(v_val_1191_) == 3)
{
lean_object* v_v_1192_; 
v_v_1192_ = lean_ctor_get(v_val_1191_, 0);
lean_inc(v_v_1192_);
lean_dec_ref(v_val_1191_);
return v_v_1192_;
}
else
{
lean_dec(v_val_1191_);
lean_inc(v_defValue_1188_);
return v_defValue_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0___boxed(lean_object* v_opts_1193_, lean_object* v_opt_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1193_, v_opt_1194_);
lean_dec_ref(v_opt_1194_);
lean_dec_ref(v_opts_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_s_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_s_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_s_1199_){
_start:
{
lean_object* v_toSnapshot_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_toSnapshot_1200_ = lean_ctor_get(v_s_1199_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_s_1199_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_s_1199_, 1);
lean_dec(v_unused_1209_);
v___x_1202_ = v_s_1199_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_toSnapshot_1200_);
lean_dec(v_s_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_toSnapshot_1200_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_s_1210_){
_start:
{
lean_object* v_tree_1211_; lean_object* v___x_1212_; 
v_tree_1211_ = lean_ctor_get(v_s_1210_, 1);
v___x_1212_ = lean_thunk_get_own(v_tree_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_s_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_s_1213_);
lean_dec_ref(v_s_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v_a_1215_, lean_object* v___x_1216_, lean_object* v_parserState_1217_, lean_object* v_x_1218_){
_start:
{
lean_object* v_toProcessingContext_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_toProcessingContext_1219_ = lean_ctor_get(v_a_1215_, 0);
v___x_1220_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1219_);
v___x_1221_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1219_, v___x_1216_, v_parserState_1217_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v_a_1222_, lean_object* v___x_1223_, lean_object* v_parserState_1224_, lean_object* v_x_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v_a_1222_, v___x_1223_, v_parserState_1224_, v_x_1225_);
lean_dec_ref(v_a_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, uint8_t v_val_1230_, lean_object* v_as_1231_, size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_b_1234_){
_start:
{
uint8_t v___x_1236_; 
v___x_1236_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v___x_1229_);
lean_dec_ref(v___x_1227_);
return v_b_1234_;
}
else
{
lean_object* v_snd_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1255_; 
v_snd_1237_ = lean_ctor_get(v_b_1234_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_b_1234_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v_b_1234_, 0);
lean_dec(v_unused_1256_);
v___x_1239_ = v_b_1234_;
v_isShared_1240_ = v_isSharedCheck_1255_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_snd_1237_);
lean_dec(v_b_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1255_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_a_1241_; lean_object* v_msg_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_a_1241_ = lean_array_uget_borrowed(v_as_1231_, v_i_1233_);
v_msg_1242_ = lean_ctor_get(v_a_1241_, 1);
v___x_1243_ = lean_box(0);
lean_inc_ref(v___x_1227_);
v___x_1244_ = l_Lean_FileMap_toPosition(v___x_1227_, v___x_1228_);
v___x_1245_ = 0;
v___x_1246_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1242_);
lean_inc_ref(v___x_1229_);
v___x_1247_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1247_, 0, v___x_1229_);
lean_ctor_set(v___x_1247_, 1, v___x_1244_);
lean_ctor_set(v___x_1247_, 2, v___x_1243_);
lean_ctor_set(v___x_1247_, 3, v___x_1246_);
lean_ctor_set(v___x_1247_, 4, v_msg_1242_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*5, v_val_1230_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*5 + 1, v___x_1245_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*5 + 2, v_val_1230_);
v___x_1248_ = l_Lean_MessageLog_add(v___x_1247_, v_snd_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1248_);
lean_ctor_set(v___x_1239_, 0, v___x_1243_);
v___x_1250_ = v___x_1239_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
size_t v___x_1251_; size_t v___x_1252_; 
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1233_, v___x_1251_);
v_i_1233_ = v___x_1252_;
v_b_1234_ = v___x_1250_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v_val_1260_, lean_object* v_as_1261_, lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v_val_44570__boxed_1266_; size_t v_sz_boxed_1267_; size_t v_i_boxed_1268_; lean_object* v_res_1269_; 
v_val_44570__boxed_1266_ = lean_unbox(v_val_1260_);
v_sz_boxed_1267_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1268_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1257_, v___x_1258_, v___x_1259_, v_val_44570__boxed_1266_, v_as_1261_, v_sz_boxed_1267_, v_i_boxed_1268_, v_b_1264_);
lean_dec_ref(v_as_1261_);
lean_dec(v___x_1258_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(lean_object* v___x_1270_, lean_object* v___x_1271_, lean_object* v___x_1272_, uint8_t v_val_1273_, lean_object* v_as_1274_, size_t v_sz_1275_, size_t v_i_1276_, lean_object* v_b_1277_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v___x_1272_);
lean_dec_ref(v___x_1270_);
return v_b_1277_;
}
else
{
lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1298_; 
v_snd_1280_ = lean_ctor_get(v_b_1277_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_b_1277_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_b_1277_, 0);
lean_dec(v_unused_1299_);
v___x_1282_ = v_b_1277_;
v_isShared_1283_ = v_isSharedCheck_1298_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_dec(v_b_1277_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1298_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_a_1284_; lean_object* v_msg_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_a_1284_ = lean_array_uget_borrowed(v_as_1274_, v_i_1276_);
v_msg_1285_ = lean_ctor_get(v_a_1284_, 1);
v___x_1286_ = lean_box(0);
lean_inc_ref(v___x_1270_);
v___x_1287_ = l_Lean_FileMap_toPosition(v___x_1270_, v___x_1271_);
v___x_1288_ = 0;
v___x_1289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1285_);
lean_inc_ref(v___x_1272_);
v___x_1290_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1290_, 0, v___x_1272_);
lean_ctor_set(v___x_1290_, 1, v___x_1287_);
lean_ctor_set(v___x_1290_, 2, v___x_1286_);
lean_ctor_set(v___x_1290_, 3, v___x_1289_);
lean_ctor_set(v___x_1290_, 4, v_msg_1285_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*5, v_val_1273_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*5 + 1, v___x_1288_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*5 + 2, v_val_1273_);
v___x_1291_ = l_Lean_MessageLog_add(v___x_1290_, v_snd_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1291_);
lean_ctor_set(v___x_1282_, 0, v___x_1286_);
v___x_1293_ = v___x_1282_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1276_, v___x_1294_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1270_, v___x_1271_, v___x_1272_, v_val_1273_, v_as_1274_, v_sz_1275_, v___x_1295_, v___x_1293_);
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3___boxed(lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v_val_1303_, lean_object* v_as_1304_, lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v_val_44622__boxed_1309_; size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_val_44622__boxed_1309_ = lean_unbox(v_val_1303_);
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1300_, v___x_1301_, v___x_1302_, v_val_44622__boxed_1309_, v_as_1304_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1307_);
lean_dec_ref(v_as_1304_);
lean_dec(v___x_1301_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(lean_object* v_init_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, uint8_t v_val_1317_, lean_object* v_n_1318_, lean_object* v_b_1319_){
_start:
{
if (lean_obj_tag(v_n_1318_) == 0)
{
lean_object* v_cs_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; size_t v_sz_1324_; size_t v___x_1325_; lean_object* v___x_1326_; lean_object* v_fst_1327_; 
v_cs_1321_ = lean_ctor_get(v_n_1318_, 0);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_b_1319_);
v_sz_1324_ = lean_array_size(v_cs_1321_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1313_, v___x_1314_, v___x_1315_, v___x_1316_, v_val_1317_, v_cs_1321_, v_sz_1324_, v___x_1325_, v___x_1323_);
v_fst_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_fst_1327_);
if (lean_obj_tag(v_fst_1327_) == 0)
{
lean_object* v_snd_1328_; lean_object* v___x_1329_; 
v_snd_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_snd_1328_);
lean_dec_ref(v___x_1326_);
v___x_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_snd_1328_);
return v___x_1329_;
}
else
{
lean_object* v_val_1330_; 
lean_dec_ref(v___x_1326_);
v_val_1330_ = lean_ctor_get(v_fst_1327_, 0);
lean_inc(v_val_1330_);
lean_dec_ref(v_fst_1327_);
return v_val_1330_;
}
}
else
{
lean_object* v_vs_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; size_t v_sz_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v_fst_1337_; 
v_vs_1331_ = lean_ctor_get(v_n_1318_, 0);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v_b_1319_);
v_sz_1334_ = lean_array_size(v_vs_1331_);
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1314_, v___x_1315_, v___x_1316_, v_val_1317_, v_vs_1331_, v_sz_1334_, v___x_1335_, v___x_1333_);
v_fst_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_fst_1337_);
if (lean_obj_tag(v_fst_1337_) == 0)
{
lean_object* v_snd_1338_; lean_object* v___x_1339_; 
v_snd_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v___x_1336_);
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_snd_1338_);
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; 
lean_dec_ref(v___x_1336_);
v_val_1340_ = lean_ctor_get(v_fst_1337_, 0);
lean_inc(v_val_1340_);
lean_dec_ref(v_fst_1337_);
return v_val_1340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object* v_init_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, uint8_t v_val_1345_, lean_object* v_as_1346_, size_t v_sz_1347_, size_t v_i_1348_, lean_object* v_b_1349_){
_start:
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_usize_dec_lt(v_i_1348_, v_sz_1347_);
if (v___x_1351_ == 0)
{
lean_dec_ref(v___x_1344_);
lean_dec_ref(v___x_1342_);
return v_b_1349_;
}
else
{
lean_object* v_snd_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1370_; 
v_snd_1352_ = lean_ctor_get(v_b_1349_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_b_1349_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v_b_1349_, 0);
lean_dec(v_unused_1371_);
v___x_1354_ = v_b_1349_;
v_isShared_1355_ = v_isSharedCheck_1370_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snd_1352_);
lean_dec(v_b_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1370_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_array_uget_borrowed(v_as_1346_, v_i_1348_);
lean_inc(v_snd_1352_);
lean_inc_ref(v___x_1344_);
lean_inc_ref(v___x_1342_);
v___x_1357_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1341_, v___x_1342_, v___x_1343_, v___x_1344_, v_val_1345_, v_a_1356_, v_snd_1352_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_dec_ref(v___x_1344_);
lean_dec_ref(v___x_1342_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1358_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_snd_1352_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec(v_snd_1352_);
v_a_1362_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1357_);
v___x_1363_ = lean_box(0);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_a_1362_);
lean_ctor_set(v___x_1354_, 0, v___x_1363_);
v___x_1365_ = v___x_1354_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1362_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
size_t v___x_1366_; size_t v___x_1367_; 
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1348_, v___x_1366_);
v_i_1348_ = v___x_1367_;
v_b_1349_ = v___x_1365_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1372_, lean_object* v___x_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v_val_1376_, lean_object* v_as_1377_, lean_object* v_sz_1378_, lean_object* v_i_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v_val_44673__boxed_1382_; size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_val_44673__boxed_1382_ = lean_unbox(v_val_1376_);
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1379_);
lean_dec(v_i_1379_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1372_, v___x_1373_, v___x_1374_, v___x_1375_, v_val_44673__boxed_1382_, v_as_1377_, v_sz_boxed_1383_, v_i_boxed_1384_, v_b_1380_);
lean_dec_ref(v_as_1377_);
lean_dec(v___x_1374_);
lean_dec_ref(v_init_1372_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v_init_1386_, lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v___x_1389_, lean_object* v_val_1390_, lean_object* v_n_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_val_44689__boxed_1394_; lean_object* v_res_1395_; 
v_val_44689__boxed_1394_ = lean_unbox(v_val_1390_);
v_res_1395_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1386_, v___x_1387_, v___x_1388_, v___x_1389_, v_val_44689__boxed_1394_, v_n_1391_, v_b_1392_);
lean_dec_ref(v_n_1391_);
lean_dec(v___x_1388_);
lean_dec_ref(v_init_1386_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, uint8_t v_val_1399_, lean_object* v_as_1400_, size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_b_1403_){
_start:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1396_);
return v_b_1403_;
}
else
{
lean_object* v_snd_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1424_; 
v_snd_1406_ = lean_ctor_get(v_b_1403_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_b_1403_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_b_1403_, 0);
lean_dec(v_unused_1425_);
v___x_1408_ = v_b_1403_;
v_isShared_1409_ = v_isSharedCheck_1424_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_snd_1406_);
lean_dec(v_b_1403_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1424_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_a_1410_; lean_object* v_msg_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v_a_1410_ = lean_array_uget_borrowed(v_as_1400_, v_i_1402_);
v_msg_1411_ = lean_ctor_get(v_a_1410_, 1);
v___x_1412_ = lean_box(0);
lean_inc_ref(v___x_1396_);
v___x_1413_ = l_Lean_FileMap_toPosition(v___x_1396_, v___x_1397_);
v___x_1414_ = 0;
v___x_1415_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1411_);
lean_inc_ref(v___x_1398_);
v___x_1416_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1416_, 0, v___x_1398_);
lean_ctor_set(v___x_1416_, 1, v___x_1413_);
lean_ctor_set(v___x_1416_, 2, v___x_1412_);
lean_ctor_set(v___x_1416_, 3, v___x_1415_);
lean_ctor_set(v___x_1416_, 4, v_msg_1411_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*5, v_val_1399_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*5 + 1, v___x_1414_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*5 + 2, v_val_1399_);
v___x_1417_ = l_Lean_MessageLog_add(v___x_1416_, v_snd_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1417_);
lean_ctor_set(v___x_1408_, 0, v___x_1412_);
v___x_1419_ = v___x_1408_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
size_t v___x_1420_; size_t v___x_1421_; 
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1402_, v___x_1420_);
v_i_1402_ = v___x_1421_;
v_b_1403_ = v___x_1419_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v_val_1429_, lean_object* v_as_1430_, lean_object* v_sz_1431_, lean_object* v_i_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v_val_44771__boxed_1435_; size_t v_sz_boxed_1436_; size_t v_i_boxed_1437_; lean_object* v_res_1438_; 
v_val_44771__boxed_1435_ = lean_unbox(v_val_1429_);
v_sz_boxed_1436_ = lean_unbox_usize(v_sz_1431_);
lean_dec(v_sz_1431_);
v_i_boxed_1437_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1426_, v___x_1427_, v___x_1428_, v_val_44771__boxed_1435_, v_as_1430_, v_sz_boxed_1436_, v_i_boxed_1437_, v_b_1433_);
lean_dec_ref(v_as_1430_);
lean_dec(v___x_1427_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, uint8_t v_val_1442_, lean_object* v_as_1443_, size_t v_sz_1444_, size_t v_i_1445_, lean_object* v_b_1446_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_lt(v_i_1445_, v_sz_1444_);
if (v___x_1448_ == 0)
{
lean_dec_ref(v___x_1441_);
lean_dec_ref(v___x_1439_);
return v_b_1446_;
}
else
{
lean_object* v_snd_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1467_; 
v_snd_1449_ = lean_ctor_get(v_b_1446_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_b_1446_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_b_1446_, 0);
lean_dec(v_unused_1468_);
v___x_1451_ = v_b_1446_;
v_isShared_1452_ = v_isSharedCheck_1467_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1449_);
lean_dec(v_b_1446_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1467_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_a_1453_; lean_object* v_msg_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v_a_1453_ = lean_array_uget_borrowed(v_as_1443_, v_i_1445_);
v_msg_1454_ = lean_ctor_get(v_a_1453_, 1);
v___x_1455_ = lean_box(0);
lean_inc_ref(v___x_1439_);
v___x_1456_ = l_Lean_FileMap_toPosition(v___x_1439_, v___x_1440_);
v___x_1457_ = 0;
v___x_1458_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1454_);
lean_inc_ref(v___x_1441_);
v___x_1459_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1459_, 0, v___x_1441_);
lean_ctor_set(v___x_1459_, 1, v___x_1456_);
lean_ctor_set(v___x_1459_, 2, v___x_1455_);
lean_ctor_set(v___x_1459_, 3, v___x_1458_);
lean_ctor_set(v___x_1459_, 4, v_msg_1454_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*5, v_val_1442_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*5 + 1, v___x_1457_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*5 + 2, v_val_1442_);
v___x_1460_ = l_Lean_MessageLog_add(v___x_1459_, v_snd_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1460_);
lean_ctor_set(v___x_1451_, 0, v___x_1455_);
v___x_1462_ = v___x_1451_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_add(v_i_1445_, v___x_1463_);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1439_, v___x_1440_, v___x_1441_, v_val_1442_, v_as_1443_, v_sz_1444_, v___x_1464_, v___x_1462_);
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v_val_1472_, lean_object* v_as_1473_, lean_object* v_sz_1474_, lean_object* v_i_1475_, lean_object* v_b_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v_val_44823__boxed_1478_; size_t v_sz_boxed_1479_; size_t v_i_boxed_1480_; lean_object* v_res_1481_; 
v_val_44823__boxed_1478_ = lean_unbox(v_val_1472_);
v_sz_boxed_1479_ = lean_unbox_usize(v_sz_1474_);
lean_dec(v_sz_1474_);
v_i_boxed_1480_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_res_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1469_, v___x_1470_, v___x_1471_, v_val_44823__boxed_1478_, v_as_1473_, v_sz_boxed_1479_, v_i_boxed_1480_, v_b_1476_);
lean_dec_ref(v_as_1473_);
lean_dec(v___x_1470_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, uint8_t v_val_1485_, lean_object* v_t_1486_, lean_object* v_init_1487_){
_start:
{
lean_object* v_root_1489_; lean_object* v_tail_1490_; lean_object* v___x_1491_; 
v_root_1489_ = lean_ctor_get(v_t_1486_, 0);
v_tail_1490_ = lean_ctor_get(v_t_1486_, 1);
lean_inc_ref(v___x_1484_);
lean_inc_ref(v___x_1482_);
lean_inc_ref(v_init_1487_);
v___x_1491_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1487_, v___x_1482_, v___x_1483_, v___x_1484_, v_val_1485_, v_root_1489_, v_init_1487_);
lean_dec_ref(v_init_1487_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; 
lean_dec_ref(v___x_1484_);
lean_dec_ref(v___x_1482_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v___x_1491_);
return v_a_1492_;
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; size_t v_sz_1496_; size_t v___x_1497_; lean_object* v___x_1498_; lean_object* v_fst_1499_; 
v_a_1493_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1491_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_a_1493_);
v_sz_1496_ = lean_array_size(v_tail_1490_);
v___x_1497_ = ((size_t)0ULL);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1482_, v___x_1483_, v___x_1484_, v_val_1485_, v_tail_1490_, v_sz_1496_, v___x_1497_, v___x_1495_);
v_fst_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_fst_1499_);
if (lean_obj_tag(v_fst_1499_) == 0)
{
lean_object* v_snd_1500_; 
v_snd_1500_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_snd_1500_);
lean_dec_ref(v___x_1498_);
return v_snd_1500_;
}
else
{
lean_object* v_val_1501_; 
lean_dec_ref(v___x_1498_);
v_val_1501_ = lean_ctor_get(v_fst_1499_, 0);
lean_inc(v_val_1501_);
lean_dec_ref(v_fst_1499_);
return v_val_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1502_, lean_object* v___x_1503_, lean_object* v___x_1504_, lean_object* v_val_1505_, lean_object* v_t_1506_, lean_object* v_init_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_val_44874__boxed_1509_; lean_object* v_res_1510_; 
v_val_44874__boxed_1509_ = lean_unbox(v_val_1505_);
v_res_1510_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1502_, v___x_1503_, v___x_1504_, v_val_44874__boxed_1509_, v_t_1506_, v_init_1507_);
lean_dec_ref(v_t_1506_);
lean_dec(v___x_1503_);
return v_res_1510_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = l_Lean_firstFrontendMacroScope;
v___x_1513_ = lean_nat_add(v___x_1512_, v___x_1511_);
return v___x_1513_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, size_t v___x_1528_, uint8_t v___x_1529_, lean_object* v_env_1530_, lean_object* v___x_1531_, lean_object* v___x_1532_, lean_object* v_a_1533_, lean_object* v_opts_1534_, lean_object* v___x_1535_, lean_object* v_pos_1536_, uint8_t v_val_1537_, lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v___x_1540_, lean_object* v___x_1541_, uint8_t v___x_1542_, lean_object* v_x_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_toProcessingContext_1564_; lean_object* v_fileName_1565_; lean_object* v_fileMap_1566_; lean_object* v_env_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; lean_object* v_fileName_1573_; lean_object* v_fileMap_1574_; lean_object* v_currRecDepth_1575_; lean_object* v_ref_1576_; lean_object* v_currNamespace_1577_; lean_object* v_openDecls_1578_; lean_object* v_initHeartbeats_1579_; lean_object* v_maxHeartbeats_1580_; lean_object* v_quotContext_1581_; lean_object* v_currMacroScope_1582_; lean_object* v_cancelTk_x3f_1583_; uint8_t v_suppressElabErrors_1584_; lean_object* v_inheritedTraceOptions_1585_; lean_object* v___y_1586_; uint8_t v___y_1603_; uint8_t v___x_1623_; 
v___x_1545_ = l_Lean_firstFrontendMacroScope;
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_1548_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_1549_ = lean_box(0);
lean_inc(v___x_1525_);
v___x_1550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1525_);
lean_ctor_set(v___x_1550_, 1, v___x_1546_);
lean_ctor_set(v___x_1550_, 2, v___x_1549_);
v___x_1551_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1552_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
v___x_1553_ = lean_mk_empty_array_with_capacity(v___x_1526_);
lean_inc_ref(v___x_1553_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_inc_n(v___x_1527_, 2);
v___x_1555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
lean_ctor_set(v___x_1555_, 2, v___x_1527_);
lean_ctor_set(v___x_1555_, 3, v___x_1527_);
lean_ctor_set_usize(v___x_1555_, 4, v___x_1528_);
v___x_1556_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1555_, 2);
v___x_1557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1555_);
lean_ctor_set(v___x_1557_, 2, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1558_, 0, v___x_1551_);
lean_ctor_set(v___x_1558_, 1, v___x_1551_);
lean_ctor_set(v___x_1558_, 2, v___x_1555_);
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*3, v___x_1529_);
v___x_1559_ = lean_mk_empty_array_with_capacity(v___x_1527_);
lean_inc_ref(v___x_1559_);
lean_inc_ref(v___x_1531_);
v___x_1560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1560_, 0, v_env_1530_);
lean_ctor_set(v___x_1560_, 1, v___x_1547_);
lean_ctor_set(v___x_1560_, 2, v___x_1548_);
lean_ctor_set(v___x_1560_, 3, v___x_1550_);
lean_ctor_set(v___x_1560_, 4, v___x_1531_);
lean_ctor_set(v___x_1560_, 5, v___x_1552_);
lean_ctor_set(v___x_1560_, 6, v___x_1557_);
lean_ctor_set(v___x_1560_, 7, v___x_1558_);
lean_ctor_set(v___x_1560_, 8, v___x_1559_);
v___x_1561_ = lean_st_mk_ref(v___x_1560_);
v___x_1562_ = lean_st_ref_get(v___x_1532_);
v___x_1563_ = lean_st_ref_get(v___x_1561_);
v_toProcessingContext_1564_ = lean_ctor_get(v_a_1533_, 0);
v_fileName_1565_ = lean_ctor_get(v_toProcessingContext_1564_, 1);
v_fileMap_1566_ = lean_ctor_get(v_toProcessingContext_1564_, 2);
v_env_1567_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_env_1567_);
lean_dec(v___x_1563_);
v___x_1568_ = lean_box(0);
v___x_1569_ = l_Lean_Core_getMaxHeartbeats(v_opts_1534_);
v___x_1570_ = l_Lean_diagnostics;
v___x_1571_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1534_, v___x_1570_);
v___x_1623_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1567_);
lean_dec_ref(v_env_1567_);
if (v___x_1623_ == 0)
{
if (v___x_1571_ == 0)
{
v___y_1603_ = v___x_1542_;
goto v___jp_1602_;
}
else
{
v___y_1603_ = v___x_1623_;
goto v___jp_1602_;
}
}
else
{
v___y_1603_ = v___x_1571_;
goto v___jp_1602_;
}
v___jp_1572_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1587_ = l_Lean_maxRecDepth;
v___x_1588_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1534_, v___x_1587_);
lean_inc(v_currMacroScope_1582_);
lean_inc(v_openDecls_1578_);
lean_inc(v_ref_1576_);
v___x_1589_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1589_, 0, v_fileName_1573_);
lean_ctor_set(v___x_1589_, 1, v_fileMap_1574_);
lean_ctor_set(v___x_1589_, 2, v_opts_1534_);
lean_ctor_set(v___x_1589_, 3, v_currRecDepth_1575_);
lean_ctor_set(v___x_1589_, 4, v___x_1588_);
lean_ctor_set(v___x_1589_, 5, v_ref_1576_);
lean_ctor_set(v___x_1589_, 6, v_currNamespace_1577_);
lean_ctor_set(v___x_1589_, 7, v_openDecls_1578_);
lean_ctor_set(v___x_1589_, 8, v_initHeartbeats_1579_);
lean_ctor_set(v___x_1589_, 9, v_maxHeartbeats_1580_);
lean_ctor_set(v___x_1589_, 10, v_quotContext_1581_);
lean_ctor_set(v___x_1589_, 11, v_currMacroScope_1582_);
lean_ctor_set(v___x_1589_, 12, v_cancelTk_x3f_1583_);
lean_ctor_set(v___x_1589_, 13, v_inheritedTraceOptions_1585_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*14, v___x_1571_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*14 + 1, v_suppressElabErrors_1584_);
v___x_1590_ = l_Lean_Language_SnapshotTree_trace(v___x_1535_, v___x_1589_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1591_; lean_object* v_traceState_1592_; lean_object* v_traces_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1540_);
v___x_1591_ = lean_st_ref_get(v___x_1561_);
lean_dec(v___x_1561_);
v_traceState_1592_ = lean_ctor_get(v___x_1591_, 4);
lean_inc_ref(v_traceState_1592_);
lean_dec(v___x_1591_);
v_traces_1593_ = lean_ctor_get(v_traceState_1592_, 0);
lean_inc_ref(v_traces_1593_);
lean_dec_ref(v_traceState_1592_);
v___x_1594_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1565_);
lean_inc_ref(v_fileMap_1566_);
v___x_1595_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_1566_, v_pos_1536_, v_fileName_1565_, v_val_1537_, v_traces_1593_, v___x_1594_);
lean_dec_ref(v_traces_1593_);
v___x_1596_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1595_);
v___x_1597_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1597_, 0, v___x_1538_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
lean_ctor_set(v___x_1597_, 2, v___x_1539_);
lean_ctor_set(v___x_1597_, 3, v___x_1531_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*4, v_val_1537_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1559_);
v___x_1599_ = lean_task_pure(v___x_1598_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v___x_1590_);
lean_dec(v___x_1561_);
lean_dec(v___x_1539_);
lean_dec_ref(v___x_1538_);
lean_dec_ref(v___x_1531_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1540_);
lean_ctor_set(v___x_1600_, 1, v___x_1559_);
v___x_1601_ = lean_task_pure(v___x_1600_);
return v___x_1601_;
}
}
v___jp_1602_:
{
if (v___y_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_traceState_1609_; lean_object* v_messages_1610_; lean_object* v_infoState_1611_; lean_object* v_snapshotTasks_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1621_; 
v___x_1604_ = lean_st_ref_take(v___x_1561_);
v_env_1605_ = lean_ctor_get(v___x_1604_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1604_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1604_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1604_, 3);
v_traceState_1609_ = lean_ctor_get(v___x_1604_, 4);
v_messages_1610_ = lean_ctor_get(v___x_1604_, 6);
v_infoState_1611_ = lean_ctor_get(v___x_1604_, 7);
v_snapshotTasks_1612_ = lean_ctor_get(v___x_1604_, 8);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1604_, 5);
lean_dec(v_unused_1622_);
v___x_1614_ = v___x_1604_;
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_snapshotTasks_1612_);
lean_inc(v_infoState_1611_);
lean_inc(v_messages_1610_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1604_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = l_Lean_Kernel_enableDiag(v_env_1605_, v___x_1571_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 5, v___x_1552_);
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_traceState_1609_);
lean_ctor_set(v_reuseFailAlloc_1620_, 5, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1620_, 6, v_messages_1610_);
lean_ctor_set(v_reuseFailAlloc_1620_, 7, v_infoState_1611_);
lean_ctor_set(v_reuseFailAlloc_1620_, 8, v_snapshotTasks_1612_);
v___x_1618_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_st_ref_set(v___x_1561_, v___x_1618_);
lean_inc(v___x_1561_);
lean_inc(v___x_1525_);
lean_inc(v___x_1527_);
lean_inc_ref(v_fileMap_1566_);
lean_inc_ref(v_fileName_1565_);
v_fileName_1573_ = v_fileName_1565_;
v_fileMap_1574_ = v_fileMap_1566_;
v_currRecDepth_1575_ = v___x_1527_;
v_ref_1576_ = v___x_1568_;
v_currNamespace_1577_ = v___x_1525_;
v_openDecls_1578_ = v___x_1549_;
v_initHeartbeats_1579_ = v___x_1527_;
v_maxHeartbeats_1580_ = v___x_1569_;
v_quotContext_1581_ = v___x_1525_;
v_currMacroScope_1582_ = v___x_1545_;
v_cancelTk_x3f_1583_ = v___x_1541_;
v_suppressElabErrors_1584_ = v_val_1537_;
v_inheritedTraceOptions_1585_ = v___x_1562_;
v___y_1586_ = v___x_1561_;
goto v___jp_1572_;
}
}
}
else
{
lean_inc(v___x_1561_);
lean_inc(v___x_1525_);
lean_inc(v___x_1527_);
lean_inc_ref(v_fileMap_1566_);
lean_inc_ref(v_fileName_1565_);
v_fileName_1573_ = v_fileName_1565_;
v_fileMap_1574_ = v_fileMap_1566_;
v_currRecDepth_1575_ = v___x_1527_;
v_ref_1576_ = v___x_1568_;
v_currNamespace_1577_ = v___x_1525_;
v_openDecls_1578_ = v___x_1549_;
v_initHeartbeats_1579_ = v___x_1527_;
v_maxHeartbeats_1580_ = v___x_1569_;
v_quotContext_1581_ = v___x_1525_;
v_currMacroScope_1582_ = v___x_1545_;
v_cancelTk_x3f_1583_ = v___x_1541_;
v_suppressElabErrors_1584_ = v_val_1537_;
v_inheritedTraceOptions_1585_ = v___x_1562_;
v___y_1586_ = v___x_1561_;
goto v___jp_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_1624_ = _args[0];
lean_object* v___x_1625_ = _args[1];
lean_object* v___x_1626_ = _args[2];
lean_object* v___x_1627_ = _args[3];
lean_object* v___x_1628_ = _args[4];
lean_object* v_env_1629_ = _args[5];
lean_object* v___x_1630_ = _args[6];
lean_object* v___x_1631_ = _args[7];
lean_object* v_a_1632_ = _args[8];
lean_object* v_opts_1633_ = _args[9];
lean_object* v___x_1634_ = _args[10];
lean_object* v_pos_1635_ = _args[11];
lean_object* v_val_1636_ = _args[12];
lean_object* v___x_1637_ = _args[13];
lean_object* v___x_1638_ = _args[14];
lean_object* v___x_1639_ = _args[15];
lean_object* v___x_1640_ = _args[16];
lean_object* v___x_1641_ = _args[17];
lean_object* v_x_1642_ = _args[18];
lean_object* v___y_1643_ = _args[19];
_start:
{
size_t v___x_44935__boxed_1644_; uint8_t v___x_44936__boxed_1645_; uint8_t v_val_44940__boxed_1646_; uint8_t v___x_44945__boxed_1647_; lean_object* v_res_1648_; 
v___x_44935__boxed_1644_ = lean_unbox_usize(v___x_1627_);
lean_dec(v___x_1627_);
v___x_44936__boxed_1645_ = lean_unbox(v___x_1628_);
v_val_44940__boxed_1646_ = lean_unbox(v_val_1636_);
v___x_44945__boxed_1647_ = lean_unbox(v___x_1641_);
v_res_1648_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1624_, v___x_1625_, v___x_1626_, v___x_44935__boxed_1644_, v___x_44936__boxed_1645_, v_env_1629_, v___x_1630_, v___x_1631_, v_a_1632_, v_opts_1633_, v___x_1634_, v_pos_1635_, v_val_44940__boxed_1646_, v___x_1637_, v___x_1638_, v___x_1639_, v___x_1640_, v___x_44945__boxed_1647_, v_x_1642_);
lean_dec(v_pos_1635_);
lean_dec_ref(v_a_1632_);
lean_dec(v___x_1631_);
lean_dec(v___x_1625_);
return v_res_1648_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1655_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1656_ = l_Lean_Name_append(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1657_, lean_object* v___x_1658_, uint8_t v_val_1659_, lean_object* v_val_1660_, lean_object* v_val_1661_, lean_object* v___x_1662_, lean_object* v___x_1663_, uint8_t v___x_1664_, lean_object* v_a_1665_, lean_object* v_pos_1666_, lean_object* v_infoSt_1667_){
_start:
{
lean_object* v___y_1670_; lean_object* v_msgLog_1671_; lean_object* v___y_1677_; lean_object* v_trees_1709_; lean_object* v_size_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_trees_1709_ = lean_ctor_get(v_infoSt_1667_, 2);
v_size_1710_ = lean_ctor_get(v_trees_1709_, 2);
v___x_1711_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1712_ = lean_nat_dec_lt(v___x_1663_, v_size_1710_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
v___x_1713_ = l_outOfBounds___redArg(v___x_1711_);
v___y_1677_ = v___x_1713_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1711_, v_trees_1709_, v___x_1663_);
v___y_1677_ = v___x_1714_;
goto v___jp_1676_;
}
v___jp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1672_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1671_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1670_);
v___x_1674_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1674_, 0, v___x_1657_);
lean_ctor_set(v___x_1674_, 1, v___x_1672_);
lean_ctor_set(v___x_1674_, 2, v___x_1673_);
lean_ctor_set(v___x_1674_, 3, v___x_1658_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*4, v_val_1659_);
v___x_1675_ = lean_io_promise_resolve(v___x_1674_, v_val_1660_);
return v___x_1675_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_scopes_1680_; lean_object* v___x_1681_; lean_object* v_opts_1682_; uint8_t v_hasTrace_1683_; lean_object* v___x_1684_; 
v___x_1678_ = l_Lean_inheritedTraceOptions;
v___x_1679_ = lean_st_ref_get(v___x_1678_);
v_scopes_1680_ = lean_ctor_get(v_val_1661_, 2);
v___x_1681_ = l_List_head_x21___redArg(v___x_1662_, v_scopes_1680_);
v_opts_1682_ = lean_ctor_get(v___x_1681_, 1);
lean_inc_ref(v_opts_1682_);
lean_dec(v___x_1681_);
v_hasTrace_1683_ = lean_ctor_get_uint8(v_opts_1682_, sizeof(void*)*1);
v___x_1684_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1683_ == 0)
{
lean_dec_ref(v_opts_1682_);
lean_dec(v___x_1679_);
lean_dec(v___x_1663_);
v___y_1670_ = v___y_1677_;
v_msgLog_1671_ = v___x_1684_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1686_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1687_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1679_, v_opts_1682_, v___x_1687_);
lean_dec_ref(v_opts_1682_);
lean_dec(v___x_1679_);
if (v___x_1688_ == 0)
{
lean_dec(v___x_1663_);
v___y_1670_ = v___y_1677_;
v_msgLog_1671_ = v___x_1684_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_box(0);
lean_inc_ref(v___y_1677_);
v___x_1690_ = l_Lean_Elab_InfoTree_format(v___y_1677_, v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; double v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_toProcessingContext_1695_; lean_object* v_fileName_1696_; lean_object* v_fileMap_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = lean_float_of_nat(v___x_1663_);
v___x_1693_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1694_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1694_, 0, v___x_1685_);
lean_ctor_set(v___x_1694_, 1, v___x_1689_);
lean_ctor_set(v___x_1694_, 2, v___x_1693_);
lean_ctor_set_float(v___x_1694_, sizeof(void*)*3, v___x_1692_);
lean_ctor_set_float(v___x_1694_, sizeof(void*)*3 + 8, v___x_1692_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 16, v___x_1664_);
v_toProcessingContext_1695_ = lean_ctor_get(v_a_1665_, 0);
v_fileName_1696_ = lean_ctor_get(v_toProcessingContext_1695_, 1);
v_fileMap_1697_ = lean_ctor_get(v_toProcessingContext_1695_, 2);
v___x_1698_ = l_Lean_MessageData_nil;
v___x_1699_ = l_Lean_MessageData_ofFormat(v_a_1691_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_mk_empty_array_with_capacity(v___x_1700_);
v___x_1702_ = lean_array_push(v___x_1701_, v___x_1699_);
v___x_1703_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1694_);
lean_ctor_set(v___x_1703_, 1, v___x_1698_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1686_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
lean_inc_ref(v_fileMap_1697_);
v___x_1705_ = l_Lean_FileMap_toPosition(v_fileMap_1697_, v_pos_1666_);
v___x_1706_ = 0;
lean_inc_ref(v_fileName_1696_);
v___x_1707_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1707_, 0, v_fileName_1696_);
lean_ctor_set(v___x_1707_, 1, v___x_1705_);
lean_ctor_set(v___x_1707_, 2, v___x_1689_);
lean_ctor_set(v___x_1707_, 3, v___x_1693_);
lean_ctor_set(v___x_1707_, 4, v___x_1704_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*5, v_val_1659_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*5 + 1, v___x_1706_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*5 + 2, v_val_1659_);
v___x_1708_ = l_Lean_MessageLog_add(v___x_1707_, v___x_1684_);
v___y_1670_ = v___y_1677_;
v_msgLog_1671_ = v___x_1708_;
goto v___jp_1669_;
}
else
{
lean_dec_ref(v___x_1690_);
lean_dec(v___x_1663_);
v___y_1670_ = v___y_1677_;
v_msgLog_1671_ = v___x_1684_;
goto v___jp_1669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_val_1717_, lean_object* v_val_1718_, lean_object* v_val_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_a_1723_, lean_object* v_pos_1724_, lean_object* v_infoSt_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v_val_45122__boxed_1727_; uint8_t v___x_45127__boxed_1728_; lean_object* v_res_1729_; 
v_val_45122__boxed_1727_ = lean_unbox(v_val_1717_);
v___x_45127__boxed_1728_ = lean_unbox(v___x_1722_);
v_res_1729_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1715_, v___x_1716_, v_val_45122__boxed_1727_, v_val_1718_, v_val_1719_, v___x_1720_, v___x_1721_, v___x_45127__boxed_1728_, v_a_1723_, v_pos_1724_, v_infoSt_1725_);
lean_dec_ref(v_infoSt_1725_);
lean_dec(v_pos_1724_);
lean_dec_ref(v_a_1723_);
lean_dec_ref(v___x_1720_);
lean_dec_ref(v_val_1719_);
lean_dec(v_val_1718_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1731_, size_t v_i_1732_, size_t v_stop_1733_, lean_object* v_b_1734_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_eq(v_i_1732_, v_stop_1733_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; 
v___x_1737_ = lean_array_uget_borrowed(v_as_1731_, v_i_1732_);
v___f_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1737_);
v___x_1739_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1738_, v___x_1737_);
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_add(v_i_1732_, v___x_1740_);
v_i_1732_ = v___x_1741_;
v_b_1734_ = v___x_1739_;
goto _start;
}
else
{
return v_b_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_stop_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_){
_start:
{
size_t v_i_boxed_1748_; size_t v_stop_boxed_1749_; lean_object* v_res_1750_; 
v_i_boxed_1748_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_stop_boxed_1749_ = lean_unbox_usize(v_stop_1745_);
lean_dec(v_stop_1745_);
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1743_, v_i_boxed_1748_, v_stop_boxed_1749_, v_b_1746_);
lean_dec_ref(v_as_1743_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1751_, lean_object* v_newParserState_1752_, lean_object* v_val_1753_, lean_object* v_sync_1754_, lean_object* v_val_1755_, lean_object* v_a_1756_, lean_object* v_oldNext_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v_sync_boxed_1759_; lean_object* v_res_1760_; 
v_sync_boxed_1759_ = lean_unbox(v_sync_1754_);
v_res_1760_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1751_, v_newParserState_1752_, v_val_1753_, v_sync_boxed_1759_, v_val_1755_, v_a_1756_, v_oldNext_1757_);
lean_dec_ref(v_a_1756_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1761_, lean_object* v_newParserState_1762_, lean_object* v_val_1763_, uint8_t v_sync_1764_, lean_object* v_val_1765_, lean_object* v_a_1766_, lean_object* v_oldResult_1767_){
_start:
{
lean_object* v_task_1769_; lean_object* v___x_1770_; lean_object* v___f_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v_task_1769_ = lean_ctor_get(v_val_1761_, 3);
lean_inc_ref(v_task_1769_);
lean_dec_ref(v_val_1761_);
v___x_1770_ = lean_box(v_sync_1764_);
lean_inc_ref(v_a_1766_);
v___f_1771_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 8, 6);
lean_closure_set(v___f_1771_, 0, v_oldResult_1767_);
lean_closure_set(v___f_1771_, 1, v_newParserState_1762_);
lean_closure_set(v___f_1771_, 2, v_val_1763_);
lean_closure_set(v___f_1771_, 3, v___x_1770_);
lean_closure_set(v___f_1771_, 4, v_val_1765_);
lean_closure_set(v___f_1771_, 5, v_a_1766_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = 1;
v___x_1774_ = l_BaseIO_chainTask___redArg(v_task_1769_, v___f_1771_, v___x_1772_, v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1775_, lean_object* v_newParserState_1776_, lean_object* v_val_1777_, lean_object* v_sync_1778_, lean_object* v_val_1779_, lean_object* v_a_1780_, lean_object* v_oldResult_1781_, lean_object* v___y_1782_){
_start:
{
uint8_t v_sync_boxed_1783_; lean_object* v_res_1784_; 
v_sync_boxed_1783_ = lean_unbox(v_sync_1778_);
v_res_1784_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1775_, v_newParserState_1776_, v_val_1777_, v_sync_boxed_1783_, v_val_1779_, v_a_1780_, v_oldResult_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1784_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1787_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1789_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1798_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1799_ = l_Lean_Name_append(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1803_, lean_object* v_val_1804_, lean_object* v_fst_1805_, uint8_t v_val_1806_, lean_object* v_a_1807_, lean_object* v_snd_1808_, lean_object* v___x_1809_, uint8_t v___x_1810_, lean_object* v_fst_1811_, lean_object* v_val_1812_, lean_object* v_val_1813_, lean_object* v_val_1814_, lean_object* v_snd_1815_, lean_object* v_prom_1816_, lean_object* v___x_1817_, lean_object* v___f_1818_, lean_object* v___f_1819_, lean_object* v___f_1820_, lean_object* v_pos_1821_, lean_object* v_fst_1822_, lean_object* v_cmdState_1823_, lean_object* v_opts_1824_, lean_object* v___x_1825_, lean_object* v_old_x3f_1826_, lean_object* v_parseCancelTk_1827_, lean_object* v_next_x3f_1828_){
_start:
{
lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v_snapshotTasks_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v_traceTask_1837_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; size_t v___y_1865_; lean_object* v___y_1866_; lean_object* v_env_1867_; lean_object* v_messages_1868_; lean_object* v_scopes_1869_; lean_object* v_infoState_1870_; lean_object* v_traceState_1871_; lean_object* v_snapshotTasks_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_reportedCmdState_1886_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; size_t v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v_reportedCmdState_1943_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; size_t v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; size_t v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_2006_; 
if (lean_obj_tag(v_next_x3f_1828_) == 0)
{
lean_object* v___x_2059_; 
lean_dec(v_parseCancelTk_1827_);
v___x_2059_ = lean_box(0);
v___y_2006_ = v___x_2059_;
goto v___jp_2005_;
}
else
{
lean_object* v_toProcessingContext_2060_; lean_object* v_val_2061_; lean_object* v_pos_2062_; lean_object* v_endPos_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_toProcessingContext_2060_ = lean_ctor_get(v_a_1807_, 0);
v_val_2061_ = lean_ctor_get(v_next_x3f_1828_, 0);
v_pos_2062_ = lean_ctor_get(v_fst_1805_, 0);
v_endPos_2063_ = lean_ctor_get(v_toProcessingContext_2060_, 3);
v___x_2064_ = lean_box(0);
lean_inc(v_endPos_2063_);
lean_inc(v_pos_2062_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v_pos_2062_);
lean_ctor_set(v___x_2065_, 1, v_endPos_2063_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_parseCancelTk_1827_);
v___x_2068_ = l_IO_Promise_result_x21___redArg(v_val_2061_);
v___x_2069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2064_);
lean_ctor_set(v___x_2069_, 1, v___x_2066_);
lean_ctor_set(v___x_2069_, 2, v___x_2067_);
lean_ctor_set(v___x_2069_, 3, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
v___y_2006_ = v___x_2070_;
goto v___jp_2005_;
}
v___jp_1830_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1838_, 0, v___y_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1803_);
lean_ctor_set(v___x_1838_, 2, v___y_1831_);
lean_ctor_set(v___x_1838_, 3, v_traceTask_1837_);
v___x_1839_ = lean_array_push(v_snapshotTasks_1833_, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___y_1834_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_io_promise_resolve(v___x_1840_, v_val_1804_);
if (lean_obj_tag(v_next_x3f_1828_) == 1)
{
lean_object* v_val_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_val_1842_ = lean_ctor_get(v_next_x3f_1828_, 0);
lean_inc(v_val_1842_);
lean_dec_ref(v_next_x3f_1828_);
v___x_1843_ = lean_box(0);
v___x_1844_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1843_, v_fst_1805_, v___y_1832_, v_val_1842_, v_val_1806_, v___y_1835_, v_a_1807_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; 
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1832_);
lean_dec(v_next_x3f_1828_);
lean_dec_ref(v_fst_1805_);
v___x_1845_ = lean_box(0);
return v___x_1845_;
}
}
v___jp_1846_:
{
lean_object* v_snapshotTasks_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_snapshotTasks_1853_ = lean_ctor_get(v___y_1847_, 10);
lean_inc_ref(v_snapshotTasks_1853_);
v___x_1854_ = lean_mk_empty_array_with_capacity(v___y_1849_);
lean_dec(v___y_1849_);
lean_inc_ref(v___y_1850_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___y_1850_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_task_pure(v___x_1855_);
v___y_1831_ = v___y_1848_;
v___y_1832_ = v___y_1847_;
v_snapshotTasks_1833_ = v_snapshotTasks_1853_;
v___y_1834_ = v___y_1850_;
v___y_1835_ = v___y_1851_;
v___y_1836_ = v___y_1852_;
v_traceTask_1837_ = v___x_1856_;
goto v___jp_1830_;
}
v___jp_1857_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_opts_1896_; uint8_t v_hasTrace_1897_; 
v___x_1887_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1868_);
v___x_1888_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1888_, 0, v___y_1880_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
lean_ctor_set(v___x_1888_, 2, v___y_1873_);
lean_ctor_set(v___x_1888_, 3, v_traceState_1871_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*4, v_val_1806_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_reportedCmdState_1886_);
v___x_1890_ = lean_io_promise_resolve(v___x_1889_, v_val_1813_);
v___x_1891_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1870_);
lean_inc(v___y_1874_);
v___x_1892_ = l_BaseIO_chainTask___redArg(v___x_1891_, v___y_1884_, v___y_1874_, v___x_1810_);
v___x_1893_ = l_Lean_inheritedTraceOptions;
v___x_1894_ = lean_st_ref_get(v___x_1893_);
v___x_1895_ = l_List_head_x21___redArg(v___x_1817_, v_scopes_1869_);
lean_dec(v_scopes_1869_);
lean_dec_ref(v___x_1817_);
v_opts_1896_ = lean_ctor_get(v___x_1895_, 1);
lean_inc_ref(v_opts_1896_);
lean_dec(v___x_1895_);
v_hasTrace_1897_ = lean_ctor_get_uint8(v_opts_1896_, sizeof(void*)*1);
if (v_hasTrace_1897_ == 0)
{
lean_dec_ref(v_opts_1896_);
lean_dec(v___x_1894_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v_snapshotTasks_1872_);
lean_dec_ref(v_env_1867_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1858_);
lean_dec(v_pos_1821_);
lean_dec_ref(v___f_1820_);
lean_dec_ref(v___f_1819_);
lean_dec_ref(v___f_1818_);
lean_dec(v___x_1809_);
v___y_1847_ = v___y_1866_;
v___y_1848_ = v___y_1879_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1881_;
v___y_1852_ = v___y_1878_;
goto v___jp_1846_;
}
else
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_1899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1894_, v_opts_1896_, v___x_1898_);
lean_dec(v___x_1894_);
if (v___x_1899_ == 0)
{
lean_dec_ref(v_opts_1896_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v_snapshotTasks_1872_);
lean_dec_ref(v_env_1867_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1858_);
lean_dec(v_pos_1821_);
lean_dec_ref(v___f_1820_);
lean_dec_ref(v___f_1819_);
lean_dec_ref(v___f_1818_);
lean_dec(v___x_1809_);
v___y_1847_ = v___y_1866_;
v___y_1848_ = v___y_1879_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1881_;
v___y_1852_ = v___y_1878_;
goto v___jp_1846_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; 
lean_inc_n(v___y_1874_, 3);
v___x_1900_ = lean_task_map(v___f_1818_, v___y_1885_, v___y_1874_, v___x_1810_);
lean_inc_n(v___y_1879_, 3);
lean_inc_n(v___y_1877_, 2);
lean_inc_n(v___y_1882_, 2);
v___x_1901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1901_, 0, v___y_1882_);
lean_ctor_set(v___x_1901_, 1, v___y_1877_);
lean_ctor_set(v___x_1901_, 2, v___y_1879_);
lean_ctor_set(v___x_1901_, 3, v___x_1900_);
v___x_1902_ = lean_task_map(v___f_1819_, v___y_1876_, v___y_1874_, v___x_1810_);
v___x_1903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1882_);
lean_ctor_set(v___x_1903_, 1, v___y_1877_);
lean_ctor_set(v___x_1903_, 2, v___y_1879_);
lean_ctor_set(v___x_1903_, 3, v___x_1902_);
v___x_1904_ = lean_task_map(v___f_1820_, v___y_1883_, v___y_1874_, v___x_1810_);
v___x_1905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1905_, 0, v___y_1882_);
lean_ctor_set(v___x_1905_, 1, v___y_1877_);
lean_ctor_set(v___x_1905_, 2, v___y_1879_);
lean_ctor_set(v___x_1905_, 3, v___x_1904_);
v___x_1906_ = lean_unsigned_to_nat(3u);
v___x_1907_ = lean_mk_empty_array_with_capacity(v___x_1906_);
v___x_1908_ = lean_array_push(v___x_1907_, v___x_1901_);
v___x_1909_ = lean_array_push(v___x_1908_, v___x_1903_);
v___x_1910_ = lean_array_push(v___x_1909_, v___x_1905_);
v___x_1911_ = l_Array_append___redArg(v___x_1910_, v_snapshotTasks_1872_);
lean_inc_ref(v___y_1875_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___y_1875_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
lean_inc_ref(v___x_1912_);
v___x_1913_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1912_);
v___x_1914_ = lean_box_usize(v___y_1865_);
v___x_1915_ = lean_box(v___x_1810_);
v___x_1916_ = lean_box(v_val_1806_);
v___x_1917_ = lean_box(v___x_1899_);
lean_inc_ref(v_a_1807_);
lean_inc_ref(v___y_1859_);
v___f_1918_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_1918_, 0, v___x_1809_);
lean_closure_set(v___f_1918_, 1, v___y_1861_);
lean_closure_set(v___f_1918_, 2, v___y_1863_);
lean_closure_set(v___f_1918_, 3, v___x_1914_);
lean_closure_set(v___f_1918_, 4, v___x_1915_);
lean_closure_set(v___f_1918_, 5, v_env_1867_);
lean_closure_set(v___f_1918_, 6, v___y_1859_);
lean_closure_set(v___f_1918_, 7, v___x_1893_);
lean_closure_set(v___f_1918_, 8, v_a_1807_);
lean_closure_set(v___f_1918_, 9, v_opts_1896_);
lean_closure_set(v___f_1918_, 10, v___x_1912_);
lean_closure_set(v___f_1918_, 11, v_pos_1821_);
lean_closure_set(v___f_1918_, 12, v___x_1916_);
lean_closure_set(v___f_1918_, 13, v___y_1860_);
lean_closure_set(v___f_1918_, 14, v___y_1864_);
lean_closure_set(v___f_1918_, 15, v___y_1862_);
lean_closure_set(v___f_1918_, 16, v___y_1858_);
lean_closure_set(v___f_1918_, 17, v___x_1917_);
v___x_1919_ = lean_io_bind_task(v___x_1913_, v___f_1918_, v___y_1874_, v_val_1806_);
v___y_1831_ = v___y_1879_;
v___y_1832_ = v___y_1866_;
v_snapshotTasks_1833_ = v_snapshotTasks_1872_;
v___y_1834_ = v___y_1875_;
v___y_1835_ = v___y_1881_;
v___y_1836_ = v___y_1878_;
v_traceTask_1837_ = v___x_1919_;
goto v___jp_1830_;
}
}
}
v___jp_1920_:
{
lean_object* v_env_1944_; lean_object* v_messages_1945_; lean_object* v_scopes_1946_; lean_object* v_infoState_1947_; lean_object* v_traceState_1948_; lean_object* v_snapshotTasks_1949_; 
v_env_1944_ = lean_ctor_get(v___y_1929_, 0);
lean_inc_ref(v_env_1944_);
v_messages_1945_ = lean_ctor_get(v___y_1929_, 1);
lean_inc_ref(v_messages_1945_);
v_scopes_1946_ = lean_ctor_get(v___y_1929_, 2);
lean_inc(v_scopes_1946_);
v_infoState_1947_ = lean_ctor_get(v___y_1929_, 8);
lean_inc_ref(v_infoState_1947_);
v_traceState_1948_ = lean_ctor_get(v___y_1929_, 9);
lean_inc_ref(v_traceState_1948_);
v_snapshotTasks_1949_ = lean_ctor_get(v___y_1929_, 10);
lean_inc_ref(v_snapshotTasks_1949_);
v___y_1858_ = v___y_1921_;
v___y_1859_ = v___y_1922_;
v___y_1860_ = v___y_1923_;
v___y_1861_ = v___y_1924_;
v___y_1862_ = v___y_1926_;
v___y_1863_ = v___y_1925_;
v___y_1864_ = v___y_1927_;
v___y_1865_ = v___y_1928_;
v___y_1866_ = v___y_1929_;
v_env_1867_ = v_env_1944_;
v_messages_1868_ = v_messages_1945_;
v_scopes_1869_ = v_scopes_1946_;
v_infoState_1870_ = v_infoState_1947_;
v_traceState_1871_ = v_traceState_1948_;
v_snapshotTasks_1872_ = v_snapshotTasks_1949_;
v___y_1873_ = v___y_1930_;
v___y_1874_ = v___y_1931_;
v___y_1875_ = v___y_1932_;
v___y_1876_ = v___y_1933_;
v___y_1877_ = v___y_1934_;
v___y_1878_ = v___y_1935_;
v___y_1879_ = v___y_1936_;
v___y_1880_ = v___y_1937_;
v___y_1881_ = v___y_1938_;
v___y_1882_ = v___y_1939_;
v___y_1883_ = v___y_1940_;
v___y_1884_ = v___y_1941_;
v___y_1885_ = v___y_1942_;
v_reportedCmdState_1886_ = v_reportedCmdState_1943_;
goto v___jp_1857_;
}
v___jp_1950_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; uint8_t v___x_1980_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1974_);
lean_ctor_set(v___x_1975_, 1, v_val_1812_);
lean_inc(v___y_1969_);
lean_inc_n(v_pos_1821_, 2);
lean_inc(v_fst_1822_);
v___x_1976_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1822_, v_cmdState_1823_, v_pos_1821_, v___x_1975_, v___y_1969_, v_a_1807_);
v___x_1977_ = lean_box(v_val_1806_);
v___x_1978_ = lean_box(v___x_1810_);
lean_inc_ref(v_a_1807_);
lean_inc(v___y_1956_);
lean_inc_ref(v___x_1817_);
lean_inc_ref(v___x_1976_);
lean_inc_ref(v___y_1952_);
lean_inc_ref(v___y_1953_);
v___f_1979_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1979_, 0, v___y_1953_);
lean_closure_set(v___f_1979_, 1, v___y_1952_);
lean_closure_set(v___f_1979_, 2, v___x_1977_);
lean_closure_set(v___f_1979_, 3, v_val_1814_);
lean_closure_set(v___f_1979_, 4, v___x_1976_);
lean_closure_set(v___f_1979_, 5, v___x_1817_);
lean_closure_set(v___f_1979_, 6, v___y_1956_);
lean_closure_set(v___f_1979_, 7, v___x_1978_);
lean_closure_set(v___f_1979_, 8, v_a_1807_);
lean_closure_set(v___f_1979_, 9, v_pos_1821_);
v___x_1980_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1824_, v___x_1825_);
if (v___x_1980_ == 0)
{
lean_dec(v___y_1960_);
lean_dec(v_fst_1822_);
lean_inc_ref(v___x_1976_);
v___y_1921_ = v___y_1951_;
v___y_1922_ = v___y_1952_;
v___y_1923_ = v___y_1953_;
v___y_1924_ = v___y_1954_;
v___y_1925_ = v___y_1956_;
v___y_1926_ = v___y_1955_;
v___y_1927_ = v___y_1957_;
v___y_1928_ = v___y_1958_;
v___y_1929_ = v___x_1976_;
v___y_1930_ = v___y_1959_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1966_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1969_;
v___y_1939_ = v___y_1970_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___f_1979_;
v___y_1942_ = v___y_1973_;
v_reportedCmdState_1943_ = v___x_1976_;
goto v___jp_1920_;
}
else
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Parser_isTerminalCommand(v_fst_1822_);
if (v___x_1981_ == 0)
{
if (v___x_1980_ == 0)
{
lean_dec(v___y_1960_);
lean_inc_ref(v___x_1976_);
v___y_1921_ = v___y_1951_;
v___y_1922_ = v___y_1952_;
v___y_1923_ = v___y_1953_;
v___y_1924_ = v___y_1954_;
v___y_1925_ = v___y_1956_;
v___y_1926_ = v___y_1955_;
v___y_1927_ = v___y_1957_;
v___y_1928_ = v___y_1958_;
v___y_1929_ = v___x_1976_;
v___y_1930_ = v___y_1959_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1966_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1969_;
v___y_1939_ = v___y_1970_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___f_1979_;
v___y_1942_ = v___y_1973_;
v_reportedCmdState_1943_ = v___x_1976_;
goto v___jp_1920_;
}
else
{
lean_object* v_env_1982_; lean_object* v_messages_1983_; lean_object* v_scopes_1984_; lean_object* v_infoState_1985_; lean_object* v_traceState_1986_; lean_object* v_snapshotTasks_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_env_1982_ = lean_ctor_get(v___x_1976_, 0);
lean_inc_ref_n(v_env_1982_, 2);
v_messages_1983_ = lean_ctor_get(v___x_1976_, 1);
lean_inc_ref(v_messages_1983_);
v_scopes_1984_ = lean_ctor_get(v___x_1976_, 2);
lean_inc(v_scopes_1984_);
v_infoState_1985_ = lean_ctor_get(v___x_1976_, 8);
lean_inc_ref(v_infoState_1985_);
v_traceState_1986_ = lean_ctor_get(v___x_1976_, 9);
lean_inc_ref(v_traceState_1986_);
v_snapshotTasks_1987_ = lean_ctor_get(v___x_1976_, 10);
lean_inc_ref(v_snapshotTasks_1987_);
v___x_1988_ = lean_mk_empty_array_with_capacity(v___y_1960_);
lean_dec(v___y_1960_);
lean_inc_ref(v___x_1988_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_inc_n(v___y_1961_, 3);
v___x_1990_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v___x_1988_);
lean_ctor_set(v___x_1990_, 2, v___y_1961_);
lean_ctor_set(v___x_1990_, 3, v___y_1961_);
lean_ctor_set_usize(v___x_1990_, 4, v___y_1972_);
v___x_1991_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1990_, 2);
v___x_1992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1990_);
lean_ctor_set(v___x_1992_, 2, v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1994_ = l_Lean_Options_empty;
v___x_1995_ = lean_box(0);
v___x_1996_ = lean_mk_empty_array_with_capacity(v___y_1961_);
lean_inc_ref_n(v___x_1996_, 2);
lean_inc_n(v___x_1809_, 2);
v___x_1997_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_1997_, 0, v___x_1993_);
lean_ctor_set(v___x_1997_, 1, v___x_1994_);
lean_ctor_set(v___x_1997_, 2, v___x_1809_);
lean_ctor_set(v___x_1997_, 3, v___x_1995_);
lean_ctor_set(v___x_1997_, 4, v___x_1995_);
lean_ctor_set(v___x_1997_, 5, v___x_1996_);
lean_ctor_set(v___x_1997_, 6, v___x_1996_);
lean_ctor_set(v___x_1997_, 7, v___x_1995_);
lean_ctor_set(v___x_1997_, 8, v___x_1995_);
lean_ctor_set(v___x_1997_, 9, v___x_1995_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*10, v_val_1806_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*10 + 1, v_val_1806_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*10 + 2, v_val_1806_);
v___x_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___x_1995_);
v___x_1999_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2000_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2001_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1809_);
v___x_2002_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2003_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
lean_ctor_set(v___x_2003_, 2, v___x_1990_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*3, v___x_1810_);
lean_inc_ref(v___y_1967_);
v___x_2004_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2004_, 0, v_env_1982_);
lean_ctor_set(v___x_2004_, 1, v___x_1992_);
lean_ctor_set(v___x_2004_, 2, v___x_1998_);
lean_ctor_set(v___x_2004_, 3, v___x_1991_);
lean_ctor_set(v___x_2004_, 4, v___x_1999_);
lean_ctor_set(v___x_2004_, 5, v___y_1961_);
lean_ctor_set(v___x_2004_, 6, v___x_2000_);
lean_ctor_set(v___x_2004_, 7, v___x_2001_);
lean_ctor_set(v___x_2004_, 8, v___x_2003_);
lean_ctor_set(v___x_2004_, 9, v___y_1967_);
lean_ctor_set(v___x_2004_, 10, v___x_1996_);
v___y_1858_ = v___y_1951_;
v___y_1859_ = v___y_1952_;
v___y_1860_ = v___y_1953_;
v___y_1861_ = v___y_1954_;
v___y_1862_ = v___y_1955_;
v___y_1863_ = v___y_1956_;
v___y_1864_ = v___y_1957_;
v___y_1865_ = v___y_1958_;
v___y_1866_ = v___x_1976_;
v_env_1867_ = v_env_1982_;
v_messages_1868_ = v_messages_1983_;
v_scopes_1869_ = v_scopes_1984_;
v_infoState_1870_ = v_infoState_1985_;
v_traceState_1871_ = v_traceState_1986_;
v_snapshotTasks_1872_ = v_snapshotTasks_1987_;
v___y_1873_ = v___y_1959_;
v___y_1874_ = v___y_1961_;
v___y_1875_ = v___y_1962_;
v___y_1876_ = v___y_1963_;
v___y_1877_ = v___y_1964_;
v___y_1878_ = v___y_1965_;
v___y_1879_ = v___y_1966_;
v___y_1880_ = v___y_1968_;
v___y_1881_ = v___y_1969_;
v___y_1882_ = v___y_1970_;
v___y_1883_ = v___y_1971_;
v___y_1884_ = v___f_1979_;
v___y_1885_ = v___y_1973_;
v_reportedCmdState_1886_ = v___x_2004_;
goto v___jp_1857_;
}
}
else
{
lean_dec(v___y_1960_);
lean_inc_ref(v___x_1976_);
v___y_1921_ = v___y_1951_;
v___y_1922_ = v___y_1952_;
v___y_1923_ = v___y_1953_;
v___y_1924_ = v___y_1954_;
v___y_1925_ = v___y_1956_;
v___y_1926_ = v___y_1955_;
v___y_1927_ = v___y_1957_;
v___y_1928_ = v___y_1958_;
v___y_1929_ = v___x_1976_;
v___y_1930_ = v___y_1959_;
v___y_1931_ = v___y_1961_;
v___y_1932_ = v___y_1962_;
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1966_;
v___y_1937_ = v___y_1968_;
v___y_1938_ = v___y_1969_;
v___y_1939_ = v___y_1970_;
v___y_1940_ = v___y_1971_;
v___y_1941_ = v___f_1979_;
v___y_1942_ = v___y_1973_;
v_reportedCmdState_1943_ = v___x_1976_;
goto v___jp_1920_;
}
}
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2007_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1808_);
v___x_2008_ = l_IO_CancelToken_new();
v___x_2009_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1809_);
v___x_2010_ = l_Lean_Name_str___override(v___x_1809_, v___x_2009_);
v___x_2011_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2012_ = l_Lean_Name_str___override(v___x_2010_, v___x_2011_);
v___x_2013_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2014_ = l_Lean_Name_str___override(v___x_2012_, v___x_2013_);
v___x_2015_ = l_Lean_Name_str___override(v___x_2014_, v___x_2011_);
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = l_Lean_Name_num___override(v___x_2015_, v___x_2016_);
v___x_2018_ = l_Lean_Name_str___override(v___x_2017_, v___x_2011_);
v___x_2019_ = l_Lean_Name_str___override(v___x_2018_, v___x_2013_);
v___x_2020_ = l_Lean_Name_str___override(v___x_2019_, v___x_2011_);
v___x_2021_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2022_ = l_Lean_Name_str___override(v___x_2020_, v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2024_ = l_Lean_Name_str___override(v___x_2022_, v___x_2023_);
v___x_2025_ = l_Lean_Name_toString(v___x_2024_, v___x_1810_);
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_unsigned_to_nat(32u);
v___x_2028_ = ((size_t)5ULL);
v___x_2029_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2025_, 2);
v___x_2030_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2030_, 0, v___x_2025_);
lean_ctor_set(v___x_2030_, 1, v___x_2007_);
lean_ctor_set(v___x_2030_, 2, v___x_2026_);
lean_ctor_set(v___x_2030_, 3, v___x_2029_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*4, v_val_1806_);
v___x_2031_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2032_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2032_, 0, v___x_2025_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
lean_ctor_set(v___x_2032_, 2, v___x_2026_);
lean_ctor_set(v___x_2032_, 3, v___x_2029_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*4, v_val_1806_);
lean_inc(v_fst_1811_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_fst_1811_);
v___x_2034_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2033_);
lean_inc(v___x_2008_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2008_);
v___x_2036_ = l_IO_Promise_result_x21___redArg(v_val_1812_);
lean_inc_ref(v___x_2036_);
lean_inc(v___x_2034_);
lean_inc_ref_n(v___x_2033_, 3);
v___x_2037_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2033_);
lean_ctor_set(v___x_2037_, 1, v___x_2034_);
lean_ctor_set(v___x_2037_, 2, v___x_2035_);
lean_ctor_set(v___x_2037_, 3, v___x_2036_);
v___x_2038_ = l_IO_Promise_result_x21___redArg(v_val_1813_);
lean_inc_ref(v___x_2038_);
lean_inc_n(v___x_1803_, 3);
v___x_2039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2033_);
lean_ctor_set(v___x_2039_, 1, v___x_1803_);
lean_ctor_set(v___x_2039_, 2, v___x_2026_);
lean_ctor_set(v___x_2039_, 3, v___x_2038_);
v___x_2040_ = l_IO_Promise_result_x21___redArg(v_val_1814_);
lean_inc_ref(v___x_2040_);
v___x_2041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2033_);
lean_ctor_set(v___x_2041_, 1, v___x_1803_);
lean_ctor_set(v___x_2041_, 2, v___x_2026_);
lean_ctor_set(v___x_2041_, 3, v___x_2040_);
v___x_2042_ = l_IO_Promise_result_x21___redArg(v_val_1804_);
v___x_2043_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2026_);
lean_ctor_set(v___x_2043_, 1, v___x_1803_);
lean_ctor_set(v___x_2043_, 2, v___x_2026_);
lean_ctor_set(v___x_2043_, 3, v___x_2042_);
lean_inc_ref(v___x_2032_);
v___x_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2032_);
lean_ctor_set(v___x_2044_, 1, v___x_2037_);
lean_ctor_set(v___x_2044_, 2, v___x_2039_);
lean_ctor_set(v___x_2044_, 3, v___x_2041_);
lean_ctor_set(v___x_2044_, 4, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2030_);
lean_ctor_set(v___x_2045_, 1, v_fst_1811_);
lean_ctor_set(v___x_2045_, 2, v_snd_1815_);
lean_ctor_set(v___x_2045_, 3, v___x_2044_);
lean_ctor_set(v___x_2045_, 4, v___y_2006_);
v___x_2046_ = lean_io_promise_resolve(v___x_2045_, v_prom_1816_);
if (lean_obj_tag(v_old_x3f_1826_) == 0)
{
lean_inc_ref(v___x_2032_);
lean_inc_ref(v___x_2025_);
v___y_1951_ = v___x_2026_;
v___y_1952_ = v___x_2029_;
v___y_1953_ = v___x_2025_;
v___y_1954_ = v___x_2027_;
v___y_1955_ = v___x_2032_;
v___y_1956_ = v___x_2016_;
v___y_1957_ = v___x_2026_;
v___y_1958_ = v___x_2028_;
v___y_1959_ = v___x_2026_;
v___y_1960_ = v___x_2027_;
v___y_1961_ = v___x_2016_;
v___y_1962_ = v___x_2032_;
v___y_1963_ = v___x_2038_;
v___y_1964_ = v___x_2034_;
v___y_1965_ = v___x_2026_;
v___y_1966_ = v___x_2026_;
v___y_1967_ = v___x_2029_;
v___y_1968_ = v___x_2025_;
v___y_1969_ = v___x_2008_;
v___y_1970_ = v___x_2033_;
v___y_1971_ = v___x_2040_;
v___y_1972_ = v___x_2028_;
v___y_1973_ = v___x_2036_;
v___y_1974_ = v___x_2026_;
goto v___jp_1950_;
}
else
{
lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2058_; 
v_val_2047_ = lean_ctor_get(v_old_x3f_1826_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_old_x3f_1826_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2049_ = v_old_x3f_1826_;
v_isShared_2050_ = v_isSharedCheck_2058_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_dec(v_old_x3f_1826_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2058_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_elabSnap_2051_; lean_object* v_stx_2052_; lean_object* v_elabSnap_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v_elabSnap_2051_ = lean_ctor_get(v_val_2047_, 3);
lean_inc_ref(v_elabSnap_2051_);
v_stx_2052_ = lean_ctor_get(v_val_2047_, 1);
lean_inc(v_stx_2052_);
lean_dec(v_val_2047_);
v_elabSnap_2053_ = lean_ctor_get(v_elabSnap_2051_, 1);
lean_inc_ref(v_elabSnap_2053_);
lean_dec_ref(v_elabSnap_2051_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_stx_2052_);
lean_ctor_set(v___x_2054_, 1, v_elabSnap_2053_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_inc_ref(v___x_2032_);
lean_inc_ref(v___x_2025_);
v___y_1951_ = v___x_2026_;
v___y_1952_ = v___x_2029_;
v___y_1953_ = v___x_2025_;
v___y_1954_ = v___x_2027_;
v___y_1955_ = v___x_2032_;
v___y_1956_ = v___x_2016_;
v___y_1957_ = v___x_2026_;
v___y_1958_ = v___x_2028_;
v___y_1959_ = v___x_2026_;
v___y_1960_ = v___x_2027_;
v___y_1961_ = v___x_2016_;
v___y_1962_ = v___x_2032_;
v___y_1963_ = v___x_2038_;
v___y_1964_ = v___x_2034_;
v___y_1965_ = v___x_2026_;
v___y_1966_ = v___x_2026_;
v___y_1967_ = v___x_2029_;
v___y_1968_ = v___x_2025_;
v___y_1969_ = v___x_2008_;
v___y_1970_ = v___x_2033_;
v___y_1971_ = v___x_2040_;
v___y_1972_ = v___x_2028_;
v___y_1973_ = v___x_2036_;
v___y_1974_ = v___x_2056_;
goto v___jp_1950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_fst_2071_, uint8_t v_val_2072_, lean_object* v_a_2073_, lean_object* v_snd_2074_, lean_object* v___x_2075_, uint8_t v___x_2076_, lean_object* v_prom_2077_, lean_object* v___x_2078_, lean_object* v___f_2079_, lean_object* v___f_2080_, lean_object* v___f_2081_, lean_object* v_pos_2082_, lean_object* v_fst_2083_, lean_object* v_cmdState_2084_, lean_object* v_opts_2085_, lean_object* v_old_x3f_2086_, lean_object* v_parseCancelTk_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v_snapshotTasks_2101_; lean_object* v_traceTask_2102_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; size_t v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v_env_2146_; lean_object* v_messages_2147_; lean_object* v_scopes_2148_; lean_object* v_infoState_2149_; lean_object* v_traceState_2150_; lean_object* v_snapshotTasks_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v_reportedCmdState_2155_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; size_t v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v_reportedCmdState_2214_; lean_object* v___x_2221_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; size_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; size_t v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v_fst_2358_; lean_object* v_snd_2359_; uint8_t v___y_2372_; uint8_t v___x_2375_; 
v___x_2089_ = lean_io_promise_new();
v___x_2090_ = lean_io_promise_new();
v___x_2091_ = lean_io_promise_new();
v___x_2092_ = lean_io_promise_new();
v___x_2221_ = l_Lean_internal_cmdlineSnapshots;
v___x_2375_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2085_, v___x_2221_);
if (v___x_2375_ == 0)
{
v___y_2372_ = v___x_2375_;
goto v___jp_2371_;
}
else
{
uint8_t v___x_2376_; 
lean_inc(v_fst_2083_);
v___x_2376_ = l_Lean_Parser_isTerminalCommand(v_fst_2083_);
if (v___x_2376_ == 0)
{
v___y_2372_ = v___x_2375_;
goto v___jp_2371_;
}
else
{
lean_inc_ref(v_fst_2071_);
lean_inc(v_fst_2083_);
v_fst_2358_ = v_fst_2083_;
v_snd_2359_ = v_fst_2071_;
goto v___jp_2357_;
}
}
v___jp_2093_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2103_, 0, v___y_2095_);
lean_ctor_set(v___x_2103_, 1, v___y_2099_);
lean_ctor_set(v___x_2103_, 2, v___y_2098_);
lean_ctor_set(v___x_2103_, 3, v_traceTask_2102_);
v___x_2104_ = lean_array_push(v_snapshotTasks_2101_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___y_2096_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_io_promise_resolve(v___x_2105_, v___x_2092_);
lean_dec(v___x_2092_);
if (lean_obj_tag(v___y_2097_) == 1)
{
lean_object* v_val_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_val_2107_ = lean_ctor_get(v___y_2097_, 0);
lean_inc(v_val_2107_);
lean_dec_ref(v___y_2097_);
v___x_2108_ = lean_box(0);
v___x_2109_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2108_, v_fst_2071_, v___y_2100_, v_val_2107_, v_val_2072_, v___y_2094_, v_a_2073_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; 
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2097_);
lean_dec(v___y_2094_);
lean_dec_ref(v_fst_2071_);
v___x_2110_ = lean_box(0);
return v___x_2110_;
}
}
v___jp_2111_:
{
lean_object* v_snapshotTasks_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_snapshotTasks_2120_ = lean_ctor_get(v___y_2117_, 10);
lean_inc_ref(v_snapshotTasks_2120_);
v___x_2121_ = lean_mk_empty_array_with_capacity(v___y_2119_);
lean_dec(v___y_2119_);
lean_inc_ref(v___y_2114_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2114_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_task_pure(v___x_2122_);
v___y_2094_ = v___y_2112_;
v___y_2095_ = v___y_2113_;
v___y_2096_ = v___y_2114_;
v___y_2097_ = v___y_2115_;
v___y_2098_ = v___y_2116_;
v___y_2099_ = v___y_2118_;
v___y_2100_ = v___y_2117_;
v_snapshotTasks_2101_ = v_snapshotTasks_2120_;
v_traceTask_2102_ = v___x_2123_;
goto v___jp_2093_;
}
v___jp_2124_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_opts_2165_; uint8_t v_hasTrace_2166_; 
v___x_2156_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2147_);
v___x_2157_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2157_, 0, v___y_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
lean_ctor_set(v___x_2157_, 2, v___y_2140_);
lean_ctor_set(v___x_2157_, 3, v_traceState_2150_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*4, v_val_2072_);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v_reportedCmdState_2155_);
v___x_2159_ = lean_io_promise_resolve(v___x_2158_, v___x_2090_);
lean_dec(v___x_2090_);
v___x_2160_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2149_);
lean_inc(v___y_2142_);
v___x_2161_ = l_BaseIO_chainTask___redArg(v___x_2160_, v___y_2144_, v___y_2142_, v___x_2076_);
v___x_2162_ = l_Lean_inheritedTraceOptions;
v___x_2163_ = lean_st_ref_get(v___x_2162_);
v___x_2164_ = l_List_head_x21___redArg(v___x_2078_, v_scopes_2148_);
lean_dec(v_scopes_2148_);
lean_dec_ref(v___x_2078_);
v_opts_2165_ = lean_ctor_get(v___x_2164_, 1);
lean_inc_ref(v_opts_2165_);
lean_dec(v___x_2164_);
v_hasTrace_2166_ = lean_ctor_get_uint8(v_opts_2165_, sizeof(void*)*1);
if (v_hasTrace_2166_ == 0)
{
lean_dec_ref(v_opts_2165_);
lean_dec(v___x_2163_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_snapshotTasks_2151_);
lean_dec_ref(v_env_2146_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec(v_pos_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v___f_2079_);
lean_dec(v___x_2075_);
v___y_2112_ = v___y_2134_;
v___y_2113_ = v___y_2136_;
v___y_2114_ = v___y_2143_;
v___y_2115_ = v___y_2138_;
v___y_2116_ = v___y_2139_;
v___y_2117_ = v___y_2145_;
v___y_2118_ = v___y_2152_;
v___y_2119_ = v___y_2142_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2163_, v_opts_2165_, v___x_2167_);
lean_dec(v___x_2163_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v_opts_2165_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_snapshotTasks_2151_);
lean_dec_ref(v_env_2146_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec(v_pos_2082_);
lean_dec_ref(v___f_2081_);
lean_dec_ref(v___f_2080_);
lean_dec_ref(v___f_2079_);
lean_dec(v___x_2075_);
v___y_2112_ = v___y_2134_;
v___y_2113_ = v___y_2136_;
v___y_2114_ = v___y_2143_;
v___y_2115_ = v___y_2138_;
v___y_2116_ = v___y_2139_;
v___y_2117_ = v___y_2145_;
v___y_2118_ = v___y_2152_;
v___y_2119_ = v___y_2142_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; 
lean_inc_n(v___y_2142_, 3);
v___x_2169_ = lean_task_map(v___f_2079_, v___y_2133_, v___y_2142_, v___x_2076_);
lean_inc_n(v___y_2139_, 3);
lean_inc_n(v___y_2141_, 2);
lean_inc_n(v___y_2135_, 2);
v___x_2170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2170_, 0, v___y_2135_);
lean_ctor_set(v___x_2170_, 1, v___y_2141_);
lean_ctor_set(v___x_2170_, 2, v___y_2139_);
lean_ctor_set(v___x_2170_, 3, v___x_2169_);
v___x_2171_ = lean_task_map(v___f_2080_, v___y_2153_, v___y_2142_, v___x_2076_);
v___x_2172_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2172_, 0, v___y_2135_);
lean_ctor_set(v___x_2172_, 1, v___y_2141_);
lean_ctor_set(v___x_2172_, 2, v___y_2139_);
lean_ctor_set(v___x_2172_, 3, v___x_2171_);
v___x_2173_ = lean_task_map(v___f_2081_, v___y_2137_, v___y_2142_, v___x_2076_);
v___x_2174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2174_, 0, v___y_2135_);
lean_ctor_set(v___x_2174_, 1, v___y_2141_);
lean_ctor_set(v___x_2174_, 2, v___y_2139_);
lean_ctor_set(v___x_2174_, 3, v___x_2173_);
v___x_2175_ = lean_unsigned_to_nat(3u);
v___x_2176_ = lean_mk_empty_array_with_capacity(v___x_2175_);
v___x_2177_ = lean_array_push(v___x_2176_, v___x_2170_);
v___x_2178_ = lean_array_push(v___x_2177_, v___x_2172_);
v___x_2179_ = lean_array_push(v___x_2178_, v___x_2174_);
v___x_2180_ = l_Array_append___redArg(v___x_2179_, v_snapshotTasks_2151_);
lean_inc_ref(v___y_2143_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2143_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
lean_inc_ref(v___x_2181_);
v___x_2182_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2181_);
v___x_2183_ = lean_box_usize(v___y_2130_);
v___x_2184_ = lean_box(v___x_2076_);
v___x_2185_ = lean_box(v_val_2072_);
v___x_2186_ = lean_box(v___x_2168_);
lean_inc_ref(v_a_2073_);
lean_inc_ref(v___y_2129_);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2187_, 0, v___x_2075_);
lean_closure_set(v___f_2187_, 1, v___y_2132_);
lean_closure_set(v___f_2187_, 2, v___y_2125_);
lean_closure_set(v___f_2187_, 3, v___x_2183_);
lean_closure_set(v___f_2187_, 4, v___x_2184_);
lean_closure_set(v___f_2187_, 5, v_env_2146_);
lean_closure_set(v___f_2187_, 6, v___y_2129_);
lean_closure_set(v___f_2187_, 7, v___x_2162_);
lean_closure_set(v___f_2187_, 8, v_a_2073_);
lean_closure_set(v___f_2187_, 9, v_opts_2165_);
lean_closure_set(v___f_2187_, 10, v___x_2181_);
lean_closure_set(v___f_2187_, 11, v_pos_2082_);
lean_closure_set(v___f_2187_, 12, v___x_2185_);
lean_closure_set(v___f_2187_, 13, v___y_2131_);
lean_closure_set(v___f_2187_, 14, v___y_2128_);
lean_closure_set(v___f_2187_, 15, v___y_2126_);
lean_closure_set(v___f_2187_, 16, v___y_2127_);
lean_closure_set(v___f_2187_, 17, v___x_2186_);
v___x_2188_ = lean_io_bind_task(v___x_2182_, v___f_2187_, v___y_2142_, v_val_2072_);
v___y_2094_ = v___y_2134_;
v___y_2095_ = v___y_2136_;
v___y_2096_ = v___y_2143_;
v___y_2097_ = v___y_2138_;
v___y_2098_ = v___y_2139_;
v___y_2099_ = v___y_2152_;
v___y_2100_ = v___y_2145_;
v_snapshotTasks_2101_ = v_snapshotTasks_2151_;
v_traceTask_2102_ = v___x_2188_;
goto v___jp_2093_;
}
}
}
v___jp_2189_:
{
lean_object* v_env_2215_; lean_object* v_messages_2216_; lean_object* v_scopes_2217_; lean_object* v_infoState_2218_; lean_object* v_traceState_2219_; lean_object* v_snapshotTasks_2220_; 
v_env_2215_ = lean_ctor_get(v___y_2210_, 0);
lean_inc_ref(v_env_2215_);
v_messages_2216_ = lean_ctor_get(v___y_2210_, 1);
lean_inc_ref(v_messages_2216_);
v_scopes_2217_ = lean_ctor_get(v___y_2210_, 2);
lean_inc(v_scopes_2217_);
v_infoState_2218_ = lean_ctor_get(v___y_2210_, 8);
lean_inc_ref(v_infoState_2218_);
v_traceState_2219_ = lean_ctor_get(v___y_2210_, 9);
lean_inc_ref(v_traceState_2219_);
v_snapshotTasks_2220_ = lean_ctor_get(v___y_2210_, 10);
lean_inc_ref(v_snapshotTasks_2220_);
v___y_2125_ = v___y_2190_;
v___y_2126_ = v___y_2191_;
v___y_2127_ = v___y_2192_;
v___y_2128_ = v___y_2193_;
v___y_2129_ = v___y_2194_;
v___y_2130_ = v___y_2195_;
v___y_2131_ = v___y_2197_;
v___y_2132_ = v___y_2196_;
v___y_2133_ = v___y_2198_;
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
v___y_2144_ = v___y_2209_;
v___y_2145_ = v___y_2210_;
v_env_2146_ = v_env_2215_;
v_messages_2147_ = v_messages_2216_;
v_scopes_2148_ = v_scopes_2217_;
v_infoState_2149_ = v_infoState_2218_;
v_traceState_2150_ = v_traceState_2219_;
v_snapshotTasks_2151_ = v_snapshotTasks_2220_;
v___y_2152_ = v___y_2211_;
v___y_2153_ = v___y_2212_;
v___y_2154_ = v___y_2213_;
v_reportedCmdState_2155_ = v_reportedCmdState_2214_;
goto v___jp_2124_;
}
v___jp_2222_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___f_2253_; uint8_t v___x_2254_; 
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___y_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2089_);
lean_inc(v___y_2233_);
lean_inc_n(v_pos_2082_, 2);
lean_inc(v_fst_2083_);
v___x_2250_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2083_, v_cmdState_2084_, v_pos_2082_, v___x_2249_, v___y_2233_, v_a_2073_);
v___x_2251_ = lean_box(v_val_2072_);
v___x_2252_ = lean_box(v___x_2076_);
lean_inc_ref(v_a_2073_);
lean_inc(v___y_2223_);
lean_inc_ref(v___x_2078_);
lean_inc_ref(v___x_2250_);
lean_inc_ref(v___y_2227_);
lean_inc_ref(v___y_2230_);
v___f_2253_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2253_, 0, v___y_2230_);
lean_closure_set(v___f_2253_, 1, v___y_2227_);
lean_closure_set(v___f_2253_, 2, v___x_2251_);
lean_closure_set(v___f_2253_, 3, v___x_2091_);
lean_closure_set(v___f_2253_, 4, v___x_2250_);
lean_closure_set(v___f_2253_, 5, v___x_2078_);
lean_closure_set(v___f_2253_, 6, v___y_2223_);
lean_closure_set(v___f_2253_, 7, v___x_2252_);
lean_closure_set(v___f_2253_, 8, v_a_2073_);
lean_closure_set(v___f_2253_, 9, v_pos_2082_);
v___x_2254_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2085_, v___x_2221_);
if (v___x_2254_ == 0)
{
lean_dec(v___y_2232_);
lean_dec(v_fst_2083_);
lean_inc_ref(v___x_2250_);
v___y_2190_ = v___y_2223_;
v___y_2191_ = v___y_2224_;
v___y_2192_ = v___y_2225_;
v___y_2193_ = v___y_2226_;
v___y_2194_ = v___y_2227_;
v___y_2195_ = v___y_2228_;
v___y_2196_ = v___y_2229_;
v___y_2197_ = v___y_2230_;
v___y_2198_ = v___y_2231_;
v___y_2199_ = v___y_2233_;
v___y_2200_ = v___y_2234_;
v___y_2201_ = v___y_2235_;
v___y_2202_ = v___y_2236_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2238_;
v___y_2205_ = v___y_2240_;
v___y_2206_ = v___y_2241_;
v___y_2207_ = v___y_2242_;
v___y_2208_ = v___y_2243_;
v___y_2209_ = v___f_2253_;
v___y_2210_ = v___x_2250_;
v___y_2211_ = v___y_2244_;
v___y_2212_ = v___y_2245_;
v___y_2213_ = v___y_2247_;
v_reportedCmdState_2214_ = v___x_2250_;
goto v___jp_2189_;
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = l_Lean_Parser_isTerminalCommand(v_fst_2083_);
if (v___x_2255_ == 0)
{
if (v___x_2254_ == 0)
{
lean_dec(v___y_2232_);
lean_inc_ref(v___x_2250_);
v___y_2190_ = v___y_2223_;
v___y_2191_ = v___y_2224_;
v___y_2192_ = v___y_2225_;
v___y_2193_ = v___y_2226_;
v___y_2194_ = v___y_2227_;
v___y_2195_ = v___y_2228_;
v___y_2196_ = v___y_2229_;
v___y_2197_ = v___y_2230_;
v___y_2198_ = v___y_2231_;
v___y_2199_ = v___y_2233_;
v___y_2200_ = v___y_2234_;
v___y_2201_ = v___y_2235_;
v___y_2202_ = v___y_2236_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2238_;
v___y_2205_ = v___y_2240_;
v___y_2206_ = v___y_2241_;
v___y_2207_ = v___y_2242_;
v___y_2208_ = v___y_2243_;
v___y_2209_ = v___f_2253_;
v___y_2210_ = v___x_2250_;
v___y_2211_ = v___y_2244_;
v___y_2212_ = v___y_2245_;
v___y_2213_ = v___y_2247_;
v_reportedCmdState_2214_ = v___x_2250_;
goto v___jp_2189_;
}
else
{
lean_object* v_env_2256_; lean_object* v_messages_2257_; lean_object* v_scopes_2258_; lean_object* v_infoState_2259_; lean_object* v_traceState_2260_; lean_object* v_snapshotTasks_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_env_2256_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref_n(v_env_2256_, 2);
v_messages_2257_ = lean_ctor_get(v___x_2250_, 1);
lean_inc_ref(v_messages_2257_);
v_scopes_2258_ = lean_ctor_get(v___x_2250_, 2);
lean_inc(v_scopes_2258_);
v_infoState_2259_ = lean_ctor_get(v___x_2250_, 8);
lean_inc_ref(v_infoState_2259_);
v_traceState_2260_ = lean_ctor_get(v___x_2250_, 9);
lean_inc_ref(v_traceState_2260_);
v_snapshotTasks_2261_ = lean_ctor_get(v___x_2250_, 10);
lean_inc_ref(v_snapshotTasks_2261_);
v___x_2262_ = lean_mk_empty_array_with_capacity(v___y_2232_);
lean_dec(v___y_2232_);
lean_inc_ref(v___x_2262_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_inc_n(v___y_2242_, 3);
v___x_2264_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2262_);
lean_ctor_set(v___x_2264_, 2, v___y_2242_);
lean_ctor_set(v___x_2264_, 3, v___y_2242_);
lean_ctor_set_usize(v___x_2264_, 4, v___y_2239_);
v___x_2265_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2264_, 2);
v___x_2266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2264_);
lean_ctor_set(v___x_2266_, 2, v___x_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2268_ = l_Lean_Options_empty;
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_mk_empty_array_with_capacity(v___y_2242_);
lean_inc_ref_n(v___x_2270_, 2);
lean_inc_n(v___x_2075_, 2);
v___x_2271_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2271_, 0, v___x_2267_);
lean_ctor_set(v___x_2271_, 1, v___x_2268_);
lean_ctor_set(v___x_2271_, 2, v___x_2075_);
lean_ctor_set(v___x_2271_, 3, v___x_2269_);
lean_ctor_set(v___x_2271_, 4, v___x_2269_);
lean_ctor_set(v___x_2271_, 5, v___x_2270_);
lean_ctor_set(v___x_2271_, 6, v___x_2270_);
lean_ctor_set(v___x_2271_, 7, v___x_2269_);
lean_ctor_set(v___x_2271_, 8, v___x_2269_);
lean_ctor_set(v___x_2271_, 9, v___x_2269_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*10, v_val_2072_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*10 + 1, v_val_2072_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*10 + 2, v_val_2072_);
v___x_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2269_);
v___x_2273_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2274_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2275_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2075_);
v___x_2276_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2277_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
lean_ctor_set(v___x_2277_, 2, v___x_2264_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3, v___x_2076_);
lean_inc_ref(v___y_2246_);
v___x_2278_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2278_, 0, v_env_2256_);
lean_ctor_set(v___x_2278_, 1, v___x_2266_);
lean_ctor_set(v___x_2278_, 2, v___x_2272_);
lean_ctor_set(v___x_2278_, 3, v___x_2265_);
lean_ctor_set(v___x_2278_, 4, v___x_2273_);
lean_ctor_set(v___x_2278_, 5, v___y_2242_);
lean_ctor_set(v___x_2278_, 6, v___x_2274_);
lean_ctor_set(v___x_2278_, 7, v___x_2275_);
lean_ctor_set(v___x_2278_, 8, v___x_2277_);
lean_ctor_set(v___x_2278_, 9, v___y_2246_);
lean_ctor_set(v___x_2278_, 10, v___x_2270_);
v___y_2125_ = v___y_2223_;
v___y_2126_ = v___y_2224_;
v___y_2127_ = v___y_2225_;
v___y_2128_ = v___y_2226_;
v___y_2129_ = v___y_2227_;
v___y_2130_ = v___y_2228_;
v___y_2131_ = v___y_2230_;
v___y_2132_ = v___y_2229_;
v___y_2133_ = v___y_2231_;
v___y_2134_ = v___y_2233_;
v___y_2135_ = v___y_2234_;
v___y_2136_ = v___y_2235_;
v___y_2137_ = v___y_2236_;
v___y_2138_ = v___y_2237_;
v___y_2139_ = v___y_2238_;
v___y_2140_ = v___y_2240_;
v___y_2141_ = v___y_2241_;
v___y_2142_ = v___y_2242_;
v___y_2143_ = v___y_2243_;
v___y_2144_ = v___f_2253_;
v___y_2145_ = v___x_2250_;
v_env_2146_ = v_env_2256_;
v_messages_2147_ = v_messages_2257_;
v_scopes_2148_ = v_scopes_2258_;
v_infoState_2149_ = v_infoState_2259_;
v_traceState_2150_ = v_traceState_2260_;
v_snapshotTasks_2151_ = v_snapshotTasks_2261_;
v___y_2152_ = v___y_2244_;
v___y_2153_ = v___y_2245_;
v___y_2154_ = v___y_2247_;
v_reportedCmdState_2155_ = v___x_2278_;
goto v___jp_2124_;
}
}
else
{
lean_dec(v___y_2232_);
lean_inc_ref(v___x_2250_);
v___y_2190_ = v___y_2223_;
v___y_2191_ = v___y_2224_;
v___y_2192_ = v___y_2225_;
v___y_2193_ = v___y_2226_;
v___y_2194_ = v___y_2227_;
v___y_2195_ = v___y_2228_;
v___y_2196_ = v___y_2229_;
v___y_2197_ = v___y_2230_;
v___y_2198_ = v___y_2231_;
v___y_2199_ = v___y_2233_;
v___y_2200_ = v___y_2234_;
v___y_2201_ = v___y_2235_;
v___y_2202_ = v___y_2236_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2238_;
v___y_2205_ = v___y_2240_;
v___y_2206_ = v___y_2241_;
v___y_2207_ = v___y_2242_;
v___y_2208_ = v___y_2243_;
v___y_2209_ = v___f_2253_;
v___y_2210_ = v___x_2250_;
v___y_2211_ = v___y_2244_;
v___y_2212_ = v___y_2245_;
v___y_2213_ = v___y_2247_;
v_reportedCmdState_2214_ = v___x_2250_;
goto v___jp_2189_;
}
}
}
v___jp_2279_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2285_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2074_);
v___x_2286_ = l_IO_CancelToken_new();
v___x_2287_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2075_);
v___x_2288_ = l_Lean_Name_str___override(v___x_2075_, v___x_2287_);
v___x_2289_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2290_ = l_Lean_Name_str___override(v___x_2288_, v___x_2289_);
v___x_2291_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2292_ = l_Lean_Name_str___override(v___x_2290_, v___x_2291_);
v___x_2293_ = l_Lean_Name_str___override(v___x_2292_, v___x_2289_);
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = l_Lean_Name_num___override(v___x_2293_, v___x_2294_);
v___x_2296_ = l_Lean_Name_str___override(v___x_2295_, v___x_2289_);
v___x_2297_ = l_Lean_Name_str___override(v___x_2296_, v___x_2291_);
v___x_2298_ = l_Lean_Name_str___override(v___x_2297_, v___x_2289_);
v___x_2299_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2300_ = l_Lean_Name_str___override(v___x_2298_, v___x_2299_);
v___x_2301_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2302_ = l_Lean_Name_str___override(v___x_2300_, v___x_2301_);
v___x_2303_ = l_Lean_Name_toString(v___x_2302_, v___x_2076_);
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_unsigned_to_nat(32u);
v___x_2306_ = lean_mk_empty_array_with_capacity(v___x_2305_);
lean_dec_ref(v___x_2306_);
v___x_2307_ = ((size_t)5ULL);
v___x_2308_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2303_, 2);
v___x_2309_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2309_, 0, v___x_2303_);
lean_ctor_set(v___x_2309_, 1, v___x_2285_);
lean_ctor_set(v___x_2309_, 2, v___x_2304_);
lean_ctor_set(v___x_2309_, 3, v___x_2308_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*4, v_val_2072_);
v___x_2310_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2311_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2311_, 0, v___x_2303_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
lean_ctor_set(v___x_2311_, 2, v___x_2304_);
lean_ctor_set(v___x_2311_, 3, v___x_2308_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*4, v_val_2072_);
lean_inc(v___y_2280_);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___y_2280_);
v___x_2313_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2312_);
lean_inc(v___x_2286_);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2286_);
v___x_2315_ = l_IO_Promise_result_x21___redArg(v___x_2089_);
lean_inc_ref(v___x_2315_);
lean_inc(v___x_2313_);
lean_inc_ref_n(v___x_2312_, 3);
v___x_2316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2312_);
lean_ctor_set(v___x_2316_, 1, v___x_2313_);
lean_ctor_set(v___x_2316_, 2, v___x_2314_);
lean_ctor_set(v___x_2316_, 3, v___x_2315_);
v___x_2317_ = l_IO_Promise_result_x21___redArg(v___x_2090_);
lean_inc_ref(v___x_2317_);
lean_inc_n(v___y_2282_, 3);
v___x_2318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2312_);
lean_ctor_set(v___x_2318_, 1, v___y_2282_);
lean_ctor_set(v___x_2318_, 2, v___x_2304_);
lean_ctor_set(v___x_2318_, 3, v___x_2317_);
v___x_2319_ = l_IO_Promise_result_x21___redArg(v___x_2091_);
lean_inc_ref(v___x_2319_);
v___x_2320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2312_);
lean_ctor_set(v___x_2320_, 1, v___y_2282_);
lean_ctor_set(v___x_2320_, 2, v___x_2304_);
lean_ctor_set(v___x_2320_, 3, v___x_2319_);
v___x_2321_ = l_IO_Promise_result_x21___redArg(v___x_2092_);
v___x_2322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2304_);
lean_ctor_set(v___x_2322_, 1, v___y_2282_);
lean_ctor_set(v___x_2322_, 2, v___x_2304_);
lean_ctor_set(v___x_2322_, 3, v___x_2321_);
lean_inc_ref(v___x_2311_);
v___x_2323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2311_);
lean_ctor_set(v___x_2323_, 1, v___x_2316_);
lean_ctor_set(v___x_2323_, 2, v___x_2318_);
lean_ctor_set(v___x_2323_, 3, v___x_2320_);
lean_ctor_set(v___x_2323_, 4, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2309_);
lean_ctor_set(v___x_2324_, 1, v___y_2280_);
lean_ctor_set(v___x_2324_, 2, v___y_2283_);
lean_ctor_set(v___x_2324_, 3, v___x_2323_);
lean_ctor_set(v___x_2324_, 4, v___y_2284_);
v___x_2325_ = lean_io_promise_resolve(v___x_2324_, v_prom_2077_);
if (lean_obj_tag(v_old_x3f_2086_) == 0)
{
lean_inc_ref(v___x_2303_);
lean_inc_ref(v___x_2311_);
v___y_2223_ = v___x_2294_;
v___y_2224_ = v___x_2311_;
v___y_2225_ = v___x_2304_;
v___y_2226_ = v___x_2304_;
v___y_2227_ = v___x_2308_;
v___y_2228_ = v___x_2307_;
v___y_2229_ = v___x_2305_;
v___y_2230_ = v___x_2303_;
v___y_2231_ = v___x_2315_;
v___y_2232_ = v___x_2305_;
v___y_2233_ = v___x_2286_;
v___y_2234_ = v___x_2312_;
v___y_2235_ = v___x_2304_;
v___y_2236_ = v___x_2319_;
v___y_2237_ = v___y_2281_;
v___y_2238_ = v___x_2304_;
v___y_2239_ = v___x_2307_;
v___y_2240_ = v___x_2304_;
v___y_2241_ = v___x_2313_;
v___y_2242_ = v___x_2294_;
v___y_2243_ = v___x_2311_;
v___y_2244_ = v___y_2282_;
v___y_2245_ = v___x_2317_;
v___y_2246_ = v___x_2308_;
v___y_2247_ = v___x_2303_;
v___y_2248_ = v___x_2304_;
goto v___jp_2222_;
}
else
{
lean_object* v_val_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2337_; 
v_val_2326_ = lean_ctor_get(v_old_x3f_2086_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_old_x3f_2086_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2328_ = v_old_x3f_2086_;
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_val_2326_);
lean_dec(v_old_x3f_2086_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_elabSnap_2330_; lean_object* v_stx_2331_; lean_object* v_elabSnap_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v_elabSnap_2330_ = lean_ctor_get(v_val_2326_, 3);
lean_inc_ref(v_elabSnap_2330_);
v_stx_2331_ = lean_ctor_get(v_val_2326_, 1);
lean_inc(v_stx_2331_);
lean_dec(v_val_2326_);
v_elabSnap_2332_ = lean_ctor_get(v_elabSnap_2330_, 1);
lean_inc_ref(v_elabSnap_2332_);
lean_dec_ref(v_elabSnap_2330_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_stx_2331_);
lean_ctor_set(v___x_2333_, 1, v_elabSnap_2332_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2333_);
v___x_2335_ = v___x_2328_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_inc_ref(v___x_2303_);
lean_inc_ref(v___x_2311_);
v___y_2223_ = v___x_2294_;
v___y_2224_ = v___x_2311_;
v___y_2225_ = v___x_2304_;
v___y_2226_ = v___x_2304_;
v___y_2227_ = v___x_2308_;
v___y_2228_ = v___x_2307_;
v___y_2229_ = v___x_2305_;
v___y_2230_ = v___x_2303_;
v___y_2231_ = v___x_2315_;
v___y_2232_ = v___x_2305_;
v___y_2233_ = v___x_2286_;
v___y_2234_ = v___x_2312_;
v___y_2235_ = v___x_2304_;
v___y_2236_ = v___x_2319_;
v___y_2237_ = v___y_2281_;
v___y_2238_ = v___x_2304_;
v___y_2239_ = v___x_2307_;
v___y_2240_ = v___x_2304_;
v___y_2241_ = v___x_2313_;
v___y_2242_ = v___x_2294_;
v___y_2243_ = v___x_2311_;
v___y_2244_ = v___y_2282_;
v___y_2245_ = v___x_2317_;
v___y_2246_ = v___x_2308_;
v___y_2247_ = v___x_2303_;
v___y_2248_ = v___x_2335_;
goto v___jp_2222_;
}
}
}
}
v___jp_2338_:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2341_);
lean_inc(v_fst_2083_);
v___x_2343_ = l_Lean_Parser_isTerminalCommand(v_fst_2083_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v_toProcessingContext_2345_; lean_object* v_pos_2346_; lean_object* v_endPos_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2344_ = lean_io_promise_new();
v_toProcessingContext_2345_ = lean_ctor_get(v_a_2073_, 0);
v_pos_2346_ = lean_ctor_get(v_fst_2071_, 0);
v_endPos_2347_ = lean_ctor_get(v_toProcessingContext_2345_, 3);
lean_inc(v___x_2344_);
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2344_);
v___x_2349_ = lean_box(0);
lean_inc(v_endPos_2347_);
lean_inc(v_pos_2346_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_pos_2346_);
lean_ctor_set(v___x_2350_, 1, v_endPos_2347_);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_parseCancelTk_2087_);
v___x_2353_ = l_IO_Promise_result_x21___redArg(v___x_2344_);
lean_dec(v___x_2344_);
v___x_2354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2349_);
lean_ctor_set(v___x_2354_, 1, v___x_2351_);
lean_ctor_set(v___x_2354_, 2, v___x_2352_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
v___y_2280_ = v___y_2339_;
v___y_2281_ = v___x_2348_;
v___y_2282_ = v___x_2342_;
v___y_2283_ = v___y_2340_;
v___y_2284_ = v___x_2355_;
goto v___jp_2279_;
}
else
{
lean_object* v___x_2356_; 
lean_dec(v_parseCancelTk_2087_);
v___x_2356_ = lean_box(0);
v___y_2280_ = v___y_2339_;
v___y_2281_ = v___x_2356_;
v___y_2282_ = v___x_2342_;
v___y_2283_ = v___y_2340_;
v___y_2284_ = v___x_2356_;
goto v___jp_2279_;
}
}
v___jp_2357_:
{
lean_object* v___x_2360_; 
lean_inc(v_fst_2083_);
v___x_2360_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2083_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_box(0);
v___y_2339_ = v_fst_2358_;
v___y_2340_ = v_snd_2359_;
v___y_2341_ = v___x_2361_;
goto v___jp_2338_;
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_val_2362_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2364_ = v___x_2360_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v___x_2360_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_inc(v_val_2362_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_val_2362_);
lean_ctor_set(v___x_2366_, 1, v_val_2362_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
v___y_2339_ = v_fst_2358_;
v___y_2340_ = v_snd_2359_;
v___y_2341_ = v___x_2368_;
goto v___jp_2338_;
}
}
}
}
v___jp_2371_:
{
if (v___y_2372_ == 0)
{
lean_inc_ref(v_fst_2071_);
lean_inc(v_fst_2083_);
v_fst_2358_ = v_fst_2083_;
v_snd_2359_ = v_fst_2071_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_box(0);
v___x_2374_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2358_ = v___x_2373_;
v_snd_2359_ = v___x_2374_;
goto v___jp_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_fst_2377_ = _args[0];
lean_object* v_val_2378_ = _args[1];
lean_object* v_a_2379_ = _args[2];
lean_object* v_snd_2380_ = _args[3];
lean_object* v___x_2381_ = _args[4];
lean_object* v___x_2382_ = _args[5];
lean_object* v_prom_2383_ = _args[6];
lean_object* v___x_2384_ = _args[7];
lean_object* v___f_2385_ = _args[8];
lean_object* v___f_2386_ = _args[9];
lean_object* v___f_2387_ = _args[10];
lean_object* v_pos_2388_ = _args[11];
lean_object* v_fst_2389_ = _args[12];
lean_object* v_cmdState_2390_ = _args[13];
lean_object* v_opts_2391_ = _args[14];
lean_object* v_old_x3f_2392_ = _args[15];
lean_object* v_parseCancelTk_2393_ = _args[16];
lean_object* v___y_2394_ = _args[17];
_start:
{
uint8_t v_val_45703__boxed_2395_; uint8_t v___x_45706__boxed_2396_; lean_object* v_res_2397_; 
v_val_45703__boxed_2395_ = lean_unbox(v_val_2378_);
v___x_45706__boxed_2396_ = lean_unbox(v___x_2382_);
v_res_2397_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_fst_2377_, v_val_45703__boxed_2395_, v_a_2379_, v_snd_2380_, v___x_2381_, v___x_45706__boxed_2396_, v_prom_2383_, v___x_2384_, v___f_2385_, v___f_2386_, v___f_2387_, v_pos_2388_, v_fst_2389_, v_cmdState_2390_, v_opts_2391_, v_old_x3f_2392_, v_parseCancelTk_2393_);
lean_dec_ref(v_opts_2391_);
lean_dec(v_prom_2383_);
lean_dec_ref(v_a_2379_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2400_, lean_object* v_parserState_2401_, lean_object* v_cmdState_2402_, lean_object* v_prom_2403_, uint8_t v_sync_2404_, lean_object* v_parseCancelTk_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_toSnapshot_2409_; lean_object* v_stx_2410_; lean_object* v_parserState_2411_; lean_object* v_elabSnap_2412_; lean_object* v_val_2413_; lean_object* v_newParserState_2414_; lean_object* v___y_2448_; lean_object* v___y_2450_; uint8_t v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2486_; uint8_t v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; uint8_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; 
v___f_2490_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2491_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2492_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2493_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2400_) == 1)
{
lean_object* v_val_2638_; lean_object* v_nextCmdSnap_x3f_2639_; 
v_val_2638_ = lean_ctor_get(v_old_x3f_2400_, 0);
v_nextCmdSnap_x3f_2639_ = lean_ctor_get(v_val_2638_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2639_) == 0)
{
goto v___jp_2605_;
}
else
{
lean_object* v_toSnapshot_2640_; lean_object* v_stx_2641_; lean_object* v_parserState_2642_; lean_object* v_elabSnap_2643_; lean_object* v_val_2644_; lean_object* v___x_2645_; 
v_toSnapshot_2640_ = lean_ctor_get(v_val_2638_, 0);
v_stx_2641_ = lean_ctor_get(v_val_2638_, 1);
v_parserState_2642_ = lean_ctor_get(v_val_2638_, 2);
v_elabSnap_2643_ = lean_ctor_get(v_val_2638_, 3);
v_val_2644_ = lean_ctor_get(v_nextCmdSnap_x3f_2639_, 0);
lean_inc(v_val_2644_);
v___x_2645_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2644_);
if (lean_obj_tag(v___x_2645_) == 1)
{
lean_object* v_val_2646_; lean_object* v_nextCmdSnap_x3f_2647_; 
v_val_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_val_2646_);
lean_dec_ref(v___x_2645_);
v_nextCmdSnap_x3f_2647_ = lean_ctor_get(v_val_2646_, 4);
lean_inc(v_nextCmdSnap_x3f_2647_);
lean_dec(v_val_2646_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2647_) == 0)
{
goto v___jp_2605_;
}
else
{
lean_object* v_val_2648_; lean_object* v___x_2649_; 
v_val_2648_ = lean_ctor_get(v_nextCmdSnap_x3f_2647_, 0);
lean_inc(v_val_2648_);
lean_dec_ref(v_nextCmdSnap_x3f_2647_);
v___x_2649_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2648_);
if (lean_obj_tag(v___x_2649_) == 1)
{
lean_object* v_val_2650_; lean_object* v_parserState_2651_; lean_object* v_pos_2652_; uint8_t v___x_2653_; 
v_val_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_val_2650_);
lean_dec_ref(v___x_2649_);
v_parserState_2651_ = lean_ctor_get(v_val_2650_, 2);
lean_inc_ref(v_parserState_2651_);
lean_dec(v_val_2650_);
v_pos_2652_ = lean_ctor_get(v_parserState_2651_, 0);
lean_inc(v_pos_2652_);
lean_dec_ref(v_parserState_2651_);
v___x_2653_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2652_, v_a_2406_);
lean_dec(v_pos_2652_);
if (v___x_2653_ == 0)
{
goto v___jp_2605_;
}
else
{
lean_inc(v_val_2644_);
lean_inc_ref(v_elabSnap_2643_);
lean_inc_ref_n(v_parserState_2642_, 2);
lean_inc(v_stx_2641_);
lean_inc_ref(v_toSnapshot_2640_);
lean_dec_ref(v_old_x3f_2400_);
lean_dec(v_parseCancelTk_2405_);
lean_dec_ref(v_cmdState_2402_);
lean_dec_ref(v_parserState_2401_);
v_toSnapshot_2409_ = v_toSnapshot_2640_;
v_stx_2410_ = v_stx_2641_;
v_parserState_2411_ = v_parserState_2642_;
v_elabSnap_2412_ = v_elabSnap_2643_;
v_val_2413_ = v_val_2644_;
v_newParserState_2414_ = v_parserState_2642_;
goto v___jp_2408_;
}
}
else
{
lean_dec(v___x_2649_);
goto v___jp_2605_;
}
}
}
else
{
lean_dec(v___x_2645_);
goto v___jp_2605_;
}
}
}
else
{
goto v___jp_2605_;
}
v___jp_2408_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_resultSnap_2417_; lean_object* v_task_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2441_; 
v___x_2415_ = lean_io_promise_new();
v___x_2416_ = l_IO_CancelToken_new();
v_resultSnap_2417_ = lean_ctor_get(v_elabSnap_2412_, 2);
lean_inc_ref(v_resultSnap_2417_);
v_task_2418_ = lean_ctor_get(v_resultSnap_2417_, 3);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_resultSnap_2417_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; 
v_unused_2442_ = lean_ctor_get(v_resultSnap_2417_, 2);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_resultSnap_2417_, 1);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_resultSnap_2417_, 0);
lean_dec(v_unused_2444_);
v___x_2420_ = v_resultSnap_2417_;
v_isShared_2421_ = v_isSharedCheck_2441_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_task_2418_);
lean_dec(v_resultSnap_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2441_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v_toProcessingContext_2427_; lean_object* v_pos_2428_; lean_object* v_endPos_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2422_ = lean_box(v_sync_2404_);
lean_inc_ref(v_a_2406_);
lean_inc(v___x_2416_);
lean_inc(v___x_2415_);
lean_inc_ref(v_newParserState_2414_);
v___f_2423_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2423_, 0, v_val_2413_);
lean_closure_set(v___f_2423_, 1, v_newParserState_2414_);
lean_closure_set(v___f_2423_, 2, v___x_2415_);
lean_closure_set(v___f_2423_, 3, v___x_2422_);
lean_closure_set(v___f_2423_, 4, v___x_2416_);
lean_closure_set(v___f_2423_, 5, v_a_2406_);
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = 1;
v___x_2426_ = l_BaseIO_chainTask___redArg(v_task_2418_, v___f_2423_, v___x_2424_, v___x_2425_);
v_toProcessingContext_2427_ = lean_ctor_get(v_a_2406_, 0);
v_pos_2428_ = lean_ctor_get(v_newParserState_2414_, 0);
lean_inc(v_pos_2428_);
lean_dec_ref(v_newParserState_2414_);
v_endPos_2429_ = lean_ctor_get(v_toProcessingContext_2427_, 3);
v___x_2430_ = lean_box(0);
lean_inc(v_endPos_2429_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_pos_2428_);
lean_ctor_set(v___x_2431_, 1, v_endPos_2429_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2416_);
v___x_2434_ = l_IO_Promise_result_x21___redArg(v___x_2415_);
lean_dec(v___x_2415_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 3, v___x_2434_);
lean_ctor_set(v___x_2420_, 2, v___x_2433_);
lean_ctor_set(v___x_2420_, 1, v___x_2432_);
lean_ctor_set(v___x_2420_, 0, v___x_2430_);
v___x_2436_ = v___x_2420_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2438_, 0, v_toSnapshot_2409_);
lean_ctor_set(v___x_2438_, 1, v_stx_2410_);
lean_ctor_set(v___x_2438_, 2, v_parserState_2411_);
lean_ctor_set(v___x_2438_, 3, v_elabSnap_2412_);
lean_ctor_set(v___x_2438_, 4, v___x_2437_);
v___x_2439_ = lean_io_promise_resolve(v___x_2438_, v_prom_2403_);
lean_dec(v_prom_2403_);
return v___x_2439_;
}
}
}
v___jp_2445_:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_box(0);
return v___x_2446_;
}
v___jp_2447_:
{
goto v___jp_2445_;
}
v___jp_2449_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2454_ = l_Lean_Name_str___override(v___y_2450_, v___x_2453_);
v___x_2455_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2456_ = l_Lean_Name_str___override(v___x_2454_, v___x_2455_);
v___x_2457_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2458_ = l_Lean_Name_str___override(v___x_2456_, v___x_2457_);
v___x_2459_ = l_Lean_Name_str___override(v___x_2458_, v___x_2455_);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = l_Lean_Name_num___override(v___x_2459_, v___x_2460_);
v___x_2462_ = l_Lean_Name_str___override(v___x_2461_, v___x_2455_);
v___x_2463_ = l_Lean_Name_str___override(v___x_2462_, v___x_2457_);
v___x_2464_ = l_Lean_Name_str___override(v___x_2463_, v___x_2455_);
v___x_2465_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2466_ = l_Lean_Name_str___override(v___x_2464_, v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2468_ = l_Lean_Name_str___override(v___x_2466_, v___x_2467_);
v___x_2469_ = l_Lean_Name_toString(v___x_2468_, v___y_2451_);
v___x_2470_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2473_ = 0;
v___x_2474_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2474_, 0, v___x_2469_);
lean_ctor_set(v___x_2474_, 1, v___x_2470_);
lean_ctor_set(v___x_2474_, 2, v___x_2471_);
lean_ctor_set(v___x_2474_, 3, v___x_2472_);
lean_ctor_set_uint8(v___x_2474_, sizeof(void*)*4, v___x_2473_);
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2474_, 3);
v___x_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2474_);
lean_ctor_set(v___x_2477_, 1, v_cmdState_2402_);
v___x_2478_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2471_, v___x_2477_);
v___x_2479_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2471_, v___x_2474_);
v___x_2480_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2474_);
lean_ctor_set(v___x_2481_, 1, v___x_2476_);
lean_ctor_set(v___x_2481_, 2, v___x_2478_);
lean_ctor_set(v___x_2481_, 3, v___x_2479_);
lean_ctor_set(v___x_2481_, 4, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2474_);
lean_ctor_set(v___x_2482_, 1, v___x_2475_);
lean_ctor_set(v___x_2482_, 2, v___y_2452_);
lean_ctor_set(v___x_2482_, 3, v___x_2481_);
lean_ctor_set(v___x_2482_, 4, v___x_2471_);
v___x_2483_ = lean_io_promise_resolve(v___x_2482_, v_prom_2403_);
lean_dec(v_prom_2403_);
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
v___jp_2485_:
{
v___y_2450_ = v___y_2486_;
v___y_2451_ = v___y_2487_;
v___y_2452_ = v___y_2488_;
goto v___jp_2449_;
}
v___jp_2494_:
{
lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2511_);
v___x_2513_ = l_Lean_Parser_isTerminalCommand(v___y_2510_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_io_promise_new();
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
v___x_2516_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2512_, v___y_2502_, v___y_2497_, v___y_2498_, v_a_2406_, v___y_2503_, v___y_2495_, v___y_2504_, v___y_2499_, v___y_2501_, v___y_2508_, v___y_2507_, v___y_2506_, v_prom_2403_, v___x_2493_, v___f_2492_, v___f_2491_, v___f_2490_, v___y_2496_, v___y_2500_, v_cmdState_2402_, v___y_2505_, v___y_2509_, v_old_x3f_2400_, v_parseCancelTk_2405_, v___x_2515_);
lean_dec_ref(v___y_2505_);
lean_dec(v_prom_2403_);
lean_dec(v___y_2508_);
lean_dec(v___y_2502_);
v___y_2448_ = v___x_2516_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_box(0);
v___x_2518_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2512_, v___y_2502_, v___y_2497_, v___y_2498_, v_a_2406_, v___y_2503_, v___y_2495_, v___y_2504_, v___y_2499_, v___y_2501_, v___y_2508_, v___y_2507_, v___y_2506_, v_prom_2403_, v___x_2493_, v___f_2492_, v___f_2491_, v___f_2490_, v___y_2496_, v___y_2500_, v_cmdState_2402_, v___y_2505_, v___y_2509_, v_old_x3f_2400_, v_parseCancelTk_2405_, v___x_2517_);
lean_dec_ref(v___y_2505_);
lean_dec(v_prom_2403_);
lean_dec(v___y_2508_);
lean_dec(v___y_2502_);
v___y_2448_ = v___x_2518_;
goto v___jp_2447_;
}
}
v___jp_2519_:
{
lean_object* v___x_2536_; 
lean_inc(v___y_2533_);
v___x_2536_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2533_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_box(0);
v___y_2495_ = v___y_2520_;
v___y_2496_ = v___y_2521_;
v___y_2497_ = v___y_2522_;
v___y_2498_ = v___y_2523_;
v___y_2499_ = v_fst_2534_;
v___y_2500_ = v___y_2524_;
v___y_2501_ = v___y_2525_;
v___y_2502_ = v___y_2526_;
v___y_2503_ = v___y_2527_;
v___y_2504_ = v___y_2528_;
v___y_2505_ = v___y_2529_;
v___y_2506_ = v_snd_2535_;
v___y_2507_ = v___y_2530_;
v___y_2508_ = v___y_2531_;
v___y_2509_ = v___y_2532_;
v___y_2510_ = v___y_2533_;
v___y_2511_ = v___x_2537_;
goto v___jp_2494_;
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2546_; 
v_val_2538_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_val_2538_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
lean_inc(v_val_2538_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_val_2538_);
lean_ctor_set(v___x_2542_, 1, v_val_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
v___y_2495_ = v___y_2520_;
v___y_2496_ = v___y_2521_;
v___y_2497_ = v___y_2522_;
v___y_2498_ = v___y_2523_;
v___y_2499_ = v_fst_2534_;
v___y_2500_ = v___y_2524_;
v___y_2501_ = v___y_2525_;
v___y_2502_ = v___y_2526_;
v___y_2503_ = v___y_2527_;
v___y_2504_ = v___y_2528_;
v___y_2505_ = v___y_2529_;
v___y_2506_ = v_snd_2535_;
v___y_2507_ = v___y_2530_;
v___y_2508_ = v___y_2531_;
v___y_2509_ = v___y_2532_;
v___y_2510_ = v___y_2533_;
v___y_2511_ = v___x_2544_;
goto v___jp_2494_;
}
}
}
}
v___jp_2547_:
{
if (v___y_2563_ == 0)
{
lean_inc(v___y_2562_);
v___y_2520_ = v___y_2548_;
v___y_2521_ = v___y_2549_;
v___y_2522_ = v___y_2550_;
v___y_2523_ = v___y_2551_;
v___y_2524_ = v___y_2552_;
v___y_2525_ = v___y_2553_;
v___y_2526_ = v___y_2554_;
v___y_2527_ = v___y_2555_;
v___y_2528_ = v___y_2556_;
v___y_2529_ = v___y_2557_;
v___y_2530_ = v___y_2558_;
v___y_2531_ = v___y_2559_;
v___y_2532_ = v___y_2560_;
v___y_2533_ = v___y_2562_;
v_fst_2534_ = v___y_2562_;
v_snd_2535_ = v___y_2561_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v___y_2561_);
v___x_2564_ = lean_box(0);
v___x_2565_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2520_ = v___y_2548_;
v___y_2521_ = v___y_2549_;
v___y_2522_ = v___y_2550_;
v___y_2523_ = v___y_2551_;
v___y_2524_ = v___y_2552_;
v___y_2525_ = v___y_2553_;
v___y_2526_ = v___y_2554_;
v___y_2527_ = v___y_2555_;
v___y_2528_ = v___y_2556_;
v___y_2529_ = v___y_2557_;
v___y_2530_ = v___y_2558_;
v___y_2531_ = v___y_2559_;
v___y_2532_ = v___y_2560_;
v___y_2533_ = v___y_2562_;
v_fst_2534_ = v___x_2564_;
v_snd_2535_ = v___x_2565_;
goto v___jp_2519_;
}
}
v___jp_2566_:
{
uint8_t v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = l_IO_CancelToken_isSet(v_parseCancelTk_2405_);
v___x_2578_ = 1;
if (v___x_2577_ == 0)
{
lean_dec(v___y_2573_);
if (v_sync_2404_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2579_ = lean_io_promise_new();
v___x_2580_ = lean_io_promise_new();
v___x_2581_ = lean_io_promise_new();
v___x_2582_ = lean_io_promise_new();
v___x_2583_ = l_Lean_internal_cmdlineSnapshots;
v___x_2584_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2574_, v___x_2583_);
lean_dec_ref(v___y_2574_);
if (v___x_2584_ == 0)
{
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2568_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___x_2577_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___x_2579_;
v___y_2554_ = v___x_2582_;
v___y_2555_ = v___y_2567_;
v___y_2556_ = v___x_2578_;
v___y_2557_ = v___y_2570_;
v___y_2558_ = v___x_2581_;
v___y_2559_ = v___x_2580_;
v___y_2560_ = v___x_2583_;
v___y_2561_ = v___y_2575_;
v___y_2562_ = v___y_2576_;
v___y_2563_ = v___x_2584_;
goto v___jp_2547_;
}
else
{
uint8_t v___x_2585_; 
lean_inc(v___y_2576_);
v___x_2585_ = l_Lean_Parser_isTerminalCommand(v___y_2576_);
if (v___x_2585_ == 0)
{
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2568_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___x_2577_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___x_2579_;
v___y_2554_ = v___x_2582_;
v___y_2555_ = v___y_2567_;
v___y_2556_ = v___x_2578_;
v___y_2557_ = v___y_2570_;
v___y_2558_ = v___x_2581_;
v___y_2559_ = v___x_2580_;
v___y_2560_ = v___x_2583_;
v___y_2561_ = v___y_2575_;
v___y_2562_ = v___y_2576_;
v___y_2563_ = v___x_2584_;
goto v___jp_2547_;
}
else
{
lean_inc(v___y_2576_);
v___y_2520_ = v___y_2569_;
v___y_2521_ = v___y_2568_;
v___y_2522_ = v___y_2571_;
v___y_2523_ = v___x_2577_;
v___y_2524_ = v___y_2572_;
v___y_2525_ = v___x_2579_;
v___y_2526_ = v___x_2582_;
v___y_2527_ = v___y_2567_;
v___y_2528_ = v___x_2578_;
v___y_2529_ = v___y_2570_;
v___y_2530_ = v___x_2581_;
v___y_2531_ = v___x_2580_;
v___y_2532_ = v___x_2583_;
v___y_2533_ = v___y_2576_;
v_fst_2534_ = v___y_2576_;
v_snd_2535_ = v___y_2575_;
goto v___jp_2519_;
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
v___x_2586_ = lean_box(v___x_2577_);
v___x_2587_ = lean_box(v___x_2578_);
lean_inc_ref(v_a_2406_);
v___f_2588_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 18, 17);
lean_closure_set(v___f_2588_, 0, v___y_2571_);
lean_closure_set(v___f_2588_, 1, v___x_2586_);
lean_closure_set(v___f_2588_, 2, v_a_2406_);
lean_closure_set(v___f_2588_, 3, v___y_2567_);
lean_closure_set(v___f_2588_, 4, v___y_2569_);
lean_closure_set(v___f_2588_, 5, v___x_2587_);
lean_closure_set(v___f_2588_, 6, v_prom_2403_);
lean_closure_set(v___f_2588_, 7, v___x_2493_);
lean_closure_set(v___f_2588_, 8, v___f_2492_);
lean_closure_set(v___f_2588_, 9, v___f_2491_);
lean_closure_set(v___f_2588_, 10, v___f_2490_);
lean_closure_set(v___f_2588_, 11, v___y_2568_);
lean_closure_set(v___f_2588_, 12, v___y_2572_);
lean_closure_set(v___f_2588_, 13, v_cmdState_2402_);
lean_closure_set(v___f_2588_, 14, v___y_2570_);
lean_closure_set(v___f_2588_, 15, v_old_x3f_2400_);
lean_closure_set(v___f_2588_, 16, v_parseCancelTk_2405_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_io_as_task(v___f_2588_, v___x_2589_);
lean_dec_ref(v___x_2590_);
goto v___jp_2445_;
}
}
else
{
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v_parseCancelTk_2405_);
if (lean_obj_tag(v_old_x3f_2400_) == 1)
{
lean_object* v_val_2591_; lean_object* v___x_2592_; lean_object* v_children_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v_val_2591_ = lean_ctor_get(v_old_x3f_2400_, 0);
lean_inc(v_val_2591_);
lean_dec_ref(v_old_x3f_2400_);
v___x_2592_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_val_2591_);
v_children_2593_ = lean_ctor_get(v___x_2592_, 1);
lean_inc_ref(v_children_2593_);
lean_dec_ref(v___x_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_array_get_size(v_children_2593_);
v___x_2596_ = lean_nat_dec_lt(v___x_2594_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_dec_ref(v_children_2593_);
v___y_2450_ = v___y_2573_;
v___y_2451_ = v___x_2578_;
v___y_2452_ = v___y_2575_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_nat_dec_le(v___x_2595_, v___x_2595_);
if (v___x_2598_ == 0)
{
if (v___x_2596_ == 0)
{
lean_dec_ref(v_children_2593_);
v___y_2450_ = v___y_2573_;
v___y_2451_ = v___x_2578_;
v___y_2452_ = v___y_2575_;
goto v___jp_2449_;
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = lean_usize_of_nat(v___x_2595_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2593_, v___x_2599_, v___x_2600_, v___x_2597_);
lean_dec_ref(v_children_2593_);
v___y_2486_ = v___y_2573_;
v___y_2487_ = v___x_2578_;
v___y_2488_ = v___y_2575_;
v___y_2489_ = v___x_2601_;
goto v___jp_2485_;
}
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = ((size_t)0ULL);
v___x_2603_ = lean_usize_of_nat(v___x_2595_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2593_, v___x_2602_, v___x_2603_, v___x_2597_);
lean_dec_ref(v_children_2593_);
v___y_2486_ = v___y_2573_;
v___y_2487_ = v___x_2578_;
v___y_2488_ = v___y_2575_;
v___y_2489_ = v___x_2604_;
goto v___jp_2485_;
}
}
}
else
{
lean_dec(v_old_x3f_2400_);
v___y_2450_ = v___y_2573_;
v___y_2451_ = v___x_2578_;
v___y_2452_ = v___y_2575_;
goto v___jp_2449_;
}
}
}
v___jp_2605_:
{
lean_object* v_env_2606_; lean_object* v_scopes_2607_; lean_object* v___x_2608_; lean_object* v_opts_2609_; lean_object* v_currNamespace_2610_; lean_object* v_openDecls_2611_; lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v_snd_2617_; 
v_env_2606_ = lean_ctor_get(v_cmdState_2402_, 0);
v_scopes_2607_ = lean_ctor_get(v_cmdState_2402_, 2);
v___x_2608_ = l_List_head_x21___redArg(v___x_2493_, v_scopes_2607_);
v_opts_2609_ = lean_ctor_get(v___x_2608_, 1);
lean_inc_ref_n(v_opts_2609_, 2);
v_currNamespace_2610_ = lean_ctor_get(v___x_2608_, 2);
lean_inc(v_currNamespace_2610_);
v_openDecls_2611_ = lean_ctor_get(v___x_2608_, 3);
lean_inc(v_openDecls_2611_);
lean_dec(v___x_2608_);
lean_inc_ref(v_env_2606_);
v___x_2612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2612_, 0, v_env_2606_);
lean_ctor_set(v___x_2612_, 1, v_opts_2609_);
lean_ctor_set(v___x_2612_, 2, v_currNamespace_2610_);
lean_ctor_set(v___x_2612_, 3, v_openDecls_2611_);
lean_inc_ref(v_parserState_2401_);
lean_inc_ref(v_a_2406_);
v___f_2613_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2613_, 0, v_a_2406_);
lean_closure_set(v___f_2613_, 1, v___x_2612_);
lean_closure_set(v___f_2613_, 2, v_parserState_2401_);
v___x_2614_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_profileit(v___x_2614_, v_opts_2609_, v___f_2613_, v___x_2615_);
v_snd_2617_ = lean_ctor_get(v___x_2616_, 1);
lean_inc(v_snd_2617_);
if (lean_obj_tag(v_old_x3f_2400_) == 1)
{
lean_object* v_val_2618_; lean_object* v_fst_2619_; lean_object* v_fst_2620_; lean_object* v_snd_2621_; lean_object* v_pos_2622_; lean_object* v_toSnapshot_2623_; lean_object* v_stx_2624_; lean_object* v_parserState_2625_; lean_object* v_elabSnap_2626_; lean_object* v_nextCmdSnap_x3f_2627_; uint8_t v___x_2628_; 
v_val_2618_ = lean_ctor_get(v_old_x3f_2400_, 0);
v_fst_2619_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_n(v_fst_2619_, 2);
lean_dec(v___x_2616_);
v_fst_2620_ = lean_ctor_get(v_snd_2617_, 0);
lean_inc(v_fst_2620_);
v_snd_2621_ = lean_ctor_get(v_snd_2617_, 1);
lean_inc(v_snd_2621_);
lean_dec(v_snd_2617_);
v_pos_2622_ = lean_ctor_get(v_parserState_2401_, 0);
lean_inc(v_pos_2622_);
lean_dec_ref(v_parserState_2401_);
v_toSnapshot_2623_ = lean_ctor_get(v_val_2618_, 0);
v_stx_2624_ = lean_ctor_get(v_val_2618_, 1);
v_parserState_2625_ = lean_ctor_get(v_val_2618_, 2);
v_elabSnap_2626_ = lean_ctor_get(v_val_2618_, 3);
v_nextCmdSnap_x3f_2627_ = lean_ctor_get(v_val_2618_, 4);
lean_inc(v_stx_2624_);
v___x_2628_ = l_Lean_Syntax_eqWithInfo(v_fst_2619_, v_stx_2624_);
if (v___x_2628_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2627_) == 0)
{
lean_inc(v_fst_2619_);
lean_inc(v_fst_2620_);
lean_inc_ref(v_opts_2609_);
v___y_2567_ = v_snd_2621_;
v___y_2568_ = v_pos_2622_;
v___y_2569_ = v___x_2615_;
v___y_2570_ = v_opts_2609_;
v___y_2571_ = v_fst_2620_;
v___y_2572_ = v_fst_2619_;
v___y_2573_ = v___x_2615_;
v___y_2574_ = v_opts_2609_;
v___y_2575_ = v_fst_2620_;
v___y_2576_ = v_fst_2619_;
goto v___jp_2566_;
}
else
{
lean_object* v_val_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v_val_2629_ = lean_ctor_get(v_nextCmdSnap_x3f_2627_, 0);
v___x_2630_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2629_);
v___x_2631_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2630_, v_val_2629_);
lean_inc(v_fst_2619_);
lean_inc(v_fst_2620_);
lean_inc_ref(v_opts_2609_);
v___y_2567_ = v_snd_2621_;
v___y_2568_ = v_pos_2622_;
v___y_2569_ = v___x_2615_;
v___y_2570_ = v_opts_2609_;
v___y_2571_ = v_fst_2620_;
v___y_2572_ = v_fst_2619_;
v___y_2573_ = v___x_2615_;
v___y_2574_ = v_opts_2609_;
v___y_2575_ = v_fst_2620_;
v___y_2576_ = v_fst_2619_;
goto v___jp_2566_;
}
}
else
{
lean_inc(v_val_2618_);
lean_dec(v_pos_2622_);
lean_dec(v_snd_2621_);
lean_dec(v_fst_2619_);
lean_dec_ref(v_old_x3f_2400_);
lean_dec_ref(v_opts_2609_);
lean_dec(v_parseCancelTk_2405_);
lean_dec_ref(v_cmdState_2402_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2627_) == 1)
{
lean_object* v_val_2632_; 
lean_inc_ref(v_nextCmdSnap_x3f_2627_);
lean_inc_ref(v_elabSnap_2626_);
lean_inc_ref(v_parserState_2625_);
lean_inc(v_stx_2624_);
lean_inc_ref(v_toSnapshot_2623_);
lean_dec(v_val_2618_);
v_val_2632_ = lean_ctor_get(v_nextCmdSnap_x3f_2627_, 0);
lean_inc(v_val_2632_);
lean_dec_ref(v_nextCmdSnap_x3f_2627_);
v_toSnapshot_2409_ = v_toSnapshot_2623_;
v_stx_2410_ = v_stx_2624_;
v_parserState_2411_ = v_parserState_2625_;
v_elabSnap_2412_ = v_elabSnap_2626_;
v_val_2413_ = v_val_2632_;
v_newParserState_2414_ = v_fst_2620_;
goto v___jp_2408_;
}
else
{
lean_object* v___x_2633_; 
lean_dec(v_fst_2620_);
v___x_2633_ = lean_io_promise_resolve(v_val_2618_, v_prom_2403_);
lean_dec(v_prom_2403_);
return v___x_2633_;
}
}
}
else
{
lean_object* v_fst_2634_; lean_object* v_fst_2635_; lean_object* v_snd_2636_; lean_object* v_pos_2637_; 
v_fst_2634_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_n(v_fst_2634_, 2);
lean_dec(v___x_2616_);
v_fst_2635_ = lean_ctor_get(v_snd_2617_, 0);
lean_inc_n(v_fst_2635_, 2);
v_snd_2636_ = lean_ctor_get(v_snd_2617_, 1);
lean_inc(v_snd_2636_);
lean_dec(v_snd_2617_);
v_pos_2637_ = lean_ctor_get(v_parserState_2401_, 0);
lean_inc(v_pos_2637_);
lean_dec_ref(v_parserState_2401_);
lean_inc_ref(v_opts_2609_);
v___y_2567_ = v_snd_2636_;
v___y_2568_ = v_pos_2637_;
v___y_2569_ = v___x_2615_;
v___y_2570_ = v_opts_2609_;
v___y_2571_ = v_fst_2635_;
v___y_2572_ = v_fst_2634_;
v___y_2573_ = v___x_2615_;
v___y_2574_ = v_opts_2609_;
v___y_2575_ = v_fst_2635_;
v___y_2576_ = v_fst_2634_;
goto v___jp_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2654_, lean_object* v_newParserState_2655_, lean_object* v_val_2656_, uint8_t v_sync_2657_, lean_object* v_val_2658_, lean_object* v_a_2659_, lean_object* v_oldNext_2660_){
_start:
{
lean_object* v_cmdState_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_cmdState_2662_ = lean_ctor_get(v_oldResult_2654_, 1);
lean_inc_ref(v_cmdState_2662_);
lean_dec_ref(v_oldResult_2654_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_oldNext_2660_);
v___x_2664_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2663_, v_newParserState_2655_, v_cmdState_2662_, v_val_2656_, v_sync_2657_, v_val_2658_, v_a_2659_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2665_ = _args[0];
lean_object* v_val_2666_ = _args[1];
lean_object* v_fst_2667_ = _args[2];
lean_object* v_val_2668_ = _args[3];
lean_object* v_a_2669_ = _args[4];
lean_object* v_snd_2670_ = _args[5];
lean_object* v___x_2671_ = _args[6];
lean_object* v___x_2672_ = _args[7];
lean_object* v_fst_2673_ = _args[8];
lean_object* v_val_2674_ = _args[9];
lean_object* v_val_2675_ = _args[10];
lean_object* v_val_2676_ = _args[11];
lean_object* v_snd_2677_ = _args[12];
lean_object* v_prom_2678_ = _args[13];
lean_object* v___x_2679_ = _args[14];
lean_object* v___f_2680_ = _args[15];
lean_object* v___f_2681_ = _args[16];
lean_object* v___f_2682_ = _args[17];
lean_object* v_pos_2683_ = _args[18];
lean_object* v_fst_2684_ = _args[19];
lean_object* v_cmdState_2685_ = _args[20];
lean_object* v_opts_2686_ = _args[21];
lean_object* v___x_2687_ = _args[22];
lean_object* v_old_x3f_2688_ = _args[23];
lean_object* v_parseCancelTk_2689_ = _args[24];
lean_object* v_next_x3f_2690_ = _args[25];
lean_object* v___y_2691_ = _args[26];
_start:
{
uint8_t v_val_45488__boxed_2692_; uint8_t v___x_45491__boxed_2693_; lean_object* v_res_2694_; 
v_val_45488__boxed_2692_ = lean_unbox(v_val_2668_);
v___x_45491__boxed_2693_ = lean_unbox(v___x_2672_);
v_res_2694_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2665_, v_val_2666_, v_fst_2667_, v_val_45488__boxed_2692_, v_a_2669_, v_snd_2670_, v___x_2671_, v___x_45491__boxed_2693_, v_fst_2673_, v_val_2674_, v_val_2675_, v_val_2676_, v_snd_2677_, v_prom_2678_, v___x_2679_, v___f_2680_, v___f_2681_, v___f_2682_, v_pos_2683_, v_fst_2684_, v_cmdState_2685_, v_opts_2686_, v___x_2687_, v_old_x3f_2688_, v_parseCancelTk_2689_, v_next_x3f_2690_);
lean_dec_ref(v___x_2687_);
lean_dec_ref(v_opts_2686_);
lean_dec(v_prom_2678_);
lean_dec(v_val_2675_);
lean_dec_ref(v_a_2669_);
lean_dec(v_val_2666_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2695_, lean_object* v_parserState_2696_, lean_object* v_cmdState_2697_, lean_object* v_prom_2698_, lean_object* v_sync_2699_, lean_object* v_parseCancelTk_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
uint8_t v_sync_boxed_2703_; lean_object* v_res_2704_; 
v_sync_boxed_2703_ = lean_unbox(v_sync_2699_);
v_res_2704_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2695_, v_parserState_2696_, v_cmdState_2697_, v_prom_2698_, v_sync_boxed_2703_, v_parseCancelTk_2700_, v_a_2701_);
lean_dec_ref(v_a_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2705_, size_t v_i_2706_, size_t v_stop_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2705_, v_i_2706_, v_stop_2707_, v_b_2708_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2712_, lean_object* v_i_2713_, lean_object* v_stop_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
size_t v_i_boxed_2718_; size_t v_stop_boxed_2719_; lean_object* v_res_2720_; 
v_i_boxed_2718_ = lean_unbox_usize(v_i_2713_);
lean_dec(v_i_2713_);
v_stop_boxed_2719_ = lean_unbox_usize(v_stop_2714_);
lean_dec(v_stop_2714_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2712_, v_i_boxed_2718_, v_stop_boxed_2719_, v_b_2715_, v___y_2716_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v_as_2712_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2721_, lean_object* v_opt_2722_){
_start:
{
lean_object* v_name_2723_; lean_object* v_map_2724_; lean_object* v___x_2725_; 
v_name_2723_ = lean_ctor_get(v_opt_2722_, 0);
v_map_2724_ = lean_ctor_get(v_opts_2721_, 0);
v___x_2725_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2724_, v_name_2723_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_box(0);
return v___x_2726_;
}
else
{
lean_object* v_val_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2736_; 
v_val_2727_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2729_ = v___x_2725_;
v_isShared_2730_ = v_isSharedCheck_2736_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_val_2727_);
lean_dec(v___x_2725_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2736_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
if (lean_obj_tag(v_val_2727_) == 0)
{
lean_object* v_v_2731_; lean_object* v___x_2733_; 
v_v_2731_ = lean_ctor_get(v_val_2727_, 0);
lean_inc_ref(v_v_2731_);
lean_dec_ref(v_val_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v_v_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_v_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
else
{
lean_object* v___x_2735_; 
lean_del_object(v___x_2729_);
lean_dec(v_val_2727_);
v___x_2735_ = lean_box(0);
return v___x_2735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2737_, lean_object* v_opt_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2737_, v_opt_2738_);
lean_dec_ref(v_opt_2738_);
lean_dec_ref(v_opts_2737_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2740_, lean_object* v_x_2741_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2740_);
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2744_, 0, v_x_2741_);
lean_ctor_set(v___x_2744_, 1, v___x_2742_);
lean_ctor_set(v___x_2744_, 2, v___x_2743_);
return v___x_2744_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2751_ = l_Array_toPArray_x27___redArg(v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
if (lean_obj_tag(v_a_2752_) == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = l_List_reverse___redArg(v_a_2753_);
return v___x_2754_;
}
else
{
lean_object* v_head_2755_; lean_object* v_tail_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2769_; 
v_head_2755_ = lean_ctor_get(v_a_2752_, 0);
v_tail_2756_ = lean_ctor_get(v_a_2752_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2758_ = v_a_2752_;
v_isShared_2759_ = v_isSharedCheck_2769_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_tail_2756_);
lean_inc(v_head_2755_);
lean_dec(v_a_2752_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2769_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2760_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
lean_ctor_set(v___x_2761_, 1, v_head_2755_);
v___x_2762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
v___x_2763_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v_a_2753_);
lean_ctor_set(v___x_2758_, 0, v___x_2764_);
v___x_2766_ = v___x_2758_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_a_2753_);
v___x_2766_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
v_a_2752_ = v_tail_2756_;
v_a_2753_ = v___x_2766_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2780_; double v___x_2781_; 
v___x_2780_ = lean_unsigned_to_nat(1000000000u);
v___x_2781_ = lean_float_of_nat(v___x_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2789_ = l_Lean_MessageData_ofFormat(v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2790_, lean_object* v_stx_2791_, lean_object* v_origStx_2792_, lean_object* v_toProcessingContext_2793_, lean_object* v___x_2794_, lean_object* v_fileMap_2795_, lean_object* v_parserState_2796_, lean_object* v_a_2797_, lean_object* v___x_2798_, lean_object* v___x_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_toProcessingContext_2802_; lean_object* v___x_2803_; 
v_toProcessingContext_2802_ = lean_ctor_get(v___y_2800_, 0);
lean_inc_ref(v_toProcessingContext_2802_);
lean_inc(v_stx_2791_);
v___x_2803_ = lean_apply_3(v_setupImports_2790_, v_stx_2791_, v_toProcessingContext_2802_, lean_box(0));
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_3013_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_3013_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_3013_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
if (lean_obj_tag(v_a_2804_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; 
lean_dec_ref(v___x_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v_parserState_2796_);
lean_dec_ref(v_fileMap_2795_);
lean_dec(v___x_2794_);
lean_dec_ref(v_toProcessingContext_2793_);
lean_dec(v_origStx_2792_);
lean_dec(v_stx_2791_);
v_a_2808_ = lean_ctor_get(v_a_2804_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v_a_2804_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v_a_2808_);
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_3012_; 
v_a_2812_ = lean_ctor_get(v_a_2804_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_a_2804_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2814_ = v_a_2804_;
v_isShared_2815_ = v_isSharedCheck_3012_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v_a_2804_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_3012_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v_mainModuleName_2817_; lean_object* v_package_x3f_2818_; uint8_t v_isModule_2819_; lean_object* v_imports_2820_; lean_object* v_opts_2821_; uint32_t v_trustLevel_2822_; lean_object* v_importArts_2823_; lean_object* v_plugins_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2829_; 
v___x_2816_ = lean_io_mono_nanos_now();
v_mainModuleName_2817_ = lean_ctor_get(v_a_2812_, 0);
lean_inc(v_mainModuleName_2817_);
v_package_x3f_2818_ = lean_ctor_get(v_a_2812_, 1);
lean_inc(v_package_x3f_2818_);
v_isModule_2819_ = lean_ctor_get_uint8(v_a_2812_, sizeof(void*)*6 + 4);
v_imports_2820_ = lean_ctor_get(v_a_2812_, 2);
lean_inc_ref(v_imports_2820_);
v_opts_2821_ = lean_ctor_get(v_a_2812_, 3);
lean_inc_ref(v_opts_2821_);
v_trustLevel_2822_ = lean_ctor_get_uint32(v_a_2812_, sizeof(void*)*6);
v_importArts_2823_ = lean_ctor_get(v_a_2812_, 4);
lean_inc(v_importArts_2823_);
v_plugins_2824_ = lean_ctor_get(v_a_2812_, 5);
lean_inc_ref(v_plugins_2824_);
lean_dec(v_a_2812_);
v___x_2825_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2791_);
v___x_2826_ = l_Lean_MessageLog_empty;
v___x_2827_ = 1;
lean_inc(v_stx_2791_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_stx_2791_);
v___x_2829_ = v___x_2814_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_stx_2791_);
v___x_2829_ = v_reuseFailAlloc_3011_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_origStx_2792_);
lean_inc_ref(v___x_2829_);
lean_inc_ref(v_opts_2821_);
v___x_2831_ = l_Lean_Elab_processHeaderCore(v___x_2825_, v_imports_2820_, v_isModule_2819_, v_opts_2821_, v___x_2826_, v_toProcessingContext_2793_, v_trustLevel_2822_, v_plugins_2824_, v___x_2827_, v_mainModuleName_2817_, v_package_x3f_2818_, v_importArts_2823_, v___x_2829_, v___x_2830_);
lean_dec(v___x_2825_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_3002_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_3002_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_3002_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_fst_2836_; lean_object* v_snd_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_3001_; 
v_fst_2836_ = lean_ctor_get(v_a_2832_, 0);
v_snd_2837_ = lean_ctor_get(v_a_2832_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_a_2832_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2839_ = v_a_2832_;
v_isShared_2840_ = v_isSharedCheck_3001_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_snd_2837_);
lean_inc(v_fst_2836_);
lean_dec(v_a_2832_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_3001_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v_traceState_2859_; 
v___x_2841_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2837_);
v___x_2842_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2837_);
v___x_2843_ = l_Lean_MessageLog_hasErrors(v_snd_2837_);
if (v___x_2843_ == 0)
{
double v___x_2951_; double v___x_2952_; double v___x_2953_; double v___x_2954_; double v___x_2955_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_del_object(v___x_2806_);
lean_dec_ref(v___x_2799_);
v___x_2951_ = lean_float_of_nat(v___x_2816_);
v___x_2952_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2953_ = lean_float_div(v___x_2951_, v___x_2952_);
v___x_2954_ = lean_float_of_nat(v___x_2841_);
v___x_2955_ = lean_float_div(v___x_2954_, v___x_2952_);
v___x_2972_ = l_Lean_trace_profiler_output;
v___x_2973_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2821_, v___x_2972_);
if (lean_obj_tag(v___x_2973_) == 0)
{
if (v___x_2843_ == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2859_ = v___x_2974_;
goto v___jp_2858_;
}
else
{
goto v___jp_2956_;
}
}
else
{
lean_dec_ref(v___x_2973_);
goto v___jp_2956_;
}
v___jp_2956_:
{
uint64_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2957_ = 0ULL;
v___x_2958_ = lean_box(0);
v___x_2959_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2960_ = lean_box(0);
v___x_2961_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2962_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2962_, 0, v___x_2959_);
lean_ctor_set(v___x_2962_, 1, v___x_2960_);
lean_ctor_set(v___x_2962_, 2, v___x_2961_);
lean_ctor_set_float(v___x_2962_, sizeof(void*)*3, v___x_2953_);
lean_ctor_set_float(v___x_2962_, sizeof(void*)*3 + 8, v___x_2955_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*3 + 16, v___x_2827_);
v___x_2963_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2964_ = lean_mk_empty_array_with_capacity(v___x_2794_);
v___x_2965_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2962_);
lean_ctor_set(v___x_2965_, 1, v___x_2963_);
lean_ctor_set(v___x_2965_, 2, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2958_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_mk_empty_array_with_capacity(v___x_2967_);
v___x_2969_ = lean_array_push(v___x_2968_, v___x_2966_);
v___x_2970_ = l_Array_toPArray_x27___redArg(v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
lean_ctor_set_uint64(v___x_2971_, sizeof(void*)*1, v___x_2957_);
v_traceState_2859_ = v___x_2971_;
goto v___jp_2858_;
}
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint64_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; size_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2999_; 
lean_dec(v___x_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_snd_2837_);
lean_dec(v_fst_2836_);
lean_del_object(v___x_2834_);
lean_dec_ref(v___x_2829_);
lean_dec_ref(v_opts_2821_);
lean_dec(v___x_2816_);
lean_dec(v___x_2798_);
lean_dec_ref(v_parserState_2796_);
lean_dec_ref(v_fileMap_2795_);
lean_dec(v_stx_2791_);
v___x_2975_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2976_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2977_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2794_, 2);
v___x_2978_ = l_Lean_Name_num___override(v___x_2977_, v___x_2794_);
v___x_2979_ = l_Lean_Name_str___override(v___x_2978_, v___x_2975_);
v___x_2980_ = l_Lean_Name_str___override(v___x_2979_, v___x_2976_);
v___x_2981_ = l_Lean_Name_str___override(v___x_2980_, v___x_2975_);
v___x_2982_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2983_ = l_Lean_Name_str___override(v___x_2981_, v___x_2982_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2985_ = l_Lean_Name_str___override(v___x_2983_, v___x_2984_);
v___x_2986_ = l_Lean_Name_toString(v___x_2985_, v___x_2827_);
v___x_2987_ = lean_box(0);
v___x_2988_ = 0ULL;
v___x_2989_ = lean_unsigned_to_nat(32u);
v___x_2990_ = lean_mk_empty_array_with_capacity(v___x_2989_);
v___x_2991_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2992_ = ((size_t)5ULL);
v___x_2993_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2990_);
lean_ctor_set(v___x_2993_, 2, v___x_2794_);
lean_ctor_set(v___x_2993_, 3, v___x_2794_);
lean_ctor_set_usize(v___x_2993_, 4, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
lean_ctor_set_uint64(v___x_2994_, sizeof(void*)*1, v___x_2988_);
v___x_2995_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2995_, 0, v___x_2986_);
lean_ctor_set(v___x_2995_, 1, v___x_2842_);
lean_ctor_set(v___x_2995_, 2, v___x_2987_);
lean_ctor_set(v___x_2995_, 3, v___x_2994_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*4, v___x_2843_);
v___x_2996_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2799_);
v___x_2997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
lean_ctor_set(v___x_2997_, 2, v___x_2987_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2997_);
v___x_2999_ = v___x_2806_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
v___jp_2844_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___y_2850_);
v___x_2852_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2852_, 0, v___y_2845_);
lean_ctor_set(v___x_2852_, 1, v___x_2842_);
lean_ctor_set(v___x_2852_, 2, v___x_2851_);
lean_ctor_set(v___x_2852_, 3, v___y_2848_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*4, v___x_2843_);
v___x_2853_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2849_, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2854_, 0, v___y_2847_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
lean_ctor_set(v___x_2854_, 2, v___y_2846_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2854_);
v___x_2856_ = v___x_2834_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
v___jp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Language_Lean_reparseOptions(v_opts_2821_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_env_2867_; lean_object* v_messages_2868_; lean_object* v_scopes_2869_; lean_object* v_usedQuotCtxts_2870_; lean_object* v_nextMacroScope_2871_; lean_object* v_maxRecDepth_2872_; lean_object* v_ngen_2873_; lean_object* v_auxDeclNGen_2874_; lean_object* v_snapshotTasks_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2940_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2794_, 4);
v___x_2863_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2794_);
lean_ctor_set(v___x_2863_, 1, v___x_2794_);
lean_ctor_set(v___x_2863_, 2, v___x_2794_);
lean_ctor_set(v___x_2863_, 3, v___x_2794_);
lean_ctor_set(v___x_2863_, 4, v___x_2862_);
lean_ctor_set(v___x_2863_, 5, v___x_2862_);
lean_ctor_set(v___x_2863_, 6, v___x_2862_);
lean_ctor_set(v___x_2863_, 7, v___x_2862_);
lean_ctor_set(v___x_2863_, 8, v___x_2862_);
lean_ctor_set(v___x_2863_, 9, v___x_2862_);
v___x_2864_ = lean_io_promise_new();
v___x_2865_ = l_IO_CancelToken_new();
lean_inc(v_fst_2836_);
v___x_2866_ = l_Lean_Elab_Command_mkState(v_fst_2836_, v_snd_2837_, v_a_2861_);
v_env_2867_ = lean_ctor_get(v___x_2866_, 0);
v_messages_2868_ = lean_ctor_get(v___x_2866_, 1);
v_scopes_2869_ = lean_ctor_get(v___x_2866_, 2);
v_usedQuotCtxts_2870_ = lean_ctor_get(v___x_2866_, 3);
v_nextMacroScope_2871_ = lean_ctor_get(v___x_2866_, 4);
v_maxRecDepth_2872_ = lean_ctor_get(v___x_2866_, 5);
v_ngen_2873_ = lean_ctor_get(v___x_2866_, 6);
v_auxDeclNGen_2874_ = lean_ctor_get(v___x_2866_, 7);
v_snapshotTasks_2875_ = lean_ctor_get(v___x_2866_, 10);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; lean_object* v_unused_2942_; 
v_unused_2941_ = lean_ctor_get(v___x_2866_, 9);
lean_dec(v_unused_2941_);
v_unused_2942_ = lean_ctor_get(v___x_2866_, 8);
lean_dec(v_unused_2942_);
v___x_2877_ = v___x_2866_;
v_isShared_2878_ = v_isSharedCheck_2940_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_snapshotTasks_2875_);
lean_inc(v_auxDeclNGen_2874_);
lean_inc(v_ngen_2873_);
lean_inc(v_maxRecDepth_2872_);
lean_inc(v_nextMacroScope_2871_);
lean_inc(v_usedQuotCtxts_2870_);
lean_inc(v_scopes_2869_);
lean_inc(v_messages_2868_);
lean_inc(v_env_2867_);
lean_dec(v___x_2866_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2940_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = l_Lean_Options_empty;
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2885_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2885_, 0, v_fst_2836_);
lean_ctor_set(v___x_2885_, 1, v___x_2879_);
lean_ctor_set(v___x_2885_, 2, v_fileMap_2795_);
lean_ctor_set(v___x_2885_, 3, v___x_2863_);
lean_ctor_set(v___x_2885_, 4, v___x_2880_);
lean_ctor_set(v___x_2885_, 5, v___x_2881_);
lean_ctor_set(v___x_2885_, 6, v___x_2882_);
lean_ctor_set(v___x_2885_, 7, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
v___x_2887_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2791_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_stx_2791_);
lean_ctor_set(v___x_2839_, 0, v___x_2887_);
v___x_2889_ = v___x_2839_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_stx_2791_);
v___x_2889_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2890_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
v___x_2891_ = lean_unsigned_to_nat(2u);
v___x_2892_ = l_Lean_Syntax_getArg(v_stx_2791_, v___x_2891_);
lean_dec(v_stx_2791_);
v___x_2893_ = l_Lean_Syntax_getArgs(v___x_2892_);
lean_dec(v___x_2892_);
v___x_2894_ = lean_array_to_list(v___x_2893_);
v___x_2895_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2894_, v___x_2882_);
v___x_2896_ = l_List_toPArray_x27___redArg(v___x_2895_);
v___x_2897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2890_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2886_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2900_ = lean_array_push(v___x_2899_, v___x_2898_);
v___x_2901_ = l_Array_toPArray_x27___redArg(v___x_2900_);
lean_dec_ref(v___x_2900_);
lean_inc_ref(v___x_2901_);
v___x_2902_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2902_, 0, v___x_2862_);
lean_ctor_set(v___x_2902_, 1, v___x_2862_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
lean_ctor_set_uint8(v___x_2902_, sizeof(void*)*3, v___x_2827_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 9, v_traceState_2859_);
lean_ctor_set(v___x_2877_, 8, v___x_2902_);
v___x_2904_ = v___x_2877_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_env_2867_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_messages_2868_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_scopes_2869_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_usedQuotCtxts_2870_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_nextMacroScope_2871_);
lean_ctor_set(v_reuseFailAlloc_2938_, 5, v_maxRecDepth_2872_);
lean_ctor_set(v_reuseFailAlloc_2938_, 6, v_ngen_2873_);
lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_auxDeclNGen_2874_);
lean_ctor_set(v_reuseFailAlloc_2938_, 8, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2938_, 9, v_traceState_2859_);
lean_ctor_set(v_reuseFailAlloc_2938_, 10, v_snapshotTasks_2875_);
v___x_2904_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; size_t v___x_2913_; lean_object* v___x_2914_; lean_object* v_size_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint64_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
lean_inc(v___x_2865_);
lean_inc(v___x_2864_);
lean_inc_ref(v___x_2904_);
v___x_2905_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2879_, v_parserState_2796_, v___x_2904_, v___x_2864_, v___x_2827_, v___x_2865_, v_a_2797_);
v___x_2906_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2907_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2908_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2794_, 3);
v___x_2909_ = l_Lean_Name_num___override(v___x_2908_, v___x_2794_);
v___x_2910_ = lean_unsigned_to_nat(32u);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2910_);
v___x_2912_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2913_ = ((size_t)5ULL);
v___x_2914_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2911_);
lean_ctor_set(v___x_2914_, 2, v___x_2794_);
lean_ctor_set(v___x_2914_, 3, v___x_2794_);
lean_ctor_set_usize(v___x_2914_, 4, v___x_2913_);
v_size_2915_ = lean_ctor_get(v___x_2901_, 2);
lean_inc(v_size_2915_);
v___x_2916_ = l_Lean_Name_str___override(v___x_2909_, v___x_2906_);
v___x_2917_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2798_);
v___x_2918_ = l_Lean_Name_str___override(v___x_2916_, v___x_2907_);
v___x_2919_ = l_Lean_Name_str___override(v___x_2918_, v___x_2906_);
v___x_2920_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2921_ = l_Lean_Name_str___override(v___x_2919_, v___x_2920_);
v___x_2922_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2923_ = l_Lean_Name_str___override(v___x_2921_, v___x_2922_);
v___x_2924_ = l_Lean_Name_toString(v___x_2923_, v___x_2827_);
v___x_2925_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2926_ = 0ULL;
v___x_2927_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2927_, 0, v___x_2914_);
lean_ctor_set_uint64(v___x_2927_, sizeof(void*)*1, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2865_);
v___x_2929_ = l_IO_Promise_result_x21___redArg(v___x_2864_);
lean_dec(v___x_2864_);
v___x_2930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2798_);
lean_ctor_set(v___x_2930_, 1, v___x_2917_);
lean_ctor_set(v___x_2930_, 2, v___x_2928_);
lean_ctor_set(v___x_2930_, 3, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2904_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_inc_ref(v___x_2927_);
lean_inc_ref(v___x_2924_);
v___x_2933_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2933_, 0, v___x_2924_);
lean_ctor_set(v___x_2933_, 1, v___x_2925_);
lean_ctor_set(v___x_2933_, 2, v___x_2879_);
lean_ctor_set(v___x_2933_, 3, v___x_2927_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*4, v___x_2843_);
v___x_2934_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2935_ = lean_nat_dec_lt(v___x_2794_, v_size_2915_);
lean_dec(v_size_2915_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref(v___x_2901_);
lean_dec(v___x_2794_);
v___x_2936_ = l_outOfBounds___redArg(v___x_2934_);
v___y_2845_ = v___x_2924_;
v___y_2846_ = v___x_2932_;
v___y_2847_ = v___x_2933_;
v___y_2848_ = v___x_2927_;
v___y_2849_ = v___x_2829_;
v___y_2850_ = v___x_2936_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2934_, v___x_2901_, v___x_2794_);
lean_dec(v___x_2794_);
lean_dec_ref(v___x_2901_);
v___y_2845_ = v___x_2924_;
v___y_2846_ = v___x_2932_;
v___y_2847_ = v___x_2933_;
v___y_2848_ = v___x_2927_;
v___y_2849_ = v___x_2829_;
v___y_2850_ = v___x_2937_;
goto v___jp_2844_;
}
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_traceState_2859_);
lean_dec_ref(v___x_2842_);
lean_del_object(v___x_2839_);
lean_dec(v_snd_2837_);
lean_dec(v_fst_2836_);
lean_del_object(v___x_2834_);
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2798_);
lean_dec_ref(v_parserState_2796_);
lean_dec_ref(v_fileMap_2795_);
lean_dec(v___x_2794_);
lean_dec(v_stx_2791_);
v_a_2943_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2860_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2860_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v___x_2829_);
lean_dec_ref(v_opts_2821_);
lean_dec(v___x_2816_);
lean_del_object(v___x_2806_);
lean_dec_ref(v___x_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v_parserState_2796_);
lean_dec_ref(v_fileMap_2795_);
lean_dec(v___x_2794_);
lean_dec(v_stx_2791_);
v_a_3003_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2831_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2831_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
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
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v___x_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v_parserState_2796_);
lean_dec_ref(v_fileMap_2795_);
lean_dec(v___x_2794_);
lean_dec_ref(v_toProcessingContext_2793_);
lean_dec(v_origStx_2792_);
lean_dec(v_stx_2791_);
v_a_3014_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2803_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2803_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3022_, lean_object* v_stx_3023_, lean_object* v_origStx_3024_, lean_object* v_toProcessingContext_3025_, lean_object* v___x_3026_, lean_object* v_fileMap_3027_, lean_object* v_parserState_3028_, lean_object* v_a_3029_, lean_object* v___x_3030_, lean_object* v___x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3022_, v_stx_3023_, v_origStx_3024_, v_toProcessingContext_3025_, v___x_3026_, v_fileMap_3027_, v_parserState_3028_, v_a_3029_, v___x_3030_, v___x_3031_, v___y_3032_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v_a_3029_);
return v_res_3034_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___f_3036_; 
v___x_3035_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3036_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3036_, 0, v___x_3035_);
return v___f_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3037_, lean_object* v_stx_3038_, lean_object* v_origStx_3039_, lean_object* v_parserState_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_toProcessingContext_3043_; lean_object* v_fileMap_3044_; lean_object* v_endPos_3045_; lean_object* v___x_3046_; lean_object* v___f_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___f_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v_toProcessingContext_3043_ = lean_ctor_get(v_a_3041_, 0);
v_fileMap_3044_ = lean_ctor_get(v_toProcessingContext_3043_, 2);
v_endPos_3045_ = lean_ctor_get(v_toProcessingContext_3043_, 3);
v___x_3046_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3047_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3048_ = lean_box(0);
v___x_3049_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3041_, 2);
lean_inc_ref(v_fileMap_3044_);
lean_inc_ref(v_toProcessingContext_3043_);
v___f_3050_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3050_, 0, v_setupImports_3037_);
lean_closure_set(v___f_3050_, 1, v_stx_3038_);
lean_closure_set(v___f_3050_, 2, v_origStx_3039_);
lean_closure_set(v___f_3050_, 3, v_toProcessingContext_3043_);
lean_closure_set(v___f_3050_, 4, v___x_3049_);
lean_closure_set(v___f_3050_, 5, v_fileMap_3044_);
lean_closure_set(v___f_3050_, 6, v_parserState_3040_);
lean_closure_set(v___f_3050_, 7, v_a_3041_);
lean_closure_set(v___f_3050_, 8, v___x_3048_);
lean_closure_set(v___f_3050_, 9, v___x_3046_);
lean_inc(v_endPos_3045_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v_endPos_3045_);
v___x_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
v___x_3053_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3053_, 0, lean_box(0));
lean_closure_set(v___x_3053_, 1, v___f_3047_);
lean_closure_set(v___x_3053_, 2, v___f_3050_);
lean_closure_set(v___x_3053_, 3, v_a_3041_);
v___x_3054_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3048_, v___x_3048_, v___x_3052_, v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3055_, lean_object* v_stx_3056_, lean_object* v_origStx_3057_, lean_object* v_parserState_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3055_, v_stx_3056_, v_origStx_3057_, v_parserState_3058_, v_a_3059_);
lean_dec_ref(v_a_3059_);
return v_res_3061_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_box(0);
v___x_3063_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = 1;
v___x_3069_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3070_ = l_Lean_Name_toString(v___x_3069_, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3071_ = 0;
v___x_3072_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3073_ = lean_box(0);
v___x_3074_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3075_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3076_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3074_);
lean_ctor_set(v___x_3076_, 2, v___x_3073_);
lean_ctor_set(v___x_3076_, 3, v___x_3072_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*4, v___x_3071_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3077_, lean_object* v_cmdState_3078_, lean_object* v_a_3079_, lean_object* v_toSnapshot_3080_, lean_object* v_newStx_3081_, lean_object* v_oldCmd_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; lean_object* v_diagnostics_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3111_; 
v___x_3084_ = lean_io_promise_new();
v___x_3085_ = l_IO_CancelToken_new();
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_oldCmd_3082_);
v___x_3087_ = 1;
lean_inc(v___x_3085_);
lean_inc(v___x_3084_);
lean_inc_ref(v_cmdState_3078_);
v___x_3088_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3086_, v_newParserState_3077_, v_cmdState_3078_, v___x_3084_, v___x_3087_, v___x_3085_, v_a_3079_);
v_diagnostics_3089_ = lean_ctor_get(v_toSnapshot_3080_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_toSnapshot_3080_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; 
v_unused_3112_ = lean_ctor_get(v_toSnapshot_3080_, 3);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_toSnapshot_3080_, 2);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_toSnapshot_3080_, 0);
lean_dec(v_unused_3114_);
v___x_3091_ = v_toSnapshot_3080_;
v_isShared_3092_ = v_isSharedCheck_3111_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_diagnostics_3089_);
lean_dec(v_toSnapshot_3080_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3111_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3095_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3096_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3085_);
v___x_3098_ = l_IO_Promise_result_x21___redArg(v___x_3084_);
lean_dec(v___x_3084_);
v___x_3099_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3093_);
lean_ctor_set(v___x_3099_, 1, v___x_3094_);
lean_ctor_set(v___x_3099_, 2, v___x_3097_);
lean_ctor_set(v___x_3099_, 3, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_cmdState_3078_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
v___x_3102_ = 0;
v___x_3103_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_newStx_3081_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 3, v___x_3096_);
lean_ctor_set(v___x_3091_, 2, v___x_3093_);
lean_ctor_set(v___x_3091_, 0, v___x_3095_);
v___x_3106_ = v___x_3091_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_diagnostics_3089_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v___x_3096_);
v___x_3106_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*4, v___x_3102_);
v___x_3107_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3104_, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3103_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
lean_ctor_set(v___x_3108_, 2, v___x_3101_);
v___x_3109_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3093_, v___x_3108_);
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3115_, lean_object* v_cmdState_3116_, lean_object* v_a_3117_, lean_object* v_toSnapshot_3118_, lean_object* v_newStx_3119_, lean_object* v_oldCmd_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3115_, v_cmdState_3116_, v_a_3117_, v_toSnapshot_3118_, v_newStx_3119_, v_oldCmd_3120_);
lean_dec_ref(v_a_3117_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3123_, lean_object* v_a_3124_, lean_object* v_newStx_3125_, lean_object* v___x_3126_, lean_object* v_oldProcessed_3127_){
_start:
{
lean_object* v_result_x3f_3129_; 
v_result_x3f_3129_ = lean_ctor_get(v_oldProcessed_3127_, 2);
if (lean_obj_tag(v_result_x3f_3129_) == 1)
{
lean_object* v_val_3130_; lean_object* v_firstCmdSnap_3131_; lean_object* v_toSnapshot_3132_; lean_object* v_cmdState_3133_; lean_object* v_stx_x3f_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; 
v_val_3130_ = lean_ctor_get(v_result_x3f_3129_, 0);
lean_inc(v_val_3130_);
v_firstCmdSnap_3131_ = lean_ctor_get(v_val_3130_, 1);
lean_inc_ref(v_firstCmdSnap_3131_);
v_toSnapshot_3132_ = lean_ctor_get(v_oldProcessed_3127_, 0);
lean_inc_ref(v_toSnapshot_3132_);
lean_dec_ref(v_oldProcessed_3127_);
v_cmdState_3133_ = lean_ctor_get(v_val_3130_, 0);
lean_inc_ref(v_cmdState_3133_);
lean_dec(v_val_3130_);
v_stx_x3f_3134_ = lean_ctor_get(v_firstCmdSnap_3131_, 0);
lean_inc(v_stx_x3f_3134_);
lean_inc_ref(v_a_3124_);
v___f_3135_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3135_, 0, v_newParserState_3123_);
lean_closure_set(v___f_3135_, 1, v_cmdState_3133_);
lean_closure_set(v___f_3135_, 2, v_a_3124_);
lean_closure_set(v___f_3135_, 3, v_toSnapshot_3132_);
lean_closure_set(v___f_3135_, 4, v_newStx_3125_);
v___x_3136_ = lean_box(0);
v___x_3137_ = 1;
v___x_3138_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3131_, v___f_3135_, v_stx_x3f_3134_, v___x_3126_, v___x_3136_, v___x_3137_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec(v___x_3126_);
lean_dec_ref(v_newParserState_3123_);
v___x_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3139_, 0, v_newStx_3125_);
v___x_3140_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3139_, v_oldProcessed_3127_);
return v___x_3140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3141_, lean_object* v_a_3142_, lean_object* v_newStx_3143_, lean_object* v___x_3144_, lean_object* v_oldProcessed_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3141_, v_a_3142_, v_newStx_3143_, v___x_3144_, v_oldProcessed_3145_);
lean_dec_ref(v_a_3142_);
return v_res_3147_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3148_ = 0;
v___x_3149_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3150_ = lean_box(0);
v___x_3151_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3152_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3153_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v___x_3151_);
lean_ctor_set(v___x_3153_, 2, v___x_3150_);
lean_ctor_set(v___x_3153_, 3, v___x_3149_);
lean_ctor_set_uint8(v___x_3153_, sizeof(void*)*4, v___x_3148_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3154_, lean_object* v_a_3155_, lean_object* v_old_3156_, lean_object* v_newStx_3157_, lean_object* v_newParserState_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_result_x3f_3161_; 
v_result_x3f_3161_ = lean_ctor_get(v_old_3156_, 4);
lean_inc(v_result_x3f_3161_);
if (lean_obj_tag(v_result_x3f_3161_) == 1)
{
lean_object* v_val_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3216_; 
v_val_3162_ = lean_ctor_get(v_result_x3f_3161_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_result_x3f_3161_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3164_ = v_result_x3f_3161_;
v_isShared_3165_ = v_isSharedCheck_3216_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_val_3162_);
lean_dec(v_result_x3f_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3216_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v_processedSnap_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3214_; 
v_processedSnap_3166_ = lean_ctor_get(v_val_3162_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_val_3162_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v_val_3162_, 0);
lean_dec(v_unused_3215_);
v___x_3168_ = v_val_3162_;
v_isShared_3169_ = v_isSharedCheck_3214_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_processedSnap_3166_);
lean_dec(v_val_3162_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3214_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v_toSnapshot_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3209_; 
v_toSnapshot_3170_ = lean_ctor_get(v_old_3156_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_old_3156_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; lean_object* v_unused_3211_; lean_object* v_unused_3212_; lean_object* v_unused_3213_; 
v_unused_3210_ = lean_ctor_get(v_old_3156_, 4);
lean_dec(v_unused_3210_);
v_unused_3211_ = lean_ctor_get(v_old_3156_, 3);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v_old_3156_, 2);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_old_3156_, 1);
lean_dec(v_unused_3213_);
v___x_3172_ = v_old_3156_;
v_isShared_3173_ = v_isSharedCheck_3209_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_toSnapshot_3170_);
lean_dec(v_old_3156_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3209_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_pos_3174_; lean_object* v_endPos_3175_; lean_object* v_stx_x3f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___f_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; lean_object* v___x_3182_; lean_object* v_diagnostics_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3205_; 
v_pos_3174_ = lean_ctor_get(v_newParserState_3158_, 0);
v_endPos_3175_ = lean_ctor_get(v_toProcessingContext_3154_, 3);
v_stx_x3f_3176_ = lean_ctor_get(v_processedSnap_3166_, 0);
lean_inc(v_stx_x3f_3176_);
lean_inc(v_endPos_3175_);
lean_inc(v_pos_3174_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_pos_3174_);
lean_ctor_set(v___x_3177_, 1, v_endPos_3175_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_inc_ref(v___x_3178_);
lean_inc(v_newStx_3157_);
lean_inc_ref(v_a_3155_);
lean_inc_ref(v_newParserState_3158_);
v___f_3179_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3179_, 0, v_newParserState_3158_);
lean_closure_set(v___f_3179_, 1, v_a_3155_);
lean_closure_set(v___f_3179_, 2, v_newStx_3157_);
lean_closure_set(v___f_3179_, 3, v___x_3178_);
v___x_3180_ = lean_box(0);
v___x_3181_ = 1;
v___x_3182_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3166_, v___f_3179_, v_stx_x3f_3176_, v___x_3178_, v___x_3180_, v___x_3181_);
v_diagnostics_3183_ = lean_ctor_get(v_toSnapshot_3170_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_toSnapshot_3170_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; lean_object* v_unused_3208_; 
v_unused_3206_ = lean_ctor_get(v_toSnapshot_3170_, 3);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_toSnapshot_3170_, 2);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_toSnapshot_3170_, 0);
lean_dec(v_unused_3208_);
v___x_3185_ = v_toSnapshot_3170_;
v_isShared_3186_ = v_isSharedCheck_3205_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_diagnostics_3183_);
lean_dec(v_toSnapshot_3170_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3205_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3187_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3188_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3182_);
lean_ctor_set(v___x_3168_, 0, v_newParserState_3158_);
v___x_3190_ = v___x_3168_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_newParserState_3158_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3182_);
v___x_3190_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3192_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3190_);
v___x_3192_ = v___x_3164_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
uint8_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3193_ = 0;
v___x_3194_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3157_);
v___x_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_newStx_3157_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 3, v___x_3188_);
lean_ctor_set(v___x_3185_, 2, v___x_3180_);
lean_ctor_set(v___x_3185_, 0, v___x_3187_);
v___x_3197_ = v___x_3185_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_diagnostics_3183_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v___x_3188_);
v___x_3197_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*4, v___x_3193_);
v___x_3198_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3195_, v___x_3197_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3192_);
lean_ctor_set(v___x_3172_, 3, v_newStx_3157_);
lean_ctor_set(v___x_3172_, 2, v_toProcessingContext_3154_);
lean_ctor_set(v___x_3172_, 1, v___x_3198_);
lean_ctor_set(v___x_3172_, 0, v___x_3194_);
v___x_3200_ = v___x_3172_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_toProcessingContext_3154_);
lean_ctor_set(v_reuseFailAlloc_3201_, 3, v_newStx_3157_);
lean_ctor_set(v_reuseFailAlloc_3201_, 4, v___x_3192_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
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
lean_dec(v_result_x3f_3161_);
lean_dec_ref(v_newParserState_3158_);
lean_dec(v_newStx_3157_);
lean_dec_ref(v_toProcessingContext_3154_);
return v_old_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3217_, lean_object* v_a_3218_, lean_object* v_old_3219_, lean_object* v_newStx_3220_, lean_object* v_newParserState_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3217_, v_a_3218_, v_old_3219_, v_newStx_3220_, v_newParserState_3221_, v___y_3222_);
lean_dec_ref(v___y_3222_);
lean_dec_ref(v_a_3218_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3225_, lean_object* v_setupImports_3226_, lean_object* v_old_x3f_3227_, lean_object* v___f_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
lean_inc_ref(v_toProcessingContext_3225_);
v___x_3231_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3225_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3301_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3301_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3301_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_snd_3236_; lean_object* v_fst_3237_; lean_object* v_fst_3238_; lean_object* v_snd_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3300_; 
v_snd_3236_ = lean_ctor_get(v_a_3232_, 1);
lean_inc(v_snd_3236_);
v_fst_3237_ = lean_ctor_get(v_a_3232_, 0);
lean_inc(v_fst_3237_);
lean_dec(v_a_3232_);
v_fst_3238_ = lean_ctor_get(v_snd_3236_, 0);
v_snd_3239_ = lean_ctor_get(v_snd_3236_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_snd_3236_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3241_ = v_snd_3236_;
v_isShared_3242_ = v_isSharedCheck_3300_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_snd_3239_);
lean_inc(v_fst_3238_);
lean_dec(v_snd_3236_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3300_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
uint8_t v___x_3243_; 
v___x_3243_ = l_Lean_MessageLog_hasErrors(v_snd_3239_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___y_3246_; 
lean_inc(v_fst_3237_);
v___x_3244_ = l_Lean_Syntax_unsetTrailing(v_fst_3237_);
if (lean_obj_tag(v_old_x3f_3227_) == 1)
{
lean_object* v_val_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3283_; 
v_val_3267_ = lean_ctor_get(v_old_x3f_3227_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_old_x3f_3227_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3269_ = v_old_x3f_3227_;
v_isShared_3270_ = v_isSharedCheck_3283_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_val_3267_);
lean_dec(v_old_x3f_3227_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3283_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v_stx_3271_; lean_object* v_result_x3f_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_stx_3271_ = lean_ctor_get(v_val_3267_, 3);
v_result_x3f_3272_ = lean_ctor_get(v_val_3267_, 4);
lean_inc(v_stx_3271_);
v___x_3273_ = l_Lean_Syntax_unsetTrailing(v_stx_3271_);
lean_inc(v___x_3244_);
v___x_3274_ = l_Lean_Syntax_eqWithInfo(v___x_3244_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_inc(v_result_x3f_3272_);
lean_del_object(v___x_3269_);
lean_dec(v_val_3267_);
lean_dec_ref(v___f_3228_);
if (lean_obj_tag(v_result_x3f_3272_) == 0)
{
v___y_3246_ = v___y_3229_;
goto v___jp_3245_;
}
else
{
lean_object* v_val_3275_; lean_object* v_processedSnap_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_val_3275_ = lean_ctor_get(v_result_x3f_3272_, 0);
lean_inc(v_val_3275_);
lean_dec_ref(v_result_x3f_3272_);
v_processedSnap_3276_ = lean_ctor_get(v_val_3275_, 1);
lean_inc_ref(v_processedSnap_3276_);
lean_dec(v_val_3275_);
v___x_3277_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3278_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3277_, v_processedSnap_3276_);
v___y_3246_ = v___y_3229_;
goto v___jp_3245_;
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_dec(v___x_3244_);
lean_del_object(v___x_3241_);
lean_dec(v_snd_3239_);
lean_del_object(v___x_3234_);
lean_dec_ref(v_setupImports_3226_);
lean_dec_ref(v_toProcessingContext_3225_);
lean_inc_ref(v___y_3229_);
v___x_3279_ = lean_apply_5(v___f_3228_, v_val_3267_, v_fst_3237_, v_fst_3238_, v___y_3229_, lean_box(0));
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3279_);
v___x_3281_ = v___x_3269_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
else
{
lean_dec_ref(v___f_3228_);
lean_dec(v_old_x3f_3227_);
v___y_3246_ = v___y_3229_;
goto v___jp_3245_;
}
v___jp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3247_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3239_);
lean_inc(v_fst_3238_);
lean_inc(v_fst_3237_);
v___x_3248_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3226_, v___x_3244_, v_fst_3237_, v_fst_3238_, v___y_3246_);
v___x_3249_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3250_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3251_ = lean_box(0);
v___x_3252_ = lean_unsigned_to_nat(32u);
v___x_3253_ = lean_mk_empty_array_with_capacity(v___x_3252_);
lean_dec_ref(v___x_3253_);
v___x_3254_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v___x_3248_);
v___x_3256_ = v___x_3241_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_fst_3238_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3248_);
v___x_3256_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3258_, 0, v___x_3249_);
lean_ctor_set(v___x_3258_, 1, v___x_3250_);
lean_ctor_set(v___x_3258_, 2, v___x_3251_);
lean_ctor_set(v___x_3258_, 3, v___x_3254_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*4, v___x_3243_);
lean_inc(v_fst_3237_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_fst_3237_);
v___x_3260_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3260_, 0, v___x_3249_);
lean_ctor_set(v___x_3260_, 1, v___x_3247_);
lean_ctor_set(v___x_3260_, 2, v___x_3251_);
lean_ctor_set(v___x_3260_, 3, v___x_3254_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*4, v___x_3243_);
v___x_3261_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3259_, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3258_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
lean_ctor_set(v___x_3262_, 2, v_toProcessingContext_3225_);
lean_ctor_set(v___x_3262_, 3, v_fst_3237_);
lean_ctor_set(v___x_3262_, 4, v___x_3257_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3262_);
v___x_3264_ = v___x_3234_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
lean_del_object(v___x_3241_);
lean_dec(v_fst_3238_);
lean_dec_ref(v___f_3228_);
lean_dec(v_old_x3f_3227_);
lean_dec_ref(v_setupImports_3226_);
v___x_3284_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3239_);
v___x_3285_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3286_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_unsigned_to_nat(32u);
v___x_3289_ = lean_mk_empty_array_with_capacity(v___x_3288_);
lean_dec_ref(v___x_3289_);
v___x_3290_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3291_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3291_, 0, v___x_3285_);
lean_ctor_set(v___x_3291_, 1, v___x_3286_);
lean_ctor_set(v___x_3291_, 2, v___x_3287_);
lean_ctor_set(v___x_3291_, 3, v___x_3290_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*4, v___x_3243_);
lean_inc(v_fst_3237_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v_fst_3237_);
v___x_3293_ = 0;
v___x_3294_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3294_, 0, v___x_3285_);
lean_ctor_set(v___x_3294_, 1, v___x_3284_);
lean_ctor_set(v___x_3294_, 2, v___x_3287_);
lean_ctor_set(v___x_3294_, 3, v___x_3290_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*4, v___x_3293_);
v___x_3295_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3292_, v___x_3294_);
v___x_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3291_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
lean_ctor_set(v___x_3296_, 2, v_toProcessingContext_3225_);
lean_ctor_set(v___x_3296_, 3, v_fst_3237_);
lean_ctor_set(v___x_3296_, 4, v___x_3287_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3296_);
v___x_3298_ = v___x_3234_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v___f_3228_);
lean_dec(v_old_x3f_3227_);
lean_dec_ref(v_setupImports_3226_);
lean_dec_ref(v_toProcessingContext_3225_);
v_a_3302_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3231_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3231_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3310_, lean_object* v_setupImports_3311_, lean_object* v_old_x3f_3312_, lean_object* v___f_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3310_, v_setupImports_3311_, v_old_x3f_3312_, v___f_3313_, v___y_3314_);
lean_dec_ref(v___y_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3317_, lean_object* v_toProcessingContext_3318_, lean_object* v_x_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3320_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3317_);
v___x_3321_ = lean_box(0);
v___x_3322_ = lean_box(0);
v___x_3323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3323_, 0, v_x_3319_);
lean_ctor_set(v___x_3323_, 1, v___x_3320_);
lean_ctor_set(v___x_3323_, 2, v_toProcessingContext_3318_);
lean_ctor_set(v___x_3323_, 3, v___x_3321_);
lean_ctor_set(v___x_3323_, 4, v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3324_, lean_object* v_old_x3f_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_toProcessingContext_3328_; lean_object* v___x_3329_; lean_object* v___f_3330_; lean_object* v___f_3331_; lean_object* v___f_3332_; 
v_toProcessingContext_3328_ = lean_ctor_get(v_a_3326_, 0);
v___x_3329_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3326_);
lean_inc_ref_n(v_toProcessingContext_3328_, 3);
v___f_3330_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3330_, 0, v_toProcessingContext_3328_);
lean_closure_set(v___f_3330_, 1, v_a_3326_);
lean_inc(v_old_x3f_3325_);
v___f_3331_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3331_, 0, v_toProcessingContext_3328_);
lean_closure_set(v___f_3331_, 1, v_setupImports_3324_);
lean_closure_set(v___f_3331_, 2, v_old_x3f_3325_);
lean_closure_set(v___f_3331_, 3, v___f_3330_);
v___f_3332_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3332_, 0, v___x_3329_);
lean_closure_set(v___f_3332_, 1, v_toProcessingContext_3328_);
if (lean_obj_tag(v_old_x3f_3325_) == 1)
{
lean_object* v_val_3333_; lean_object* v_result_x3f_3334_; 
v_val_3333_ = lean_ctor_get(v_old_x3f_3325_, 0);
lean_inc(v_val_3333_);
lean_dec_ref(v_old_x3f_3325_);
v_result_x3f_3334_ = lean_ctor_get(v_val_3333_, 4);
if (lean_obj_tag(v_result_x3f_3334_) == 1)
{
lean_object* v_stx_3335_; lean_object* v_val_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_stx_3335_ = lean_ctor_get(v_val_3333_, 3);
lean_inc(v_stx_3335_);
v_val_3336_ = lean_ctor_get(v_result_x3f_3334_, 0);
lean_inc(v_val_3333_);
v___x_3337_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3333_);
v___x_3338_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 1)
{
lean_object* v_val_3339_; 
v_val_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v___x_3338_);
if (lean_obj_tag(v_val_3339_) == 1)
{
lean_object* v_val_3340_; lean_object* v_firstCmdSnap_3341_; lean_object* v___x_3342_; 
v_val_3340_ = lean_ctor_get(v_val_3339_, 0);
lean_inc(v_val_3340_);
lean_dec_ref(v_val_3339_);
v_firstCmdSnap_3341_ = lean_ctor_get(v_val_3340_, 1);
lean_inc_ref(v_firstCmdSnap_3341_);
lean_dec(v_val_3340_);
v___x_3342_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3341_);
if (lean_obj_tag(v___x_3342_) == 1)
{
lean_object* v_val_3343_; lean_object* v_nextCmdSnap_x3f_3344_; 
v_val_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_val_3343_);
lean_dec_ref(v___x_3342_);
v_nextCmdSnap_x3f_3344_ = lean_ctor_get(v_val_3343_, 4);
lean_inc(v_nextCmdSnap_x3f_3344_);
lean_dec(v_val_3343_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3344_) == 0)
{
lean_object* v___x_3345_; 
lean_dec(v_stx_3335_);
lean_dec(v_val_3333_);
v___x_3345_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3345_;
}
else
{
lean_object* v_val_3346_; lean_object* v___x_3347_; 
v_val_3346_ = lean_ctor_get(v_nextCmdSnap_x3f_3344_, 0);
lean_inc(v_val_3346_);
lean_dec_ref(v_nextCmdSnap_x3f_3344_);
v___x_3347_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3346_);
if (lean_obj_tag(v___x_3347_) == 1)
{
lean_object* v_val_3348_; lean_object* v_parserState_3349_; lean_object* v_pos_3350_; uint8_t v___x_3351_; 
v_val_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_val_3348_);
lean_dec_ref(v___x_3347_);
v_parserState_3349_ = lean_ctor_get(v_val_3348_, 2);
lean_inc_ref(v_parserState_3349_);
lean_dec(v_val_3348_);
v_pos_3350_ = lean_ctor_get(v_parserState_3349_, 0);
lean_inc(v_pos_3350_);
lean_dec_ref(v_parserState_3349_);
v___x_3351_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3350_, v_a_3326_);
lean_dec(v_pos_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec(v_stx_3335_);
lean_dec(v_val_3333_);
v___x_3352_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3352_;
}
else
{
lean_object* v_parserState_3353_; lean_object* v___x_3354_; 
lean_dec_ref(v___f_3332_);
lean_dec_ref(v___f_3331_);
v_parserState_3353_ = lean_ctor_get(v_val_3336_, 0);
lean_inc_ref(v_parserState_3353_);
lean_inc_ref(v_toProcessingContext_3328_);
v___x_3354_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3328_, v_a_3326_, v_val_3333_, v_stx_3335_, v_parserState_3353_, v_a_3326_);
return v___x_3354_;
}
}
else
{
lean_object* v___x_3355_; 
lean_dec(v___x_3347_);
lean_dec(v_stx_3335_);
lean_dec(v_val_3333_);
v___x_3355_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3355_;
}
}
}
else
{
lean_object* v___x_3356_; 
lean_dec(v___x_3342_);
lean_dec(v_stx_3335_);
lean_dec(v_val_3333_);
v___x_3356_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3356_;
}
}
else
{
lean_object* v___x_3357_; 
lean_dec(v_val_3339_);
lean_dec(v_stx_3335_);
lean_dec(v_val_3333_);
v___x_3357_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3357_;
}
}
else
{
lean_object* v___x_3358_; 
lean_dec(v___x_3338_);
lean_dec(v_stx_3335_);
lean_dec(v_val_3333_);
v___x_3358_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3358_;
}
}
else
{
lean_object* v___x_3359_; 
lean_dec(v_val_3333_);
v___x_3359_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3359_;
}
}
else
{
lean_object* v___x_3360_; 
lean_dec(v_old_x3f_3325_);
v___x_3360_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3332_, v___f_3331_, v_a_3326_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3361_, lean_object* v_old_x3f_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3361_, v_old_x3f_3362_, v_a_3363_);
lean_dec_ref(v_a_3363_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3366_, lean_object* v_old_x3f_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v___x_3370_; 
lean_inc(v_old_x3f_3367_);
v___x_3370_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3370_, 0, v_setupImports_3366_);
lean_closure_set(v___x_3370_, 1, v_old_x3f_3367_);
if (lean_obj_tag(v_old_x3f_3367_) == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_box(0);
v___x_3372_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3370_, v___x_3371_, v_a_3368_);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3382_; 
v_val_3373_ = lean_ctor_get(v_old_x3f_3367_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_old_x3f_3367_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3375_ = v_old_x3f_3367_;
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v_old_x3f_3367_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_ictx_3377_; lean_object* v___x_3379_; 
v_ictx_3377_ = lean_ctor_get(v_val_3373_, 2);
lean_inc_ref(v_ictx_3377_);
lean_dec(v_val_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v_ictx_3377_);
v___x_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_ictx_3377_);
v___x_3379_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3370_, v___x_3379_, v_a_3368_);
return v___x_3380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3383_, lean_object* v_old_x3f_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Language_Lean_process(v_setupImports_3383_, v_old_x3f_3384_, v_a_3385_);
lean_dec_ref(v_a_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3388_, lean_object* v_parserState_3389_, lean_object* v_commandState_3390_, lean_object* v_old_x3f_3391_){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3401_; 
v___x_3393_ = lean_io_promise_new();
v___x_3394_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3391_) == 0)
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_box(0);
v___y_3401_ = v___x_3415_;
goto v___jp_3400_;
}
else
{
lean_object* v_val_3416_; lean_object* v_snd_3417_; lean_object* v___x_3418_; 
v_val_3416_ = lean_ctor_get(v_old_x3f_3391_, 0);
v_snd_3417_ = lean_ctor_get(v_val_3416_, 1);
lean_inc(v_snd_3417_);
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_snd_3417_);
v___y_3401_ = v___x_3418_;
goto v___jp_3400_;
}
v___jp_3395_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3396_, v___y_3397_, v_inputCtx_3388_);
lean_dec(v___x_3398_);
v___x_3399_ = l_IO_Promise_result_x21___redArg(v___x_3393_);
lean_dec(v___x_3393_);
return v___x_3399_;
}
v___jp_3400_:
{
uint8_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = 1;
v___x_3403_ = lean_box(v___x_3402_);
lean_inc(v___x_3393_);
v___x_3404_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 8, 6);
lean_closure_set(v___x_3404_, 0, v___y_3401_);
lean_closure_set(v___x_3404_, 1, v_parserState_3389_);
lean_closure_set(v___x_3404_, 2, v_commandState_3390_);
lean_closure_set(v___x_3404_, 3, v___x_3393_);
lean_closure_set(v___x_3404_, 4, v___x_3403_);
lean_closure_set(v___x_3404_, 5, v___x_3394_);
if (lean_obj_tag(v_old_x3f_3391_) == 0)
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_box(0);
v___y_3396_ = v___x_3404_;
v___y_3397_ = v___x_3405_;
goto v___jp_3395_;
}
else
{
lean_object* v_val_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3414_; 
v_val_3406_ = lean_ctor_get(v_old_x3f_3391_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_old_x3f_3391_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3408_ = v_old_x3f_3391_;
v_isShared_3409_ = v_isSharedCheck_3414_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_val_3406_);
lean_dec(v_old_x3f_3391_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3414_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v___x_3412_; 
v_fst_3410_ = lean_ctor_get(v_val_3406_, 0);
lean_inc(v_fst_3410_);
lean_dec(v_val_3406_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_fst_3410_);
v___x_3412_ = v___x_3408_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_fst_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
v___y_3396_ = v___x_3404_;
v___y_3397_ = v___x_3412_;
goto v___jp_3395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3419_, lean_object* v_parserState_3420_, lean_object* v_commandState_3421_, lean_object* v_old_x3f_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3419_, v_parserState_3420_, v_commandState_3421_, v_old_x3f_3422_);
lean_dec_ref(v_inputCtx_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3425_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3426_; 
v_nextCmdSnap_x3f_3426_ = lean_ctor_get(v_snap_3425_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3426_) == 1)
{
lean_object* v_val_3427_; lean_object* v___x_3428_; 
lean_inc_ref(v_nextCmdSnap_x3f_3426_);
lean_dec_ref(v_snap_3425_);
v_val_3427_ = lean_ctor_get(v_nextCmdSnap_x3f_3426_, 0);
lean_inc(v_val_3427_);
lean_dec_ref(v_nextCmdSnap_x3f_3426_);
v___x_3428_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3427_);
v_snap_3425_ = v___x_3428_;
goto _start;
}
else
{
lean_object* v_elabSnap_3430_; lean_object* v_resultSnap_3431_; lean_object* v___x_3432_; lean_object* v_cmdState_3433_; lean_object* v___x_3434_; 
v_elabSnap_3430_ = lean_ctor_get(v_snap_3425_, 3);
lean_inc_ref(v_elabSnap_3430_);
lean_dec_ref(v_snap_3425_);
v_resultSnap_3431_ = lean_ctor_get(v_elabSnap_3430_, 2);
lean_inc_ref(v_resultSnap_3431_);
lean_dec_ref(v_elabSnap_3430_);
v___x_3432_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3431_);
v_cmdState_3433_ = lean_ctor_get(v___x_3432_, 1);
lean_inc_ref(v_cmdState_3433_);
lean_dec(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v_cmdState_3433_);
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3435_){
_start:
{
lean_object* v_result_x3f_3436_; 
v_result_x3f_3436_ = lean_ctor_get(v_snap_3435_, 4);
lean_inc(v_result_x3f_3436_);
lean_dec_ref(v_snap_3435_);
if (lean_obj_tag(v_result_x3f_3436_) == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_box(0);
return v___x_3437_;
}
else
{
lean_object* v_val_3438_; lean_object* v_processedSnap_3439_; lean_object* v___x_3440_; lean_object* v_result_x3f_3441_; 
v_val_3438_ = lean_ctor_get(v_result_x3f_3436_, 0);
lean_inc(v_val_3438_);
lean_dec_ref(v_result_x3f_3436_);
v_processedSnap_3439_ = lean_ctor_get(v_val_3438_, 1);
lean_inc_ref(v_processedSnap_3439_);
lean_dec(v_val_3438_);
v___x_3440_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3439_);
v_result_x3f_3441_ = lean_ctor_get(v___x_3440_, 2);
lean_inc(v_result_x3f_3441_);
lean_dec(v___x_3440_);
if (lean_obj_tag(v_result_x3f_3441_) == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
return v___x_3442_;
}
else
{
lean_object* v_val_3443_; lean_object* v_firstCmdSnap_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_val_3443_ = lean_ctor_get(v_result_x3f_3441_, 0);
lean_inc(v_val_3443_);
lean_dec_ref(v_result_x3f_3441_);
v_firstCmdSnap_3444_ = lean_ctor_get(v_val_3443_, 1);
lean_inc_ref(v_firstCmdSnap_3444_);
lean_dec(v_val_3443_);
v___x_3445_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3444_);
v___x_3446_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3445_);
return v___x_3446_;
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

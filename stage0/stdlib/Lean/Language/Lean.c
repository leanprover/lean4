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
uint8_t v___y_9163__boxed_642_; uint8_t v_suppressElabErrors_boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v___y_9163__boxed_642_ = lean_unbox(v___y_639_);
v_suppressElabErrors_boxed_643_ = lean_unbox(v_suppressElabErrors_640_);
v_res_644_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9163__boxed_642_, v_suppressElabErrors_boxed_643_, v_x_641_);
lean_dec(v_x_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_647_, lean_object* v_msgData_648_, uint8_t v_severity_649_, uint8_t v_isSilent_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; uint8_t v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; uint8_t v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; uint8_t v___y_754_; uint8_t v___y_755_; uint8_t v___y_756_; uint8_t v___x_771_; uint8_t v___y_773_; uint8_t v___y_774_; uint8_t v___y_775_; uint8_t v___y_777_; uint8_t v___x_789_; 
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
lean_ctor_set(v___x_688_, 1, v___y_658_);
lean_inc_ref(v___y_656_);
lean_inc_ref(v___y_660_);
v___x_689_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_689_, 0, v___y_660_);
lean_ctor_set(v___x_689_, 1, v___y_655_);
lean_ctor_set(v___x_689_, 2, v___y_657_);
lean_ctor_set(v___x_689_, 3, v___y_656_);
lean_ctor_set(v___x_689_, 4, v___x_688_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*5, v___y_659_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*5 + 1, v___y_661_);
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
lean_dec(v___y_657_);
lean_dec_ref(v___y_655_);
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
lean_dec(v___y_657_);
lean_dec_ref(v___y_655_);
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
v___y_655_ = v___x_732_;
v___y_656_ = v___x_735_;
v___y_657_ = v___x_734_;
v___y_658_ = v_a_728_;
v___y_659_ = v___y_720_;
v___y_660_ = v_fileName_723_;
v___y_661_ = v___y_721_;
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
v___y_655_ = v___x_732_;
v___y_656_ = v___x_735_;
v___y_657_ = v___x_734_;
v___y_658_ = v_a_728_;
v___y_659_ = v___y_720_;
v___y_660_ = v_fileName_723_;
v___y_661_ = v___y_721_;
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
lean_object* v___x_1074_; lean_object* v_toProcessingContext_1075_; lean_object* v_fileName_1076_; lean_object* v_fileMap_1077_; lean_object* v_opts_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; uint8_t v___y_1088_; lean_object* v___y_1089_; lean_object* v_messages_1090_; lean_object* v___y_1116_; 
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
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*4, v___y_1088_);
v___x_1095_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1080_, v___x_1094_);
v___x_1096_ = lean_io_promise_resolve(v___x_1095_, v_new_1091_);
lean_dec(v_new_1091_);
v_env_1097_ = lean_ctor_get(v___y_1089_, 0);
v_scopes_1098_ = lean_ctor_get(v___y_1089_, 2);
v_usedQuotCtxts_1099_ = lean_ctor_get(v___y_1089_, 3);
v_nextMacroScope_1100_ = lean_ctor_get(v___y_1089_, 4);
v_maxRecDepth_1101_ = lean_ctor_get(v___y_1089_, 5);
v_ngen_1102_ = lean_ctor_get(v___y_1089_, 6);
v_auxDeclNGen_1103_ = lean_ctor_get(v___y_1089_, 7);
v_infoState_1104_ = lean_ctor_get(v___y_1089_, 8);
v_traceState_1105_ = lean_ctor_get(v___y_1089_, 9);
v_snapshotTasks_1106_ = lean_ctor_get(v___y_1089_, 10);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___y_1089_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___y_1089_, 1);
lean_dec(v_unused_1114_);
v___x_1108_ = v___y_1089_;
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
lean_dec(v___y_1089_);
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
v___y_1088_ = v___x_1118_;
v___y_1089_ = v___x_1125_;
v_messages_1090_ = v___x_1135_;
goto v___jp_1087_;
}
else
{
lean_dec(v_fst_1124_);
lean_dec(v_beginPos_1050_);
v___y_1088_ = v___x_1118_;
v___y_1089_ = v___x_1125_;
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
uint8_t v_val_44557__boxed_1266_; size_t v_sz_boxed_1267_; size_t v_i_boxed_1268_; lean_object* v_res_1269_; 
v_val_44557__boxed_1266_ = lean_unbox(v_val_1260_);
v_sz_boxed_1267_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1268_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3_spec__5(v___x_1257_, v___x_1258_, v___x_1259_, v_val_44557__boxed_1266_, v_as_1261_, v_sz_boxed_1267_, v_i_boxed_1268_, v_b_1264_);
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
uint8_t v_val_44609__boxed_1309_; size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_val_44609__boxed_1309_ = lean_unbox(v_val_1303_);
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1300_, v___x_1301_, v___x_1302_, v_val_44609__boxed_1309_, v_as_1304_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1307_);
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
lean_object* v_cs_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1336_; 
v_cs_1321_ = lean_ctor_get(v_n_1318_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_n_1318_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1323_ = v_n_1318_;
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_cs_1321_);
lean_dec(v_n_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; size_t v_sz_1327_; size_t v___x_1328_; lean_object* v___x_1329_; lean_object* v_fst_1330_; 
v___x_1325_ = lean_box(0);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_b_1319_);
v_sz_1327_ = lean_array_size(v_cs_1321_);
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1313_, v___x_1314_, v___x_1315_, v___x_1316_, v_val_1317_, v_cs_1321_, v_sz_1327_, v___x_1328_, v___x_1326_);
lean_dec_ref(v_cs_1321_);
v_fst_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_fst_1330_);
if (lean_obj_tag(v_fst_1330_) == 0)
{
lean_object* v_snd_1331_; lean_object* v___x_1333_; 
v_snd_1331_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_snd_1331_);
lean_dec_ref(v___x_1329_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 1);
lean_ctor_set(v___x_1323_, 0, v_snd_1331_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_snd_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v_val_1335_; 
lean_dec_ref(v___x_1329_);
lean_del_object(v___x_1323_);
v_val_1335_ = lean_ctor_get(v_fst_1330_, 0);
lean_inc(v_val_1335_);
lean_dec_ref(v_fst_1330_);
return v_val_1335_;
}
}
}
else
{
lean_object* v_vs_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1352_; 
v_vs_1337_ = lean_ctor_get(v_n_1318_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_n_1318_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1339_ = v_n_1318_;
v_isShared_1340_ = v_isSharedCheck_1352_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_vs_1337_);
lean_dec(v_n_1318_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1352_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; size_t v_sz_1343_; size_t v___x_1344_; lean_object* v___x_1345_; lean_object* v_fst_1346_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_b_1319_);
v_sz_1343_ = lean_array_size(v_vs_1337_);
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__3(v___x_1314_, v___x_1315_, v___x_1316_, v_val_1317_, v_vs_1337_, v_sz_1343_, v___x_1344_, v___x_1342_);
lean_dec_ref(v_vs_1337_);
v_fst_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_fst_1346_);
if (lean_obj_tag(v_fst_1346_) == 0)
{
lean_object* v_snd_1347_; lean_object* v___x_1349_; 
v_snd_1347_ = lean_ctor_get(v___x_1345_, 1);
lean_inc(v_snd_1347_);
lean_dec_ref(v___x_1345_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_snd_1347_);
v___x_1349_ = v___x_1339_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_snd_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
lean_object* v_val_1351_; 
lean_dec_ref(v___x_1345_);
lean_del_object(v___x_1339_);
v_val_1351_ = lean_ctor_get(v_fst_1346_, 0);
lean_inc(v_val_1351_);
lean_dec_ref(v_fst_1346_);
return v_val_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(lean_object* v_init_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, uint8_t v_val_1357_, lean_object* v_as_1358_, size_t v_sz_1359_, size_t v_i_1360_, lean_object* v_b_1361_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1360_, v_sz_1359_);
if (v___x_1363_ == 0)
{
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1354_);
return v_b_1361_;
}
else
{
lean_object* v_snd_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1382_; 
v_snd_1364_ = lean_ctor_get(v_b_1361_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_b_1361_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_b_1361_, 0);
lean_dec(v_unused_1383_);
v___x_1366_ = v_b_1361_;
v_isShared_1367_ = v_isSharedCheck_1382_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snd_1364_);
lean_dec(v_b_1361_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1382_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_array_uget_borrowed(v_as_1358_, v_i_1360_);
lean_inc(v_snd_1364_);
lean_inc(v_a_1368_);
lean_inc_ref(v___x_1356_);
lean_inc_ref(v___x_1354_);
v___x_1369_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1353_, v___x_1354_, v___x_1355_, v___x_1356_, v_val_1357_, v_a_1368_, v_snd_1364_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1354_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1372_ = v___x_1366_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_snd_1364_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_snd_1364_);
v_a_1374_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1369_);
v___x_1375_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v_a_1374_);
lean_ctor_set(v___x_1366_, 0, v___x_1375_);
v___x_1377_ = v___x_1366_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_a_1374_);
v___x_1377_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
size_t v___x_1378_; size_t v___x_1379_; 
v___x_1378_ = ((size_t)1ULL);
v___x_1379_ = lean_usize_add(v_i_1360_, v___x_1378_);
v_i_1360_ = v___x_1379_;
v_b_1361_ = v___x_1377_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_init_1384_, lean_object* v___x_1385_, lean_object* v___x_1386_, lean_object* v___x_1387_, lean_object* v_val_1388_, lean_object* v_as_1389_, lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_val_44660__boxed_1394_; size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_val_44660__boxed_1394_ = lean_unbox(v_val_1388_);
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1_spec__2(v_init_1384_, v___x_1385_, v___x_1386_, v___x_1387_, v_val_44660__boxed_1394_, v_as_1389_, v_sz_boxed_1395_, v_i_boxed_1396_, v_b_1392_);
lean_dec_ref(v_as_1389_);
lean_dec(v___x_1386_);
lean_dec_ref(v_init_1384_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1___boxed(lean_object* v_init_1398_, lean_object* v___x_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v_val_1402_, lean_object* v_n_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v_val_44676__boxed_1406_; lean_object* v_res_1407_; 
v_val_44676__boxed_1406_ = lean_unbox(v_val_1402_);
v_res_1407_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1398_, v___x_1399_, v___x_1400_, v___x_1401_, v_val_44676__boxed_1406_, v_n_1403_, v_b_1404_);
lean_dec(v___x_1400_);
lean_dec_ref(v_init_1398_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v___x_1410_, uint8_t v_val_1411_, lean_object* v_as_1412_, size_t v_sz_1413_, size_t v_i_1414_, lean_object* v_b_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_lt(v_i_1414_, v_sz_1413_);
if (v___x_1417_ == 0)
{
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___x_1408_);
return v_b_1415_;
}
else
{
lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1436_; 
v_snd_1418_ = lean_ctor_get(v_b_1415_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_b_1415_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_b_1415_, 0);
lean_dec(v_unused_1437_);
v___x_1420_ = v_b_1415_;
v_isShared_1421_ = v_isSharedCheck_1436_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_dec(v_b_1415_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1436_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_a_1422_; lean_object* v_msg_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v_a_1422_ = lean_array_uget_borrowed(v_as_1412_, v_i_1414_);
v_msg_1423_ = lean_ctor_get(v_a_1422_, 1);
v___x_1424_ = lean_box(0);
lean_inc_ref(v___x_1408_);
v___x_1425_ = l_Lean_FileMap_toPosition(v___x_1408_, v___x_1409_);
v___x_1426_ = 0;
v___x_1427_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1423_);
lean_inc_ref(v___x_1410_);
v___x_1428_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1428_, 0, v___x_1410_);
lean_ctor_set(v___x_1428_, 1, v___x_1425_);
lean_ctor_set(v___x_1428_, 2, v___x_1424_);
lean_ctor_set(v___x_1428_, 3, v___x_1427_);
lean_ctor_set(v___x_1428_, 4, v_msg_1423_);
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*5, v_val_1411_);
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*5 + 1, v___x_1426_);
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*5 + 2, v_val_1411_);
v___x_1429_ = l_Lean_MessageLog_add(v___x_1428_, v_snd_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1429_);
lean_ctor_set(v___x_1420_, 0, v___x_1424_);
v___x_1431_ = v___x_1420_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
size_t v___x_1432_; size_t v___x_1433_; 
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = lean_usize_add(v_i_1414_, v___x_1432_);
v_i_1414_ = v___x_1433_;
v_b_1415_ = v___x_1431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1438_, lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v_val_1441_, lean_object* v_as_1442_, lean_object* v_sz_1443_, lean_object* v_i_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_val_44782__boxed_1447_; size_t v_sz_boxed_1448_; size_t v_i_boxed_1449_; lean_object* v_res_1450_; 
v_val_44782__boxed_1447_ = lean_unbox(v_val_1441_);
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1443_);
lean_dec(v_sz_1443_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1438_, v___x_1439_, v___x_1440_, v_val_44782__boxed_1447_, v_as_1442_, v_sz_boxed_1448_, v_i_boxed_1449_, v_b_1445_);
lean_dec_ref(v_as_1442_);
lean_dec(v___x_1439_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(lean_object* v___x_1451_, lean_object* v___x_1452_, lean_object* v___x_1453_, uint8_t v_val_1454_, lean_object* v_as_1455_, size_t v_sz_1456_, size_t v_i_1457_, lean_object* v_b_1458_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_lt(v_i_1457_, v_sz_1456_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1453_);
lean_dec_ref(v___x_1451_);
return v_b_1458_;
}
else
{
lean_object* v_snd_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1479_; 
v_snd_1461_ = lean_ctor_get(v_b_1458_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_b_1458_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_b_1458_, 0);
lean_dec(v_unused_1480_);
v___x_1463_ = v_b_1458_;
v_isShared_1464_ = v_isSharedCheck_1479_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snd_1461_);
lean_dec(v_b_1458_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1479_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_a_1465_; lean_object* v_msg_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v_a_1465_ = lean_array_uget_borrowed(v_as_1455_, v_i_1457_);
v_msg_1466_ = lean_ctor_get(v_a_1465_, 1);
v___x_1467_ = lean_box(0);
lean_inc_ref(v___x_1451_);
v___x_1468_ = l_Lean_FileMap_toPosition(v___x_1451_, v___x_1452_);
v___x_1469_ = 0;
v___x_1470_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1466_);
lean_inc_ref(v___x_1453_);
v___x_1471_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1471_, 0, v___x_1453_);
lean_ctor_set(v___x_1471_, 1, v___x_1468_);
lean_ctor_set(v___x_1471_, 2, v___x_1467_);
lean_ctor_set(v___x_1471_, 3, v___x_1470_);
lean_ctor_set(v___x_1471_, 4, v_msg_1466_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*5, v_val_1454_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*5 + 1, v___x_1469_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*5 + 2, v_val_1454_);
v___x_1472_ = l_Lean_MessageLog_add(v___x_1471_, v_snd_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v___x_1472_);
lean_ctor_set(v___x_1463_, 0, v___x_1467_);
v___x_1474_ = v___x_1463_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1457_, v___x_1475_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2_spec__5(v___x_1451_, v___x_1452_, v___x_1453_, v_val_1454_, v_as_1455_, v_sz_1456_, v___x_1476_, v___x_1474_);
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2___boxed(lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v_val_1484_, lean_object* v_as_1485_, lean_object* v_sz_1486_, lean_object* v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_val_44834__boxed_1490_; size_t v_sz_boxed_1491_; size_t v_i_boxed_1492_; lean_object* v_res_1493_; 
v_val_44834__boxed_1490_ = lean_unbox(v_val_1484_);
v_sz_boxed_1491_ = lean_unbox_usize(v_sz_1486_);
lean_dec(v_sz_1486_);
v_i_boxed_1492_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_res_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1481_, v___x_1482_, v___x_1483_, v_val_44834__boxed_1490_, v_as_1485_, v_sz_boxed_1491_, v_i_boxed_1492_, v_b_1488_);
lean_dec_ref(v_as_1485_);
lean_dec(v___x_1482_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v___x_1494_, lean_object* v___x_1495_, lean_object* v___x_1496_, uint8_t v_val_1497_, lean_object* v_t_1498_, lean_object* v_init_1499_){
_start:
{
lean_object* v_root_1501_; lean_object* v_tail_1502_; lean_object* v___x_1503_; 
v_root_1501_ = lean_ctor_get(v_t_1498_, 0);
lean_inc_ref(v_root_1501_);
v_tail_1502_ = lean_ctor_get(v_t_1498_, 1);
lean_inc_ref(v_tail_1502_);
lean_dec_ref(v_t_1498_);
lean_inc_ref(v___x_1496_);
lean_inc_ref(v___x_1494_);
lean_inc_ref(v_init_1499_);
v___x_1503_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__1(v_init_1499_, v___x_1494_, v___x_1495_, v___x_1496_, v_val_1497_, v_root_1501_, v_init_1499_);
lean_dec_ref(v_init_1499_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; 
lean_dec_ref(v_tail_1502_);
lean_dec_ref(v___x_1496_);
lean_dec_ref(v___x_1494_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
return v_a_1504_;
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; size_t v_sz_1508_; size_t v___x_1509_; lean_object* v___x_1510_; lean_object* v_fst_1511_; 
v_a_1505_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1503_);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_a_1505_);
v_sz_1508_ = lean_array_size(v_tail_1502_);
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1_spec__2(v___x_1494_, v___x_1495_, v___x_1496_, v_val_1497_, v_tail_1502_, v_sz_1508_, v___x_1509_, v___x_1507_);
lean_dec_ref(v_tail_1502_);
v_fst_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_fst_1511_);
if (lean_obj_tag(v_fst_1511_) == 0)
{
lean_object* v_snd_1512_; 
v_snd_1512_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_snd_1512_);
lean_dec_ref(v___x_1510_);
return v_snd_1512_;
}
else
{
lean_object* v_val_1513_; 
lean_dec_ref(v___x_1510_);
v_val_1513_ = lean_ctor_get(v_fst_1511_, 0);
lean_inc(v_val_1513_);
lean_dec_ref(v_fst_1511_);
return v_val_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1___boxed(lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v_val_1517_, lean_object* v_t_1518_, lean_object* v_init_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_val_44885__boxed_1521_; lean_object* v_res_1522_; 
v_val_44885__boxed_1521_ = lean_unbox(v_val_1517_);
v_res_1522_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v___x_1514_, v___x_1515_, v___x_1516_, v_val_44885__boxed_1521_, v_t_1518_, v_init_1519_);
lean_dec(v___x_1515_);
return v_res_1522_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = l_Lean_firstFrontendMacroScope;
v___x_1525_ = lean_nat_add(v___x_1524_, v___x_1523_);
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1532_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1537_, lean_object* v___x_1538_, lean_object* v___x_1539_, size_t v___x_1540_, uint8_t v___x_1541_, lean_object* v_env_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v_a_1545_, lean_object* v_opts_1546_, lean_object* v___x_1547_, lean_object* v_pos_1548_, uint8_t v_val_1549_, lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v___x_1552_, lean_object* v___x_1553_, uint8_t v___x_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_toProcessingContext_1576_; lean_object* v_fileName_1577_; lean_object* v_fileMap_1578_; lean_object* v_env_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; lean_object* v_fileName_1585_; lean_object* v_fileMap_1586_; lean_object* v_currRecDepth_1587_; lean_object* v_ref_1588_; lean_object* v_currNamespace_1589_; lean_object* v_openDecls_1590_; lean_object* v_initHeartbeats_1591_; lean_object* v_maxHeartbeats_1592_; lean_object* v_quotContext_1593_; lean_object* v_currMacroScope_1594_; lean_object* v_cancelTk_x3f_1595_; uint8_t v_suppressElabErrors_1596_; lean_object* v_inheritedTraceOptions_1597_; lean_object* v___y_1598_; uint8_t v___y_1615_; uint8_t v___x_1635_; 
v___x_1557_ = l_Lean_firstFrontendMacroScope;
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_1560_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_1561_ = lean_box(0);
lean_inc(v___x_1537_);
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1537_);
lean_ctor_set(v___x_1562_, 1, v___x_1558_);
lean_ctor_set(v___x_1562_, 2, v___x_1561_);
v___x_1563_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5);
v___x_1564_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__6);
v___x_1565_ = lean_mk_empty_array_with_capacity(v___x_1538_);
lean_inc_ref(v___x_1565_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_inc_n(v___x_1539_, 2);
v___x_1567_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v___x_1565_);
lean_ctor_set(v___x_1567_, 2, v___x_1539_);
lean_ctor_set(v___x_1567_, 3, v___x_1539_);
lean_ctor_set_usize(v___x_1567_, 4, v___x_1540_);
v___x_1568_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1567_, 2);
v___x_1569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1567_);
lean_ctor_set(v___x_1569_, 2, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1563_);
lean_ctor_set(v___x_1570_, 1, v___x_1563_);
lean_ctor_set(v___x_1570_, 2, v___x_1567_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*3, v___x_1541_);
v___x_1571_ = lean_mk_empty_array_with_capacity(v___x_1539_);
lean_inc_ref(v___x_1571_);
lean_inc_ref(v___x_1543_);
v___x_1572_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1572_, 0, v_env_1542_);
lean_ctor_set(v___x_1572_, 1, v___x_1559_);
lean_ctor_set(v___x_1572_, 2, v___x_1560_);
lean_ctor_set(v___x_1572_, 3, v___x_1562_);
lean_ctor_set(v___x_1572_, 4, v___x_1543_);
lean_ctor_set(v___x_1572_, 5, v___x_1564_);
lean_ctor_set(v___x_1572_, 6, v___x_1569_);
lean_ctor_set(v___x_1572_, 7, v___x_1570_);
lean_ctor_set(v___x_1572_, 8, v___x_1571_);
v___x_1573_ = lean_st_mk_ref(v___x_1572_);
v___x_1574_ = lean_st_ref_get(v___x_1544_);
v___x_1575_ = lean_st_ref_get(v___x_1573_);
v_toProcessingContext_1576_ = lean_ctor_get(v_a_1545_, 0);
v_fileName_1577_ = lean_ctor_get(v_toProcessingContext_1576_, 1);
v_fileMap_1578_ = lean_ctor_get(v_toProcessingContext_1576_, 2);
v_env_1579_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_ref(v_env_1579_);
lean_dec(v___x_1575_);
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Lean_Core_getMaxHeartbeats(v_opts_1546_);
v___x_1582_ = l_Lean_diagnostics;
v___x_1583_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1546_, v___x_1582_);
v___x_1635_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1579_);
lean_dec_ref(v_env_1579_);
if (v___x_1635_ == 0)
{
if (v___x_1583_ == 0)
{
v___y_1615_ = v___x_1554_;
goto v___jp_1614_;
}
else
{
v___y_1615_ = v___x_1635_;
goto v___jp_1614_;
}
}
else
{
v___y_1615_ = v___x_1583_;
goto v___jp_1614_;
}
v___jp_1584_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1599_ = l_Lean_maxRecDepth;
v___x_1600_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(v_opts_1546_, v___x_1599_);
lean_inc(v_currMacroScope_1594_);
lean_inc(v_openDecls_1590_);
lean_inc(v_ref_1588_);
v___x_1601_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1601_, 0, v_fileName_1585_);
lean_ctor_set(v___x_1601_, 1, v_fileMap_1586_);
lean_ctor_set(v___x_1601_, 2, v_opts_1546_);
lean_ctor_set(v___x_1601_, 3, v_currRecDepth_1587_);
lean_ctor_set(v___x_1601_, 4, v___x_1600_);
lean_ctor_set(v___x_1601_, 5, v_ref_1588_);
lean_ctor_set(v___x_1601_, 6, v_currNamespace_1589_);
lean_ctor_set(v___x_1601_, 7, v_openDecls_1590_);
lean_ctor_set(v___x_1601_, 8, v_initHeartbeats_1591_);
lean_ctor_set(v___x_1601_, 9, v_maxHeartbeats_1592_);
lean_ctor_set(v___x_1601_, 10, v_quotContext_1593_);
lean_ctor_set(v___x_1601_, 11, v_currMacroScope_1594_);
lean_ctor_set(v___x_1601_, 12, v_cancelTk_x3f_1595_);
lean_ctor_set(v___x_1601_, 13, v_inheritedTraceOptions_1597_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14, v___x_1583_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*14 + 1, v_suppressElabErrors_1596_);
v___x_1602_ = l_Lean_Language_SnapshotTree_trace(v___x_1547_, v___x_1601_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1603_; lean_object* v_traceState_1604_; lean_object* v_traces_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v___x_1602_);
lean_dec_ref(v___x_1552_);
v___x_1603_ = lean_st_ref_get(v___x_1573_);
lean_dec(v___x_1573_);
v_traceState_1604_ = lean_ctor_get(v___x_1603_, 4);
lean_inc_ref(v_traceState_1604_);
lean_dec(v___x_1603_);
v_traces_1605_ = lean_ctor_get(v_traceState_1604_, 0);
lean_inc_ref(v_traces_1605_);
lean_dec_ref(v_traceState_1604_);
v___x_1606_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1577_);
lean_inc_ref(v_fileMap_1578_);
v___x_1607_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(v_fileMap_1578_, v_pos_1548_, v_fileName_1577_, v_val_1549_, v_traces_1605_, v___x_1606_);
v___x_1608_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1609_, 0, v___x_1550_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
lean_ctor_set(v___x_1609_, 2, v___x_1551_);
lean_ctor_set(v___x_1609_, 3, v___x_1543_);
lean_ctor_set_uint8(v___x_1609_, sizeof(void*)*4, v_val_1549_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1571_);
v___x_1611_ = lean_task_pure(v___x_1610_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v___x_1602_);
lean_dec(v___x_1573_);
lean_dec(v___x_1551_);
lean_dec_ref(v___x_1550_);
lean_dec_ref(v___x_1543_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1552_);
lean_ctor_set(v___x_1612_, 1, v___x_1571_);
v___x_1613_ = lean_task_pure(v___x_1612_);
return v___x_1613_;
}
}
v___jp_1614_:
{
if (v___y_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v_env_1617_; lean_object* v_nextMacroScope_1618_; lean_object* v_ngen_1619_; lean_object* v_auxDeclNGen_1620_; lean_object* v_traceState_1621_; lean_object* v_messages_1622_; lean_object* v_infoState_1623_; lean_object* v_snapshotTasks_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1633_; 
v___x_1616_ = lean_st_ref_take(v___x_1573_);
v_env_1617_ = lean_ctor_get(v___x_1616_, 0);
v_nextMacroScope_1618_ = lean_ctor_get(v___x_1616_, 1);
v_ngen_1619_ = lean_ctor_get(v___x_1616_, 2);
v_auxDeclNGen_1620_ = lean_ctor_get(v___x_1616_, 3);
v_traceState_1621_ = lean_ctor_get(v___x_1616_, 4);
v_messages_1622_ = lean_ctor_get(v___x_1616_, 6);
v_infoState_1623_ = lean_ctor_get(v___x_1616_, 7);
v_snapshotTasks_1624_ = lean_ctor_get(v___x_1616_, 8);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v___x_1616_, 5);
lean_dec(v_unused_1634_);
v___x_1626_ = v___x_1616_;
v_isShared_1627_ = v_isSharedCheck_1633_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snapshotTasks_1624_);
lean_inc(v_infoState_1623_);
lean_inc(v_messages_1622_);
lean_inc(v_traceState_1621_);
lean_inc(v_auxDeclNGen_1620_);
lean_inc(v_ngen_1619_);
lean_inc(v_nextMacroScope_1618_);
lean_inc(v_env_1617_);
lean_dec(v___x_1616_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1633_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = l_Lean_Kernel_enableDiag(v_env_1617_, v___x_1583_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 5, v___x_1564_);
lean_ctor_set(v___x_1626_, 0, v___x_1628_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_nextMacroScope_1618_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_ngen_1619_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_auxDeclNGen_1620_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v_traceState_1621_);
lean_ctor_set(v_reuseFailAlloc_1632_, 5, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1632_, 6, v_messages_1622_);
lean_ctor_set(v_reuseFailAlloc_1632_, 7, v_infoState_1623_);
lean_ctor_set(v_reuseFailAlloc_1632_, 8, v_snapshotTasks_1624_);
v___x_1630_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_st_ref_set(v___x_1573_, v___x_1630_);
lean_inc(v___x_1573_);
lean_inc(v___x_1537_);
lean_inc(v___x_1539_);
lean_inc_ref(v_fileMap_1578_);
lean_inc_ref(v_fileName_1577_);
v_fileName_1585_ = v_fileName_1577_;
v_fileMap_1586_ = v_fileMap_1578_;
v_currRecDepth_1587_ = v___x_1539_;
v_ref_1588_ = v___x_1580_;
v_currNamespace_1589_ = v___x_1537_;
v_openDecls_1590_ = v___x_1561_;
v_initHeartbeats_1591_ = v___x_1539_;
v_maxHeartbeats_1592_ = v___x_1581_;
v_quotContext_1593_ = v___x_1537_;
v_currMacroScope_1594_ = v___x_1557_;
v_cancelTk_x3f_1595_ = v___x_1553_;
v_suppressElabErrors_1596_ = v_val_1549_;
v_inheritedTraceOptions_1597_ = v___x_1574_;
v___y_1598_ = v___x_1573_;
goto v___jp_1584_;
}
}
}
else
{
lean_inc(v___x_1573_);
lean_inc(v___x_1537_);
lean_inc(v___x_1539_);
lean_inc_ref(v_fileMap_1578_);
lean_inc_ref(v_fileName_1577_);
v_fileName_1585_ = v_fileName_1577_;
v_fileMap_1586_ = v_fileMap_1578_;
v_currRecDepth_1587_ = v___x_1539_;
v_ref_1588_ = v___x_1580_;
v_currNamespace_1589_ = v___x_1537_;
v_openDecls_1590_ = v___x_1561_;
v_initHeartbeats_1591_ = v___x_1539_;
v_maxHeartbeats_1592_ = v___x_1581_;
v_quotContext_1593_ = v___x_1537_;
v_currMacroScope_1594_ = v___x_1557_;
v_cancelTk_x3f_1595_ = v___x_1553_;
v_suppressElabErrors_1596_ = v_val_1549_;
v_inheritedTraceOptions_1597_ = v___x_1574_;
v___y_1598_ = v___x_1573_;
goto v___jp_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_1636_ = _args[0];
lean_object* v___x_1637_ = _args[1];
lean_object* v___x_1638_ = _args[2];
lean_object* v___x_1639_ = _args[3];
lean_object* v___x_1640_ = _args[4];
lean_object* v_env_1641_ = _args[5];
lean_object* v___x_1642_ = _args[6];
lean_object* v___x_1643_ = _args[7];
lean_object* v_a_1644_ = _args[8];
lean_object* v_opts_1645_ = _args[9];
lean_object* v___x_1646_ = _args[10];
lean_object* v_pos_1647_ = _args[11];
lean_object* v_val_1648_ = _args[12];
lean_object* v___x_1649_ = _args[13];
lean_object* v___x_1650_ = _args[14];
lean_object* v___x_1651_ = _args[15];
lean_object* v___x_1652_ = _args[16];
lean_object* v___x_1653_ = _args[17];
lean_object* v_x_1654_ = _args[18];
lean_object* v___y_1655_ = _args[19];
_start:
{
size_t v___x_44946__boxed_1656_; uint8_t v___x_44947__boxed_1657_; uint8_t v_val_44951__boxed_1658_; uint8_t v___x_44956__boxed_1659_; lean_object* v_res_1660_; 
v___x_44946__boxed_1656_ = lean_unbox_usize(v___x_1639_);
lean_dec(v___x_1639_);
v___x_44947__boxed_1657_ = lean_unbox(v___x_1640_);
v_val_44951__boxed_1658_ = lean_unbox(v_val_1648_);
v___x_44956__boxed_1659_ = lean_unbox(v___x_1653_);
v_res_1660_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1636_, v___x_1637_, v___x_1638_, v___x_44946__boxed_1656_, v___x_44947__boxed_1657_, v_env_1641_, v___x_1642_, v___x_1643_, v_a_1644_, v_opts_1645_, v___x_1646_, v_pos_1647_, v_val_44951__boxed_1658_, v___x_1649_, v___x_1650_, v___x_1651_, v___x_1652_, v___x_44956__boxed_1659_, v_x_1654_);
lean_dec(v_pos_1647_);
lean_dec_ref(v_a_1644_);
lean_dec(v___x_1643_);
lean_dec(v___x_1637_);
return v_res_1660_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1667_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1668_ = l_Lean_Name_append(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(lean_object* v___x_1669_, lean_object* v___x_1670_, uint8_t v_val_1671_, lean_object* v_val_1672_, lean_object* v_val_1673_, lean_object* v___x_1674_, lean_object* v___x_1675_, uint8_t v___x_1676_, lean_object* v_a_1677_, lean_object* v_pos_1678_, lean_object* v_infoSt_1679_){
_start:
{
lean_object* v___y_1682_; lean_object* v_msgLog_1683_; lean_object* v___y_1689_; lean_object* v_trees_1721_; lean_object* v_size_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_trees_1721_ = lean_ctor_get(v_infoSt_1679_, 2);
v_size_1722_ = lean_ctor_get(v_trees_1721_, 2);
v___x_1723_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1724_ = lean_nat_dec_lt(v___x_1675_, v_size_1722_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = l_outOfBounds___redArg(v___x_1723_);
v___y_1689_ = v___x_1725_;
goto v___jp_1688_;
}
else
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1723_, v_trees_1721_, v___x_1675_);
v___y_1689_ = v___x_1726_;
goto v___jp_1688_;
}
v___jp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1684_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1683_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___y_1682_);
v___x_1686_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1686_, 0, v___x_1669_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
lean_ctor_set(v___x_1686_, 2, v___x_1685_);
lean_ctor_set(v___x_1686_, 3, v___x_1670_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*4, v_val_1671_);
v___x_1687_ = lean_io_promise_resolve(v___x_1686_, v_val_1672_);
return v___x_1687_;
}
v___jp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_scopes_1692_; lean_object* v___x_1693_; lean_object* v_opts_1694_; uint8_t v_hasTrace_1695_; lean_object* v___x_1696_; 
v___x_1690_ = l_Lean_inheritedTraceOptions;
v___x_1691_ = lean_st_ref_get(v___x_1690_);
v_scopes_1692_ = lean_ctor_get(v_val_1673_, 2);
v___x_1693_ = l_List_head_x21___redArg(v___x_1674_, v_scopes_1692_);
v_opts_1694_ = lean_ctor_get(v___x_1693_, 1);
lean_inc_ref(v_opts_1694_);
lean_dec(v___x_1693_);
v_hasTrace_1695_ = lean_ctor_get_uint8(v_opts_1694_, sizeof(void*)*1);
v___x_1696_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1695_ == 0)
{
lean_dec_ref(v_opts_1694_);
lean_dec(v___x_1691_);
lean_dec(v___x_1675_);
v___y_1682_ = v___y_1689_;
v_msgLog_1683_ = v___x_1696_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__2));
v___x_1698_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1699_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___closed__3);
v___x_1700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1691_, v_opts_1694_, v___x_1699_);
lean_dec_ref(v_opts_1694_);
lean_dec(v___x_1691_);
if (v___x_1700_ == 0)
{
lean_dec(v___x_1675_);
v___y_1682_ = v___y_1689_;
v_msgLog_1683_ = v___x_1696_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_box(0);
lean_inc_ref(v___y_1689_);
v___x_1702_ = l_Lean_Elab_InfoTree_format(v___y_1689_, v___x_1701_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; double v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_toProcessingContext_1707_; lean_object* v_fileName_1708_; lean_object* v_fileMap_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = lean_float_of_nat(v___x_1675_);
v___x_1705_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1706_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1706_, 0, v___x_1697_);
lean_ctor_set(v___x_1706_, 1, v___x_1701_);
lean_ctor_set(v___x_1706_, 2, v___x_1705_);
lean_ctor_set_float(v___x_1706_, sizeof(void*)*3, v___x_1704_);
lean_ctor_set_float(v___x_1706_, sizeof(void*)*3 + 8, v___x_1704_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*3 + 16, v___x_1676_);
v_toProcessingContext_1707_ = lean_ctor_get(v_a_1677_, 0);
v_fileName_1708_ = lean_ctor_get(v_toProcessingContext_1707_, 1);
v_fileMap_1709_ = lean_ctor_get(v_toProcessingContext_1707_, 2);
v___x_1710_ = l_Lean_MessageData_nil;
v___x_1711_ = l_Lean_MessageData_ofFormat(v_a_1703_);
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = lean_mk_empty_array_with_capacity(v___x_1712_);
v___x_1714_ = lean_array_push(v___x_1713_, v___x_1711_);
v___x_1715_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1706_);
lean_ctor_set(v___x_1715_, 1, v___x_1710_);
lean_ctor_set(v___x_1715_, 2, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1698_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
lean_inc_ref(v_fileMap_1709_);
v___x_1717_ = l_Lean_FileMap_toPosition(v_fileMap_1709_, v_pos_1678_);
v___x_1718_ = 0;
lean_inc_ref(v_fileName_1708_);
v___x_1719_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1719_, 0, v_fileName_1708_);
lean_ctor_set(v___x_1719_, 1, v___x_1717_);
lean_ctor_set(v___x_1719_, 2, v___x_1701_);
lean_ctor_set(v___x_1719_, 3, v___x_1705_);
lean_ctor_set(v___x_1719_, 4, v___x_1716_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*5, v_val_1671_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*5 + 1, v___x_1718_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*5 + 2, v_val_1671_);
v___x_1720_ = l_Lean_MessageLog_add(v___x_1719_, v___x_1696_);
v___y_1682_ = v___y_1689_;
v_msgLog_1683_ = v___x_1720_;
goto v___jp_1681_;
}
else
{
lean_dec_ref(v___x_1702_);
lean_dec(v___x_1675_);
v___y_1682_ = v___y_1689_;
v_msgLog_1683_ = v___x_1696_;
goto v___jp_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed(lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_val_1729_, lean_object* v_val_1730_, lean_object* v_val_1731_, lean_object* v___x_1732_, lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v_a_1735_, lean_object* v_pos_1736_, lean_object* v_infoSt_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v_val_45133__boxed_1739_; uint8_t v___x_45138__boxed_1740_; lean_object* v_res_1741_; 
v_val_45133__boxed_1739_ = lean_unbox(v_val_1729_);
v___x_45138__boxed_1740_ = lean_unbox(v___x_1734_);
v_res_1741_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7(v___x_1727_, v___x_1728_, v_val_45133__boxed_1739_, v_val_1730_, v_val_1731_, v___x_1732_, v___x_1733_, v___x_45138__boxed_1740_, v_a_1735_, v_pos_1736_, v_infoSt_1737_);
lean_dec_ref(v_infoSt_1737_);
lean_dec(v_pos_1736_);
lean_dec_ref(v_a_1735_);
lean_dec_ref(v___x_1732_);
lean_dec_ref(v_val_1731_);
lean_dec(v_val_1730_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(lean_object* v_as_1743_, size_t v_i_1744_, size_t v_stop_1745_, lean_object* v_b_1746_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_usize_dec_eq(v_i_1744_, v_stop_1745_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; 
v___x_1749_ = lean_array_uget_borrowed(v_as_1743_, v_i_1744_);
v___f_1750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___closed__0));
lean_inc(v___x_1749_);
v___x_1751_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1750_, v___x_1749_);
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1744_, v___x_1752_);
v_i_1744_ = v___x_1753_;
v_b_1746_ = v___x_1751_;
goto _start;
}
else
{
return v_b_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg___boxed(lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_stop_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_){
_start:
{
size_t v_i_boxed_1760_; size_t v_stop_boxed_1761_; lean_object* v_res_1762_; 
v_i_boxed_1760_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_stop_boxed_1761_ = lean_unbox_usize(v_stop_1757_);
lean_dec(v_stop_1757_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_1755_, v_i_boxed_1760_, v_stop_boxed_1761_, v_b_1758_);
lean_dec_ref(v_as_1755_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed(lean_object* v_oldResult_1763_, lean_object* v_newParserState_1764_, lean_object* v_val_1765_, lean_object* v_sync_1766_, lean_object* v_val_1767_, lean_object* v_a_1768_, lean_object* v_oldNext_1769_, lean_object* v___y_1770_){
_start:
{
uint8_t v_sync_boxed_1771_; lean_object* v_res_1772_; 
v_sync_boxed_1771_ = lean_unbox(v_sync_1766_);
v_res_1772_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(v_oldResult_1763_, v_newParserState_1764_, v_val_1765_, v_sync_boxed_1771_, v_val_1767_, v_a_1768_, v_oldNext_1769_);
lean_dec_ref(v_a_1768_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_val_1773_, lean_object* v_newParserState_1774_, lean_object* v_val_1775_, uint8_t v_sync_1776_, lean_object* v_val_1777_, lean_object* v_a_1778_, lean_object* v_oldResult_1779_){
_start:
{
lean_object* v_task_1781_; lean_object* v___x_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; 
v_task_1781_ = lean_ctor_get(v_val_1773_, 3);
lean_inc_ref(v_task_1781_);
lean_dec_ref(v_val_1773_);
v___x_1782_ = lean_box(v_sync_1776_);
lean_inc_ref(v_a_1778_);
v___f_1783_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6___boxed), 8, 6);
lean_closure_set(v___f_1783_, 0, v_oldResult_1779_);
lean_closure_set(v___f_1783_, 1, v_newParserState_1774_);
lean_closure_set(v___f_1783_, 2, v_val_1775_);
lean_closure_set(v___f_1783_, 3, v___x_1782_);
lean_closure_set(v___f_1783_, 4, v_val_1777_);
lean_closure_set(v___f_1783_, 5, v_a_1778_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = 1;
v___x_1786_ = l_BaseIO_chainTask___redArg(v_task_1781_, v___f_1783_, v___x_1784_, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object* v_val_1787_, lean_object* v_newParserState_1788_, lean_object* v_val_1789_, lean_object* v_sync_1790_, lean_object* v_val_1791_, lean_object* v_a_1792_, lean_object* v_oldResult_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_sync_boxed_1795_; lean_object* v_res_1796_; 
v_sync_boxed_1795_ = lean_unbox(v_sync_1790_);
v_res_1796_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_val_1787_, v_newParserState_1788_, v_val_1789_, v_sync_boxed_1795_, v_val_1791_, v_a_1792_, v_oldResult_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1796_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1799_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1801_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__1));
v___x_1810_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1811_ = l_Lean_Name_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__3);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v___x_1815_, lean_object* v_val_1816_, lean_object* v_fst_1817_, uint8_t v_val_1818_, lean_object* v_a_1819_, lean_object* v_snd_1820_, lean_object* v___x_1821_, uint8_t v___x_1822_, lean_object* v_fst_1823_, lean_object* v_val_1824_, lean_object* v_val_1825_, lean_object* v_val_1826_, lean_object* v_snd_1827_, lean_object* v_prom_1828_, lean_object* v___x_1829_, lean_object* v___f_1830_, lean_object* v___f_1831_, lean_object* v___f_1832_, lean_object* v_pos_1833_, lean_object* v_fst_1834_, lean_object* v_cmdState_1835_, lean_object* v_opts_1836_, lean_object* v___x_1837_, lean_object* v_old_x3f_1838_, lean_object* v_parseCancelTk_1839_, lean_object* v_next_x3f_1840_){
_start:
{
lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v_snapshotTasks_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v_traceTask_1849_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; size_t v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v_env_1879_; lean_object* v_messages_1880_; lean_object* v_scopes_1881_; lean_object* v_infoState_1882_; lean_object* v_traceState_1883_; lean_object* v_snapshotTasks_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_reportedCmdState_1898_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; size_t v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v_reportedCmdState_1955_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; size_t v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; size_t v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_2018_; 
if (lean_obj_tag(v_next_x3f_1840_) == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_parseCancelTk_1839_);
v___x_2071_ = lean_box(0);
v___y_2018_ = v___x_2071_;
goto v___jp_2017_;
}
else
{
lean_object* v_toProcessingContext_2072_; lean_object* v_val_2073_; lean_object* v_pos_2074_; lean_object* v_endPos_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_toProcessingContext_2072_ = lean_ctor_get(v_a_1819_, 0);
v_val_2073_ = lean_ctor_get(v_next_x3f_1840_, 0);
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
lean_ctor_set(v___x_2079_, 0, v_parseCancelTk_1839_);
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
v___jp_1842_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1850_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1850_, 0, v___y_1847_);
lean_ctor_set(v___x_1850_, 1, v___x_1815_);
lean_ctor_set(v___x_1850_, 2, v___y_1846_);
lean_ctor_set(v___x_1850_, 3, v_traceTask_1849_);
v___x_1851_ = lean_array_push(v_snapshotTasks_1845_, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___y_1848_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_io_promise_resolve(v___x_1852_, v_val_1816_);
if (lean_obj_tag(v_next_x3f_1840_) == 1)
{
lean_object* v_val_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_val_1854_ = lean_ctor_get(v_next_x3f_1840_, 0);
lean_inc(v_val_1854_);
lean_dec_ref(v_next_x3f_1840_);
v___x_1855_ = lean_box(0);
v___x_1856_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1855_, v_fst_1817_, v___y_1844_, v_val_1854_, v_val_1818_, v___y_1843_, v_a_1819_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; 
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v_next_x3f_1840_);
lean_dec_ref(v_fst_1817_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
}
v___jp_1858_:
{
lean_object* v_snapshotTasks_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_snapshotTasks_1865_ = lean_ctor_get(v___y_1859_, 10);
lean_inc_ref(v_snapshotTasks_1865_);
v___x_1866_ = lean_mk_empty_array_with_capacity(v___y_1863_);
lean_dec(v___y_1863_);
lean_inc_ref(v___y_1864_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___y_1864_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_task_pure(v___x_1867_);
v___y_1843_ = v___y_1860_;
v___y_1844_ = v___y_1859_;
v_snapshotTasks_1845_ = v_snapshotTasks_1865_;
v___y_1846_ = v___y_1862_;
v___y_1847_ = v___y_1861_;
v___y_1848_ = v___y_1864_;
v_traceTask_1849_ = v___x_1868_;
goto v___jp_1842_;
}
v___jp_1869_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_opts_1908_; uint8_t v_hasTrace_1909_; 
v___x_1899_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1880_);
v___x_1900_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1900_, 0, v___y_1888_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
lean_ctor_set(v___x_1900_, 2, v___y_1895_);
lean_ctor_set(v___x_1900_, 3, v_traceState_1883_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*4, v_val_1818_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_reportedCmdState_1898_);
v___x_1902_ = lean_io_promise_resolve(v___x_1901_, v_val_1825_);
v___x_1903_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1882_);
lean_inc(v___y_1892_);
v___x_1904_ = l_BaseIO_chainTask___redArg(v___x_1903_, v___y_1897_, v___y_1892_, v___x_1822_);
v___x_1905_ = l_Lean_inheritedTraceOptions;
v___x_1906_ = lean_st_ref_get(v___x_1905_);
v___x_1907_ = l_List_head_x21___redArg(v___x_1829_, v_scopes_1881_);
lean_dec(v_scopes_1881_);
lean_dec_ref(v___x_1829_);
v_opts_1908_ = lean_ctor_get(v___x_1907_, 1);
lean_inc_ref(v_opts_1908_);
lean_dec(v___x_1907_);
v_hasTrace_1909_ = lean_ctor_get_uint8(v_opts_1908_, sizeof(void*)*1);
if (v_hasTrace_1909_ == 0)
{
lean_dec_ref(v_opts_1908_);
lean_dec(v___x_1906_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v_snapshotTasks_1884_);
lean_dec_ref(v_env_1879_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v_pos_1833_);
lean_dec_ref(v___f_1832_);
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec(v___x_1821_);
v___y_1859_ = v___y_1878_;
v___y_1860_ = v___y_1885_;
v___y_1861_ = v___y_1886_;
v___y_1862_ = v___y_1887_;
v___y_1863_ = v___y_1892_;
v___y_1864_ = v___y_1889_;
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
lean_dec_ref(v___y_1896_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v_snapshotTasks_1884_);
lean_dec_ref(v_env_1879_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v_pos_1833_);
lean_dec_ref(v___f_1832_);
lean_dec_ref(v___f_1831_);
lean_dec_ref(v___f_1830_);
lean_dec(v___x_1821_);
v___y_1859_ = v___y_1878_;
v___y_1860_ = v___y_1885_;
v___y_1861_ = v___y_1886_;
v___y_1862_ = v___y_1887_;
v___y_1863_ = v___y_1892_;
v___y_1864_ = v___y_1889_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
lean_inc_n(v___y_1892_, 3);
v___x_1912_ = lean_task_map(v___f_1830_, v___y_1893_, v___y_1892_, v___x_1822_);
lean_inc_n(v___y_1887_, 3);
lean_inc_n(v___y_1891_, 2);
lean_inc_n(v___y_1890_, 2);
v___x_1913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1913_, 0, v___y_1890_);
lean_ctor_set(v___x_1913_, 1, v___y_1891_);
lean_ctor_set(v___x_1913_, 2, v___y_1887_);
lean_ctor_set(v___x_1913_, 3, v___x_1912_);
v___x_1914_ = lean_task_map(v___f_1831_, v___y_1896_, v___y_1892_, v___x_1822_);
v___x_1915_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1915_, 0, v___y_1890_);
lean_ctor_set(v___x_1915_, 1, v___y_1891_);
lean_ctor_set(v___x_1915_, 2, v___y_1887_);
lean_ctor_set(v___x_1915_, 3, v___x_1914_);
v___x_1916_ = lean_task_map(v___f_1832_, v___y_1894_, v___y_1892_, v___x_1822_);
v___x_1917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1917_, 0, v___y_1890_);
lean_ctor_set(v___x_1917_, 1, v___y_1891_);
lean_ctor_set(v___x_1917_, 2, v___y_1887_);
lean_ctor_set(v___x_1917_, 3, v___x_1916_);
v___x_1918_ = lean_unsigned_to_nat(3u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1913_);
v___x_1921_ = lean_array_push(v___x_1920_, v___x_1915_);
v___x_1922_ = lean_array_push(v___x_1921_, v___x_1917_);
v___x_1923_ = l_Array_append___redArg(v___x_1922_, v_snapshotTasks_1884_);
lean_inc_ref(v___y_1889_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___y_1889_);
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
lean_closure_set(v___f_1930_, 1, v___y_1871_);
lean_closure_set(v___f_1930_, 2, v___y_1877_);
lean_closure_set(v___f_1930_, 3, v___x_1926_);
lean_closure_set(v___f_1930_, 4, v___x_1927_);
lean_closure_set(v___f_1930_, 5, v_env_1879_);
lean_closure_set(v___f_1930_, 6, v___y_1870_);
lean_closure_set(v___f_1930_, 7, v___x_1905_);
lean_closure_set(v___f_1930_, 8, v_a_1819_);
lean_closure_set(v___f_1930_, 9, v_opts_1908_);
lean_closure_set(v___f_1930_, 10, v___x_1924_);
lean_closure_set(v___f_1930_, 11, v_pos_1833_);
lean_closure_set(v___f_1930_, 12, v___x_1928_);
lean_closure_set(v___f_1930_, 13, v___y_1875_);
lean_closure_set(v___f_1930_, 14, v___y_1872_);
lean_closure_set(v___f_1930_, 15, v___y_1876_);
lean_closure_set(v___f_1930_, 16, v___y_1873_);
lean_closure_set(v___f_1930_, 17, v___x_1929_);
v___x_1931_ = lean_io_bind_task(v___x_1925_, v___f_1930_, v___y_1892_, v_val_1818_);
v___y_1843_ = v___y_1885_;
v___y_1844_ = v___y_1878_;
v_snapshotTasks_1845_ = v_snapshotTasks_1884_;
v___y_1846_ = v___y_1887_;
v___y_1847_ = v___y_1886_;
v___y_1848_ = v___y_1889_;
v_traceTask_1849_ = v___x_1931_;
goto v___jp_1842_;
}
}
}
v___jp_1932_:
{
lean_object* v_env_1956_; lean_object* v_messages_1957_; lean_object* v_scopes_1958_; lean_object* v_infoState_1959_; lean_object* v_traceState_1960_; lean_object* v_snapshotTasks_1961_; 
v_env_1956_ = lean_ctor_get(v___y_1941_, 0);
lean_inc_ref(v_env_1956_);
v_messages_1957_ = lean_ctor_get(v___y_1941_, 1);
lean_inc_ref(v_messages_1957_);
v_scopes_1958_ = lean_ctor_get(v___y_1941_, 2);
lean_inc(v_scopes_1958_);
v_infoState_1959_ = lean_ctor_get(v___y_1941_, 8);
lean_inc_ref(v_infoState_1959_);
v_traceState_1960_ = lean_ctor_get(v___y_1941_, 9);
lean_inc_ref(v_traceState_1960_);
v_snapshotTasks_1961_ = lean_ctor_get(v___y_1941_, 10);
lean_inc_ref(v_snapshotTasks_1961_);
v___y_1870_ = v___y_1934_;
v___y_1871_ = v___y_1933_;
v___y_1872_ = v___y_1935_;
v___y_1873_ = v___y_1937_;
v___y_1874_ = v___y_1936_;
v___y_1875_ = v___y_1938_;
v___y_1876_ = v___y_1939_;
v___y_1877_ = v___y_1940_;
v___y_1878_ = v___y_1941_;
v_env_1879_ = v_env_1956_;
v_messages_1880_ = v_messages_1957_;
v_scopes_1881_ = v_scopes_1958_;
v_infoState_1882_ = v_infoState_1959_;
v_traceState_1883_ = v_traceState_1960_;
v_snapshotTasks_1884_ = v_snapshotTasks_1961_;
v___y_1885_ = v___y_1942_;
v___y_1886_ = v___y_1943_;
v___y_1887_ = v___y_1944_;
v___y_1888_ = v___y_1945_;
v___y_1889_ = v___y_1946_;
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
lean_inc(v___y_1971_);
lean_inc_n(v_pos_1833_, 2);
lean_inc(v_fst_1834_);
v___x_1988_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1834_, v_cmdState_1835_, v_pos_1833_, v___x_1987_, v___y_1971_, v_a_1819_);
v___x_1989_ = lean_box(v_val_1818_);
v___x_1990_ = lean_box(v___x_1822_);
lean_inc_ref(v_a_1819_);
lean_inc(v___y_1970_);
lean_inc_ref(v___x_1829_);
lean_inc_ref(v___x_1988_);
lean_inc_ref(v___y_1964_);
lean_inc_ref(v___y_1968_);
v___f_1991_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_1991_, 0, v___y_1968_);
lean_closure_set(v___f_1991_, 1, v___y_1964_);
lean_closure_set(v___f_1991_, 2, v___x_1989_);
lean_closure_set(v___f_1991_, 3, v_val_1826_);
lean_closure_set(v___f_1991_, 4, v___x_1988_);
lean_closure_set(v___f_1991_, 5, v___x_1829_);
lean_closure_set(v___f_1991_, 6, v___y_1970_);
lean_closure_set(v___f_1991_, 7, v___x_1990_);
lean_closure_set(v___f_1991_, 8, v_a_1819_);
lean_closure_set(v___f_1991_, 9, v_pos_1833_);
v___x_1992_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1836_, v___x_1837_);
if (v___x_1992_ == 0)
{
lean_dec(v___y_1978_);
lean_dec(v_fst_1834_);
lean_inc_ref(v___x_1988_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1966_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___x_1988_;
v___y_1942_ = v___y_1971_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1973_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___y_1979_;
v___y_1948_ = v___y_1980_;
v___y_1949_ = v___y_1981_;
v___y_1950_ = v___y_1982_;
v___y_1951_ = v___y_1983_;
v___y_1952_ = v___y_1984_;
v___y_1953_ = v___y_1985_;
v___y_1954_ = v___f_1991_;
v_reportedCmdState_1955_ = v___x_1988_;
goto v___jp_1932_;
}
else
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Parser_isTerminalCommand(v_fst_1834_);
if (v___x_1993_ == 0)
{
if (v___x_1992_ == 0)
{
lean_dec(v___y_1978_);
lean_inc_ref(v___x_1988_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1966_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___x_1988_;
v___y_1942_ = v___y_1971_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1973_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___y_1979_;
v___y_1948_ = v___y_1980_;
v___y_1949_ = v___y_1981_;
v___y_1950_ = v___y_1982_;
v___y_1951_ = v___y_1983_;
v___y_1952_ = v___y_1984_;
v___y_1953_ = v___y_1985_;
v___y_1954_ = v___f_1991_;
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
v___x_2000_ = lean_mk_empty_array_with_capacity(v___y_1978_);
lean_dec(v___y_1978_);
lean_inc_ref(v___x_2000_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_inc_n(v___y_1981_, 3);
v___x_2002_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___x_2000_);
lean_ctor_set(v___x_2002_, 2, v___y_1981_);
lean_ctor_set(v___x_2002_, 3, v___y_1981_);
lean_ctor_set_usize(v___x_2002_, 4, v___y_1972_);
v___x_2003_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2002_, 2);
v___x_2004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2002_);
lean_ctor_set(v___x_2004_, 2, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2006_ = l_Lean_Options_empty;
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_mk_empty_array_with_capacity(v___y_1981_);
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
lean_inc_ref(v___y_1976_);
v___x_2016_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2016_, 0, v_env_1994_);
lean_ctor_set(v___x_2016_, 1, v___x_2004_);
lean_ctor_set(v___x_2016_, 2, v___x_2010_);
lean_ctor_set(v___x_2016_, 3, v___x_2003_);
lean_ctor_set(v___x_2016_, 4, v___x_2011_);
lean_ctor_set(v___x_2016_, 5, v___y_1981_);
lean_ctor_set(v___x_2016_, 6, v___x_2012_);
lean_ctor_set(v___x_2016_, 7, v___x_2013_);
lean_ctor_set(v___x_2016_, 8, v___x_2015_);
lean_ctor_set(v___x_2016_, 9, v___y_1976_);
lean_ctor_set(v___x_2016_, 10, v___x_2008_);
v___y_1870_ = v___y_1964_;
v___y_1871_ = v___y_1963_;
v___y_1872_ = v___y_1965_;
v___y_1873_ = v___y_1966_;
v___y_1874_ = v___y_1967_;
v___y_1875_ = v___y_1968_;
v___y_1876_ = v___y_1969_;
v___y_1877_ = v___y_1970_;
v___y_1878_ = v___x_1988_;
v_env_1879_ = v_env_1994_;
v_messages_1880_ = v_messages_1995_;
v_scopes_1881_ = v_scopes_1996_;
v_infoState_1882_ = v_infoState_1997_;
v_traceState_1883_ = v_traceState_1998_;
v_snapshotTasks_1884_ = v_snapshotTasks_1999_;
v___y_1885_ = v___y_1971_;
v___y_1886_ = v___y_1974_;
v___y_1887_ = v___y_1973_;
v___y_1888_ = v___y_1975_;
v___y_1889_ = v___y_1977_;
v___y_1890_ = v___y_1979_;
v___y_1891_ = v___y_1980_;
v___y_1892_ = v___y_1981_;
v___y_1893_ = v___y_1982_;
v___y_1894_ = v___y_1983_;
v___y_1895_ = v___y_1984_;
v___y_1896_ = v___y_1985_;
v___y_1897_ = v___f_1991_;
v_reportedCmdState_1898_ = v___x_2016_;
goto v___jp_1869_;
}
}
else
{
lean_dec(v___y_1978_);
lean_inc_ref(v___x_1988_);
v___y_1933_ = v___y_1963_;
v___y_1934_ = v___y_1964_;
v___y_1935_ = v___y_1965_;
v___y_1936_ = v___y_1967_;
v___y_1937_ = v___y_1966_;
v___y_1938_ = v___y_1968_;
v___y_1939_ = v___y_1969_;
v___y_1940_ = v___y_1970_;
v___y_1941_ = v___x_1988_;
v___y_1942_ = v___y_1971_;
v___y_1943_ = v___y_1974_;
v___y_1944_ = v___y_1973_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___y_1979_;
v___y_1948_ = v___y_1980_;
v___y_1949_ = v___y_1981_;
v___y_1950_ = v___y_1982_;
v___y_1951_ = v___y_1983_;
v___y_1952_ = v___y_1984_;
v___y_1953_ = v___y_1985_;
v___y_1954_ = v___f_1991_;
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
lean_inc(v___x_2020_);
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
lean_inc_n(v___x_1815_, 3);
v___x_2051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2045_);
lean_ctor_set(v___x_2051_, 1, v___x_1815_);
lean_ctor_set(v___x_2051_, 2, v___x_2038_);
lean_ctor_set(v___x_2051_, 3, v___x_2050_);
v___x_2052_ = l_IO_Promise_result_x21___redArg(v_val_1826_);
lean_inc_ref(v___x_2052_);
v___x_2053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2045_);
lean_ctor_set(v___x_2053_, 1, v___x_1815_);
lean_ctor_set(v___x_2053_, 2, v___x_2038_);
lean_ctor_set(v___x_2053_, 3, v___x_2052_);
v___x_2054_ = l_IO_Promise_result_x21___redArg(v_val_1816_);
v___x_2055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2038_);
lean_ctor_set(v___x_2055_, 1, v___x_1815_);
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
if (lean_obj_tag(v_old_x3f_1838_) == 0)
{
lean_inc_ref(v___x_2044_);
lean_inc_ref(v___x_2037_);
v___y_1963_ = v___x_2039_;
v___y_1964_ = v___x_2041_;
v___y_1965_ = v___x_2038_;
v___y_1966_ = v___x_2038_;
v___y_1967_ = v___x_2040_;
v___y_1968_ = v___x_2037_;
v___y_1969_ = v___x_2044_;
v___y_1970_ = v___x_2028_;
v___y_1971_ = v___x_2020_;
v___y_1972_ = v___x_2040_;
v___y_1973_ = v___x_2038_;
v___y_1974_ = v___x_2038_;
v___y_1975_ = v___x_2037_;
v___y_1976_ = v___x_2041_;
v___y_1977_ = v___x_2044_;
v___y_1978_ = v___x_2039_;
v___y_1979_ = v___x_2045_;
v___y_1980_ = v___x_2046_;
v___y_1981_ = v___x_2028_;
v___y_1982_ = v___x_2048_;
v___y_1983_ = v___x_2052_;
v___y_1984_ = v___x_2038_;
v___y_1985_ = v___x_2050_;
v___y_1986_ = v___x_2038_;
goto v___jp_1962_;
}
else
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2070_; 
v_val_2059_ = lean_ctor_get(v_old_x3f_1838_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_old_x3f_1838_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2061_ = v_old_x3f_1838_;
v_isShared_2062_ = v_isSharedCheck_2070_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v_old_x3f_1838_);
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
lean_inc_ref(v___x_2044_);
lean_inc_ref(v___x_2037_);
v___y_1963_ = v___x_2039_;
v___y_1964_ = v___x_2041_;
v___y_1965_ = v___x_2038_;
v___y_1966_ = v___x_2038_;
v___y_1967_ = v___x_2040_;
v___y_1968_ = v___x_2037_;
v___y_1969_ = v___x_2044_;
v___y_1970_ = v___x_2028_;
v___y_1971_ = v___x_2020_;
v___y_1972_ = v___x_2040_;
v___y_1973_ = v___x_2038_;
v___y_1974_ = v___x_2038_;
v___y_1975_ = v___x_2037_;
v___y_1976_ = v___x_2041_;
v___y_1977_ = v___x_2044_;
v___y_1978_ = v___x_2039_;
v___y_1979_ = v___x_2045_;
v___y_1980_ = v___x_2046_;
v___y_1981_ = v___x_2028_;
v___y_1982_ = v___x_2048_;
v___y_1983_ = v___x_2052_;
v___y_1984_ = v___x_2038_;
v___y_1985_ = v___x_2050_;
v___y_1986_ = v___x_2068_;
goto v___jp_1962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(lean_object* v_fst_2083_, uint8_t v_val_2084_, lean_object* v_a_2085_, lean_object* v_snd_2086_, lean_object* v___x_2087_, uint8_t v___x_2088_, lean_object* v_prom_2089_, lean_object* v___x_2090_, lean_object* v___f_2091_, lean_object* v___f_2092_, lean_object* v___f_2093_, lean_object* v_pos_2094_, lean_object* v_fst_2095_, lean_object* v_cmdState_2096_, lean_object* v_opts_2097_, lean_object* v_old_x3f_2098_, lean_object* v_parseCancelTk_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v_snapshotTasks_2112_; lean_object* v___y_2113_; lean_object* v_traceTask_2114_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; size_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v_env_2153_; lean_object* v_messages_2154_; lean_object* v_scopes_2155_; lean_object* v_infoState_2156_; lean_object* v_traceState_2157_; lean_object* v_snapshotTasks_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v_reportedCmdState_2167_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; size_t v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v_reportedCmdState_2226_; lean_object* v___x_2233_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; size_t v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; size_t v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v_fst_2370_; lean_object* v_snd_2371_; uint8_t v___y_2384_; uint8_t v___x_2387_; 
v___x_2101_ = lean_io_promise_new();
v___x_2102_ = lean_io_promise_new();
v___x_2103_ = lean_io_promise_new();
v___x_2104_ = lean_io_promise_new();
v___x_2233_ = l_Lean_internal_cmdlineSnapshots;
v___x_2387_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2097_, v___x_2233_);
if (v___x_2387_ == 0)
{
v___y_2384_ = v___x_2387_;
goto v___jp_2383_;
}
else
{
uint8_t v___x_2388_; 
lean_inc(v_fst_2095_);
v___x_2388_ = l_Lean_Parser_isTerminalCommand(v_fst_2095_);
if (v___x_2388_ == 0)
{
v___y_2384_ = v___x_2387_;
goto v___jp_2383_;
}
else
{
lean_inc_ref(v_fst_2083_);
lean_inc(v_fst_2095_);
v_fst_2370_ = v_fst_2095_;
v_snd_2371_ = v_fst_2083_;
goto v___jp_2369_;
}
}
v___jp_2105_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2115_, 0, v___y_2108_);
lean_ctor_set(v___x_2115_, 1, v___y_2110_);
lean_ctor_set(v___x_2115_, 2, v___y_2107_);
lean_ctor_set(v___x_2115_, 3, v_traceTask_2114_);
v___x_2116_ = lean_array_push(v_snapshotTasks_2112_, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___y_2106_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_io_promise_resolve(v___x_2117_, v___x_2104_);
lean_dec(v___x_2104_);
if (lean_obj_tag(v___y_2113_) == 1)
{
lean_object* v_val_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_val_2119_ = lean_ctor_get(v___y_2113_, 0);
lean_inc(v_val_2119_);
lean_dec_ref(v___y_2113_);
v___x_2120_ = lean_box(0);
v___x_2121_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2120_, v_fst_2083_, v___y_2111_, v_val_2119_, v_val_2084_, v___y_2109_, v_a_2085_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2109_);
lean_dec_ref(v_fst_2083_);
v___x_2122_ = lean_box(0);
return v___x_2122_;
}
}
v___jp_2123_:
{
lean_object* v_snapshotTasks_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_snapshotTasks_2132_ = lean_ctor_get(v___y_2129_, 10);
lean_inc_ref(v_snapshotTasks_2132_);
v___x_2133_ = lean_mk_empty_array_with_capacity(v___y_2130_);
lean_dec(v___y_2130_);
lean_inc_ref(v___y_2124_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___y_2124_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_task_pure(v___x_2134_);
v___y_2106_ = v___y_2124_;
v___y_2107_ = v___y_2125_;
v___y_2108_ = v___y_2126_;
v___y_2109_ = v___y_2127_;
v___y_2110_ = v___y_2128_;
v___y_2111_ = v___y_2129_;
v_snapshotTasks_2112_ = v_snapshotTasks_2132_;
v___y_2113_ = v___y_2131_;
v_traceTask_2114_ = v___x_2135_;
goto v___jp_2105_;
}
v___jp_2136_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_opts_2177_; uint8_t v_hasTrace_2178_; 
v___x_2168_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2154_);
v___x_2169_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2169_, 0, v___y_2145_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
lean_ctor_set(v___x_2169_, 2, v___y_2151_);
lean_ctor_set(v___x_2169_, 3, v_traceState_2157_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*4, v_val_2084_);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v_reportedCmdState_2167_);
v___x_2171_ = lean_io_promise_resolve(v___x_2170_, v___x_2102_);
lean_dec(v___x_2102_);
v___x_2172_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2156_);
lean_inc(v___y_2159_);
v___x_2173_ = l_BaseIO_chainTask___redArg(v___x_2172_, v___y_2148_, v___y_2159_, v___x_2088_);
v___x_2174_ = l_Lean_inheritedTraceOptions;
v___x_2175_ = lean_st_ref_get(v___x_2174_);
v___x_2176_ = l_List_head_x21___redArg(v___x_2090_, v_scopes_2155_);
lean_dec(v_scopes_2155_);
lean_dec_ref(v___x_2090_);
v_opts_2177_ = lean_ctor_get(v___x_2176_, 1);
lean_inc_ref(v_opts_2177_);
lean_dec(v___x_2176_);
v_hasTrace_2178_ = lean_ctor_get_uint8(v_opts_2177_, sizeof(void*)*1);
if (v_hasTrace_2178_ == 0)
{
lean_dec_ref(v_opts_2177_);
lean_dec(v___x_2175_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_snapshotTasks_2158_);
lean_dec_ref(v_env_2153_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec(v_pos_2094_);
lean_dec_ref(v___f_2093_);
lean_dec_ref(v___f_2092_);
lean_dec_ref(v___f_2091_);
lean_dec(v___x_2087_);
v___y_2124_ = v___y_2146_;
v___y_2125_ = v___y_2161_;
v___y_2126_ = v___y_2150_;
v___y_2127_ = v___y_2162_;
v___y_2128_ = v___y_2163_;
v___y_2129_ = v___y_2152_;
v___y_2130_ = v___y_2159_;
v___y_2131_ = v___y_2160_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__2);
v___x_2180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2175_, v_opts_2177_, v___x_2179_);
lean_dec(v___x_2175_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v_opts_2177_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_snapshotTasks_2158_);
lean_dec_ref(v_env_2153_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec(v_pos_2094_);
lean_dec_ref(v___f_2093_);
lean_dec_ref(v___f_2092_);
lean_dec_ref(v___f_2091_);
lean_dec(v___x_2087_);
v___y_2124_ = v___y_2146_;
v___y_2125_ = v___y_2161_;
v___y_2126_ = v___y_2150_;
v___y_2127_ = v___y_2162_;
v___y_2128_ = v___y_2163_;
v___y_2129_ = v___y_2152_;
v___y_2130_ = v___y_2159_;
v___y_2131_ = v___y_2160_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; 
lean_inc_n(v___y_2159_, 3);
v___x_2181_ = lean_task_map(v___f_2091_, v___y_2147_, v___y_2159_, v___x_2088_);
lean_inc_n(v___y_2161_, 3);
lean_inc_n(v___y_2149_, 2);
lean_inc_n(v___y_2166_, 2);
v___x_2182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2182_, 0, v___y_2166_);
lean_ctor_set(v___x_2182_, 1, v___y_2149_);
lean_ctor_set(v___x_2182_, 2, v___y_2161_);
lean_ctor_set(v___x_2182_, 3, v___x_2181_);
v___x_2183_ = lean_task_map(v___f_2092_, v___y_2165_, v___y_2159_, v___x_2088_);
v___x_2184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2184_, 0, v___y_2166_);
lean_ctor_set(v___x_2184_, 1, v___y_2149_);
lean_ctor_set(v___x_2184_, 2, v___y_2161_);
lean_ctor_set(v___x_2184_, 3, v___x_2183_);
v___x_2185_ = lean_task_map(v___f_2093_, v___y_2164_, v___y_2159_, v___x_2088_);
v___x_2186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2166_);
lean_ctor_set(v___x_2186_, 1, v___y_2149_);
lean_ctor_set(v___x_2186_, 2, v___y_2161_);
lean_ctor_set(v___x_2186_, 3, v___x_2185_);
v___x_2187_ = lean_unsigned_to_nat(3u);
v___x_2188_ = lean_mk_empty_array_with_capacity(v___x_2187_);
v___x_2189_ = lean_array_push(v___x_2188_, v___x_2182_);
v___x_2190_ = lean_array_push(v___x_2189_, v___x_2184_);
v___x_2191_ = lean_array_push(v___x_2190_, v___x_2186_);
v___x_2192_ = l_Array_append___redArg(v___x_2191_, v_snapshotTasks_2158_);
lean_inc_ref(v___y_2146_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___y_2146_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
lean_inc_ref(v___x_2193_);
v___x_2194_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2193_);
v___x_2195_ = lean_box_usize(v___y_2140_);
v___x_2196_ = lean_box(v___x_2088_);
v___x_2197_ = lean_box(v_val_2084_);
v___x_2198_ = lean_box(v___x_2180_);
lean_inc_ref(v_a_2085_);
lean_inc_ref(v___y_2139_);
v___f_2199_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed), 20, 18);
lean_closure_set(v___f_2199_, 0, v___x_2087_);
lean_closure_set(v___f_2199_, 1, v___y_2137_);
lean_closure_set(v___f_2199_, 2, v___y_2143_);
lean_closure_set(v___f_2199_, 3, v___x_2195_);
lean_closure_set(v___f_2199_, 4, v___x_2196_);
lean_closure_set(v___f_2199_, 5, v_env_2153_);
lean_closure_set(v___f_2199_, 6, v___y_2139_);
lean_closure_set(v___f_2199_, 7, v___x_2174_);
lean_closure_set(v___f_2199_, 8, v_a_2085_);
lean_closure_set(v___f_2199_, 9, v_opts_2177_);
lean_closure_set(v___f_2199_, 10, v___x_2193_);
lean_closure_set(v___f_2199_, 11, v_pos_2094_);
lean_closure_set(v___f_2199_, 12, v___x_2197_);
lean_closure_set(v___f_2199_, 13, v___y_2144_);
lean_closure_set(v___f_2199_, 14, v___y_2141_);
lean_closure_set(v___f_2199_, 15, v___y_2142_);
lean_closure_set(v___f_2199_, 16, v___y_2138_);
lean_closure_set(v___f_2199_, 17, v___x_2198_);
v___x_2200_ = lean_io_bind_task(v___x_2194_, v___f_2199_, v___y_2159_, v_val_2084_);
v___y_2106_ = v___y_2146_;
v___y_2107_ = v___y_2161_;
v___y_2108_ = v___y_2150_;
v___y_2109_ = v___y_2162_;
v___y_2110_ = v___y_2163_;
v___y_2111_ = v___y_2152_;
v_snapshotTasks_2112_ = v_snapshotTasks_2158_;
v___y_2113_ = v___y_2160_;
v_traceTask_2114_ = v___x_2200_;
goto v___jp_2105_;
}
}
}
v___jp_2201_:
{
lean_object* v_env_2227_; lean_object* v_messages_2228_; lean_object* v_scopes_2229_; lean_object* v_infoState_2230_; lean_object* v_traceState_2231_; lean_object* v_snapshotTasks_2232_; 
v_env_2227_ = lean_ctor_get(v___y_2217_, 0);
lean_inc_ref(v_env_2227_);
v_messages_2228_ = lean_ctor_get(v___y_2217_, 1);
lean_inc_ref(v_messages_2228_);
v_scopes_2229_ = lean_ctor_get(v___y_2217_, 2);
lean_inc(v_scopes_2229_);
v_infoState_2230_ = lean_ctor_get(v___y_2217_, 8);
lean_inc_ref(v_infoState_2230_);
v_traceState_2231_ = lean_ctor_get(v___y_2217_, 9);
lean_inc_ref(v_traceState_2231_);
v_snapshotTasks_2232_ = lean_ctor_get(v___y_2217_, 10);
lean_inc_ref(v_snapshotTasks_2232_);
v___y_2137_ = v___y_2202_;
v___y_2138_ = v___y_2204_;
v___y_2139_ = v___y_2203_;
v___y_2140_ = v___y_2205_;
v___y_2141_ = v___y_2206_;
v___y_2142_ = v___y_2208_;
v___y_2143_ = v___y_2207_;
v___y_2144_ = v___y_2209_;
v___y_2145_ = v___y_2210_;
v___y_2146_ = v___y_2211_;
v___y_2147_ = v___y_2212_;
v___y_2148_ = v___y_2213_;
v___y_2149_ = v___y_2214_;
v___y_2150_ = v___y_2215_;
v___y_2151_ = v___y_2216_;
v___y_2152_ = v___y_2217_;
v_env_2153_ = v_env_2227_;
v_messages_2154_ = v_messages_2228_;
v_scopes_2155_ = v_scopes_2229_;
v_infoState_2156_ = v_infoState_2230_;
v_traceState_2157_ = v_traceState_2231_;
v_snapshotTasks_2158_ = v_snapshotTasks_2232_;
v___y_2159_ = v___y_2218_;
v___y_2160_ = v___y_2219_;
v___y_2161_ = v___y_2220_;
v___y_2162_ = v___y_2221_;
v___y_2163_ = v___y_2222_;
v___y_2164_ = v___y_2223_;
v___y_2165_ = v___y_2224_;
v___y_2166_ = v___y_2225_;
v_reportedCmdState_2167_ = v_reportedCmdState_2226_;
goto v___jp_2136_;
}
v___jp_2234_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; uint8_t v___x_2266_; 
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___y_2260_);
lean_ctor_set(v___x_2261_, 1, v___x_2101_);
lean_inc(v___y_2255_);
lean_inc_n(v_pos_2094_, 2);
lean_inc(v_fst_2095_);
v___x_2262_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2095_, v_cmdState_2096_, v_pos_2094_, v___x_2261_, v___y_2255_, v_a_2085_);
v___x_2263_ = lean_box(v_val_2084_);
v___x_2264_ = lean_box(v___x_2088_);
lean_inc_ref(v_a_2085_);
lean_inc(v___y_2241_);
lean_inc_ref(v___x_2090_);
lean_inc_ref(v___x_2262_);
lean_inc_ref(v___y_2237_);
lean_inc_ref(v___y_2242_);
v___f_2265_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__7___boxed), 12, 10);
lean_closure_set(v___f_2265_, 0, v___y_2242_);
lean_closure_set(v___f_2265_, 1, v___y_2237_);
lean_closure_set(v___f_2265_, 2, v___x_2263_);
lean_closure_set(v___f_2265_, 3, v___x_2103_);
lean_closure_set(v___f_2265_, 4, v___x_2262_);
lean_closure_set(v___f_2265_, 5, v___x_2090_);
lean_closure_set(v___f_2265_, 6, v___y_2241_);
lean_closure_set(v___f_2265_, 7, v___x_2264_);
lean_closure_set(v___f_2265_, 8, v_a_2085_);
lean_closure_set(v___f_2265_, 9, v_pos_2094_);
v___x_2266_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2097_, v___x_2233_);
if (v___x_2266_ == 0)
{
lean_dec(v___y_2244_);
lean_dec(v_fst_2095_);
lean_inc_ref(v___x_2262_);
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2236_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2240_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2245_;
v___y_2211_ = v___y_2246_;
v___y_2212_ = v___y_2247_;
v___y_2213_ = v___f_2265_;
v___y_2214_ = v___y_2248_;
v___y_2215_ = v___y_2249_;
v___y_2216_ = v___y_2250_;
v___y_2217_ = v___x_2262_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___y_2257_;
v___y_2224_ = v___y_2259_;
v___y_2225_ = v___y_2258_;
v_reportedCmdState_2226_ = v___x_2262_;
goto v___jp_2201_;
}
else
{
uint8_t v___x_2267_; 
v___x_2267_ = l_Lean_Parser_isTerminalCommand(v_fst_2095_);
if (v___x_2267_ == 0)
{
if (v___x_2266_ == 0)
{
lean_dec(v___y_2244_);
lean_inc_ref(v___x_2262_);
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2236_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2240_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2245_;
v___y_2211_ = v___y_2246_;
v___y_2212_ = v___y_2247_;
v___y_2213_ = v___f_2265_;
v___y_2214_ = v___y_2248_;
v___y_2215_ = v___y_2249_;
v___y_2216_ = v___y_2250_;
v___y_2217_ = v___x_2262_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___y_2257_;
v___y_2224_ = v___y_2259_;
v___y_2225_ = v___y_2258_;
v_reportedCmdState_2226_ = v___x_2262_;
goto v___jp_2201_;
}
else
{
lean_object* v_env_2268_; lean_object* v_messages_2269_; lean_object* v_scopes_2270_; lean_object* v_infoState_2271_; lean_object* v_traceState_2272_; lean_object* v_snapshotTasks_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_env_2268_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_ref_n(v_env_2268_, 2);
v_messages_2269_ = lean_ctor_get(v___x_2262_, 1);
lean_inc_ref(v_messages_2269_);
v_scopes_2270_ = lean_ctor_get(v___x_2262_, 2);
lean_inc(v_scopes_2270_);
v_infoState_2271_ = lean_ctor_get(v___x_2262_, 8);
lean_inc_ref(v_infoState_2271_);
v_traceState_2272_ = lean_ctor_get(v___x_2262_, 9);
lean_inc_ref(v_traceState_2272_);
v_snapshotTasks_2273_ = lean_ctor_get(v___x_2262_, 10);
lean_inc_ref(v_snapshotTasks_2273_);
v___x_2274_ = lean_mk_empty_array_with_capacity(v___y_2244_);
lean_dec(v___y_2244_);
lean_inc_ref(v___x_2274_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_inc_n(v___y_2251_, 3);
v___x_2276_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_2274_);
lean_ctor_set(v___x_2276_, 2, v___y_2251_);
lean_ctor_set(v___x_2276_, 3, v___y_2251_);
lean_ctor_set_usize(v___x_2276_, 4, v___y_2254_);
v___x_2277_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2276_, 2);
v___x_2278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2277_);
v___x_2279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2280_ = l_Lean_Options_empty;
v___x_2281_ = lean_box(0);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___y_2251_);
lean_inc_ref_n(v___x_2282_, 2);
lean_inc_n(v___x_2087_, 2);
v___x_2283_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2283_, 0, v___x_2279_);
lean_ctor_set(v___x_2283_, 1, v___x_2280_);
lean_ctor_set(v___x_2283_, 2, v___x_2087_);
lean_ctor_set(v___x_2283_, 3, v___x_2281_);
lean_ctor_set(v___x_2283_, 4, v___x_2281_);
lean_ctor_set(v___x_2283_, 5, v___x_2282_);
lean_ctor_set(v___x_2283_, 6, v___x_2282_);
lean_ctor_set(v___x_2283_, 7, v___x_2281_);
lean_ctor_set(v___x_2283_, 8, v___x_2281_);
lean_ctor_set(v___x_2283_, 9, v___x_2281_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*10, v_val_2084_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*10 + 1, v_val_2084_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*10 + 2, v_val_2084_);
v___x_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
lean_ctor_set(v___x_2284_, 1, v___x_2281_);
v___x_2285_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0);
v___x_2286_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3));
v___x_2287_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2087_);
v___x_2288_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__4);
v___x_2289_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
lean_ctor_set(v___x_2289_, 2, v___x_2276_);
lean_ctor_set_uint8(v___x_2289_, sizeof(void*)*3, v___x_2088_);
lean_inc_ref(v___y_2243_);
v___x_2290_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2290_, 0, v_env_2268_);
lean_ctor_set(v___x_2290_, 1, v___x_2278_);
lean_ctor_set(v___x_2290_, 2, v___x_2284_);
lean_ctor_set(v___x_2290_, 3, v___x_2277_);
lean_ctor_set(v___x_2290_, 4, v___x_2285_);
lean_ctor_set(v___x_2290_, 5, v___y_2251_);
lean_ctor_set(v___x_2290_, 6, v___x_2286_);
lean_ctor_set(v___x_2290_, 7, v___x_2287_);
lean_ctor_set(v___x_2290_, 8, v___x_2289_);
lean_ctor_set(v___x_2290_, 9, v___y_2243_);
lean_ctor_set(v___x_2290_, 10, v___x_2282_);
v___y_2137_ = v___y_2235_;
v___y_2138_ = v___y_2236_;
v___y_2139_ = v___y_2237_;
v___y_2140_ = v___y_2238_;
v___y_2141_ = v___y_2239_;
v___y_2142_ = v___y_2240_;
v___y_2143_ = v___y_2241_;
v___y_2144_ = v___y_2242_;
v___y_2145_ = v___y_2245_;
v___y_2146_ = v___y_2246_;
v___y_2147_ = v___y_2247_;
v___y_2148_ = v___f_2265_;
v___y_2149_ = v___y_2248_;
v___y_2150_ = v___y_2249_;
v___y_2151_ = v___y_2250_;
v___y_2152_ = v___x_2262_;
v_env_2153_ = v_env_2268_;
v_messages_2154_ = v_messages_2269_;
v_scopes_2155_ = v_scopes_2270_;
v_infoState_2156_ = v_infoState_2271_;
v_traceState_2157_ = v_traceState_2272_;
v_snapshotTasks_2158_ = v_snapshotTasks_2273_;
v___y_2159_ = v___y_2251_;
v___y_2160_ = v___y_2252_;
v___y_2161_ = v___y_2253_;
v___y_2162_ = v___y_2255_;
v___y_2163_ = v___y_2256_;
v___y_2164_ = v___y_2257_;
v___y_2165_ = v___y_2259_;
v___y_2166_ = v___y_2258_;
v_reportedCmdState_2167_ = v___x_2290_;
goto v___jp_2136_;
}
}
else
{
lean_dec(v___y_2244_);
lean_inc_ref(v___x_2262_);
v___y_2202_ = v___y_2235_;
v___y_2203_ = v___y_2237_;
v___y_2204_ = v___y_2236_;
v___y_2205_ = v___y_2238_;
v___y_2206_ = v___y_2239_;
v___y_2207_ = v___y_2241_;
v___y_2208_ = v___y_2240_;
v___y_2209_ = v___y_2242_;
v___y_2210_ = v___y_2245_;
v___y_2211_ = v___y_2246_;
v___y_2212_ = v___y_2247_;
v___y_2213_ = v___f_2265_;
v___y_2214_ = v___y_2248_;
v___y_2215_ = v___y_2249_;
v___y_2216_ = v___y_2250_;
v___y_2217_ = v___x_2262_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___y_2257_;
v___y_2224_ = v___y_2259_;
v___y_2225_ = v___y_2258_;
v_reportedCmdState_2226_ = v___x_2262_;
goto v___jp_2201_;
}
}
}
v___jp_2291_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2297_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2086_);
v___x_2298_ = l_IO_CancelToken_new();
v___x_2299_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2087_);
v___x_2300_ = l_Lean_Name_str___override(v___x_2087_, v___x_2299_);
v___x_2301_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2302_ = l_Lean_Name_str___override(v___x_2300_, v___x_2301_);
v___x_2303_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2304_ = l_Lean_Name_str___override(v___x_2302_, v___x_2303_);
v___x_2305_ = l_Lean_Name_str___override(v___x_2304_, v___x_2301_);
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = l_Lean_Name_num___override(v___x_2305_, v___x_2306_);
v___x_2308_ = l_Lean_Name_str___override(v___x_2307_, v___x_2301_);
v___x_2309_ = l_Lean_Name_str___override(v___x_2308_, v___x_2303_);
v___x_2310_ = l_Lean_Name_str___override(v___x_2309_, v___x_2301_);
v___x_2311_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2312_ = l_Lean_Name_str___override(v___x_2310_, v___x_2311_);
v___x_2313_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2314_ = l_Lean_Name_str___override(v___x_2312_, v___x_2313_);
v___x_2315_ = l_Lean_Name_toString(v___x_2314_, v___x_2088_);
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_unsigned_to_nat(32u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
lean_dec_ref(v___x_2318_);
v___x_2319_ = ((size_t)5ULL);
v___x_2320_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2315_, 2);
v___x_2321_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2321_, 0, v___x_2315_);
lean_ctor_set(v___x_2321_, 1, v___x_2297_);
lean_ctor_set(v___x_2321_, 2, v___x_2316_);
lean_ctor_set(v___x_2321_, 3, v___x_2320_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*4, v_val_2084_);
v___x_2322_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2323_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2323_, 0, v___x_2315_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
lean_ctor_set(v___x_2323_, 2, v___x_2316_);
lean_ctor_set(v___x_2323_, 3, v___x_2320_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*4, v_val_2084_);
lean_inc(v___y_2292_);
v___x_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___y_2292_);
v___x_2325_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2324_);
lean_inc(v___x_2298_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2298_);
v___x_2327_ = l_IO_Promise_result_x21___redArg(v___x_2101_);
lean_inc_ref(v___x_2327_);
lean_inc(v___x_2325_);
lean_inc_ref_n(v___x_2324_, 3);
v___x_2328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2324_);
lean_ctor_set(v___x_2328_, 1, v___x_2325_);
lean_ctor_set(v___x_2328_, 2, v___x_2326_);
lean_ctor_set(v___x_2328_, 3, v___x_2327_);
v___x_2329_ = l_IO_Promise_result_x21___redArg(v___x_2102_);
lean_inc_ref(v___x_2329_);
lean_inc_n(v___y_2294_, 3);
v___x_2330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2324_);
lean_ctor_set(v___x_2330_, 1, v___y_2294_);
lean_ctor_set(v___x_2330_, 2, v___x_2316_);
lean_ctor_set(v___x_2330_, 3, v___x_2329_);
v___x_2331_ = l_IO_Promise_result_x21___redArg(v___x_2103_);
lean_inc_ref(v___x_2331_);
v___x_2332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2324_);
lean_ctor_set(v___x_2332_, 1, v___y_2294_);
lean_ctor_set(v___x_2332_, 2, v___x_2316_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
v___x_2333_ = l_IO_Promise_result_x21___redArg(v___x_2104_);
v___x_2334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2316_);
lean_ctor_set(v___x_2334_, 1, v___y_2294_);
lean_ctor_set(v___x_2334_, 2, v___x_2316_);
lean_ctor_set(v___x_2334_, 3, v___x_2333_);
lean_inc_ref(v___x_2323_);
v___x_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2323_);
lean_ctor_set(v___x_2335_, 1, v___x_2328_);
lean_ctor_set(v___x_2335_, 2, v___x_2330_);
lean_ctor_set(v___x_2335_, 3, v___x_2332_);
lean_ctor_set(v___x_2335_, 4, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2321_);
lean_ctor_set(v___x_2336_, 1, v___y_2292_);
lean_ctor_set(v___x_2336_, 2, v___y_2293_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
lean_ctor_set(v___x_2336_, 4, v___y_2296_);
v___x_2337_ = lean_io_promise_resolve(v___x_2336_, v_prom_2089_);
if (lean_obj_tag(v_old_x3f_2098_) == 0)
{
lean_inc_ref(v___x_2315_);
lean_inc_ref(v___x_2323_);
v___y_2235_ = v___x_2317_;
v___y_2236_ = v___x_2316_;
v___y_2237_ = v___x_2320_;
v___y_2238_ = v___x_2319_;
v___y_2239_ = v___x_2316_;
v___y_2240_ = v___x_2323_;
v___y_2241_ = v___x_2306_;
v___y_2242_ = v___x_2315_;
v___y_2243_ = v___x_2320_;
v___y_2244_ = v___x_2317_;
v___y_2245_ = v___x_2315_;
v___y_2246_ = v___x_2323_;
v___y_2247_ = v___x_2327_;
v___y_2248_ = v___x_2325_;
v___y_2249_ = v___x_2316_;
v___y_2250_ = v___x_2316_;
v___y_2251_ = v___x_2306_;
v___y_2252_ = v___y_2295_;
v___y_2253_ = v___x_2316_;
v___y_2254_ = v___x_2319_;
v___y_2255_ = v___x_2298_;
v___y_2256_ = v___y_2294_;
v___y_2257_ = v___x_2331_;
v___y_2258_ = v___x_2324_;
v___y_2259_ = v___x_2329_;
v___y_2260_ = v___x_2316_;
goto v___jp_2234_;
}
else
{
lean_object* v_val_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2349_; 
v_val_2338_ = lean_ctor_get(v_old_x3f_2098_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_old_x3f_2098_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2340_ = v_old_x3f_2098_;
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_val_2338_);
lean_dec(v_old_x3f_2098_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2349_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v_elabSnap_2342_; lean_object* v_stx_2343_; lean_object* v_elabSnap_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v_elabSnap_2342_ = lean_ctor_get(v_val_2338_, 3);
lean_inc_ref(v_elabSnap_2342_);
v_stx_2343_ = lean_ctor_get(v_val_2338_, 1);
lean_inc(v_stx_2343_);
lean_dec(v_val_2338_);
v_elabSnap_2344_ = lean_ctor_get(v_elabSnap_2342_, 1);
lean_inc_ref(v_elabSnap_2344_);
lean_dec_ref(v_elabSnap_2342_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_stx_2343_);
lean_ctor_set(v___x_2345_, 1, v_elabSnap_2344_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2345_);
v___x_2347_ = v___x_2340_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_inc_ref(v___x_2315_);
lean_inc_ref(v___x_2323_);
v___y_2235_ = v___x_2317_;
v___y_2236_ = v___x_2316_;
v___y_2237_ = v___x_2320_;
v___y_2238_ = v___x_2319_;
v___y_2239_ = v___x_2316_;
v___y_2240_ = v___x_2323_;
v___y_2241_ = v___x_2306_;
v___y_2242_ = v___x_2315_;
v___y_2243_ = v___x_2320_;
v___y_2244_ = v___x_2317_;
v___y_2245_ = v___x_2315_;
v___y_2246_ = v___x_2323_;
v___y_2247_ = v___x_2327_;
v___y_2248_ = v___x_2325_;
v___y_2249_ = v___x_2316_;
v___y_2250_ = v___x_2316_;
v___y_2251_ = v___x_2306_;
v___y_2252_ = v___y_2295_;
v___y_2253_ = v___x_2316_;
v___y_2254_ = v___x_2319_;
v___y_2255_ = v___x_2298_;
v___y_2256_ = v___y_2294_;
v___y_2257_ = v___x_2331_;
v___y_2258_ = v___x_2324_;
v___y_2259_ = v___x_2329_;
v___y_2260_ = v___x_2347_;
goto v___jp_2234_;
}
}
}
}
v___jp_2350_:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2353_);
lean_inc(v_fst_2095_);
v___x_2355_ = l_Lean_Parser_isTerminalCommand(v_fst_2095_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; lean_object* v_toProcessingContext_2357_; lean_object* v_pos_2358_; lean_object* v_endPos_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2356_ = lean_io_promise_new();
v_toProcessingContext_2357_ = lean_ctor_get(v_a_2085_, 0);
v_pos_2358_ = lean_ctor_get(v_fst_2083_, 0);
v_endPos_2359_ = lean_ctor_get(v_toProcessingContext_2357_, 3);
lean_inc(v___x_2356_);
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2356_);
v___x_2361_ = lean_box(0);
lean_inc(v_endPos_2359_);
lean_inc(v_pos_2358_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_pos_2358_);
lean_ctor_set(v___x_2362_, 1, v_endPos_2359_);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_parseCancelTk_2099_);
v___x_2365_ = l_IO_Promise_result_x21___redArg(v___x_2356_);
lean_dec(v___x_2356_);
v___x_2366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2361_);
lean_ctor_set(v___x_2366_, 1, v___x_2363_);
lean_ctor_set(v___x_2366_, 2, v___x_2364_);
lean_ctor_set(v___x_2366_, 3, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___y_2292_ = v___y_2351_;
v___y_2293_ = v___y_2352_;
v___y_2294_ = v___x_2354_;
v___y_2295_ = v___x_2360_;
v___y_2296_ = v___x_2367_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2368_; 
lean_dec(v_parseCancelTk_2099_);
v___x_2368_ = lean_box(0);
v___y_2292_ = v___y_2351_;
v___y_2293_ = v___y_2352_;
v___y_2294_ = v___x_2354_;
v___y_2295_ = v___x_2368_;
v___y_2296_ = v___x_2368_;
goto v___jp_2291_;
}
}
v___jp_2369_:
{
lean_object* v___x_2372_; 
lean_inc(v_fst_2095_);
v___x_2372_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2095_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_box(0);
v___y_2351_ = v_fst_2370_;
v___y_2352_ = v_snd_2371_;
v___y_2353_ = v___x_2373_;
goto v___jp_2350_;
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2382_; 
v_val_2374_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2376_ = v___x_2372_;
v_isShared_2377_ = v_isSharedCheck_2382_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_val_2374_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2382_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
lean_inc(v_val_2374_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_val_2374_);
lean_ctor_set(v___x_2378_, 1, v_val_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2378_);
v___x_2380_ = v___x_2376_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
v___y_2351_ = v_fst_2370_;
v___y_2352_ = v_snd_2371_;
v___y_2353_ = v___x_2380_;
goto v___jp_2350_;
}
}
}
}
v___jp_2383_:
{
if (v___y_2384_ == 0)
{
lean_inc_ref(v_fst_2083_);
lean_inc(v_fst_2095_);
v_fst_2370_ = v_fst_2095_;
v_snd_2371_ = v_fst_2083_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_box(0);
v___x_2386_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2370_ = v___x_2385_;
v_snd_2371_ = v___x_2386_;
goto v___jp_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed(lean_object** _args){
lean_object* v_fst_2389_ = _args[0];
lean_object* v_val_2390_ = _args[1];
lean_object* v_a_2391_ = _args[2];
lean_object* v_snd_2392_ = _args[3];
lean_object* v___x_2393_ = _args[4];
lean_object* v___x_2394_ = _args[5];
lean_object* v_prom_2395_ = _args[6];
lean_object* v___x_2396_ = _args[7];
lean_object* v___f_2397_ = _args[8];
lean_object* v___f_2398_ = _args[9];
lean_object* v___f_2399_ = _args[10];
lean_object* v_pos_2400_ = _args[11];
lean_object* v_fst_2401_ = _args[12];
lean_object* v_cmdState_2402_ = _args[13];
lean_object* v_opts_2403_ = _args[14];
lean_object* v_old_x3f_2404_ = _args[15];
lean_object* v_parseCancelTk_2405_ = _args[16];
lean_object* v___y_2406_ = _args[17];
_start:
{
uint8_t v_val_45714__boxed_2407_; uint8_t v___x_45717__boxed_2408_; lean_object* v_res_2409_; 
v_val_45714__boxed_2407_ = lean_unbox(v_val_2390_);
v___x_45717__boxed_2408_ = lean_unbox(v___x_2394_);
v_res_2409_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11(v_fst_2389_, v_val_45714__boxed_2407_, v_a_2391_, v_snd_2392_, v___x_2393_, v___x_45717__boxed_2408_, v_prom_2395_, v___x_2396_, v___f_2397_, v___f_2398_, v___f_2399_, v_pos_2400_, v_fst_2401_, v_cmdState_2402_, v_opts_2403_, v_old_x3f_2404_, v_parseCancelTk_2405_);
lean_dec_ref(v_opts_2403_);
lean_dec(v_prom_2395_);
lean_dec_ref(v_a_2391_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2412_, lean_object* v_parserState_2413_, lean_object* v_cmdState_2414_, lean_object* v_prom_2415_, uint8_t v_sync_2416_, lean_object* v_parseCancelTk_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_toSnapshot_2421_; lean_object* v_stx_2422_; lean_object* v_parserState_2423_; lean_object* v_elabSnap_2424_; lean_object* v_val_2425_; lean_object* v_newParserState_2426_; lean_object* v___y_2460_; lean_object* v___y_2462_; lean_object* v___y_2463_; uint8_t v___y_2464_; lean_object* v___y_2498_; lean_object* v___y_2499_; uint8_t v___y_2500_; lean_object* v___y_2501_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; uint8_t v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; uint8_t v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2532_; lean_object* v___y_2533_; uint8_t v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v_fst_2546_; lean_object* v_snd_2547_; lean_object* v___y_2560_; lean_object* v___y_2561_; uint8_t v___y_2562_; lean_object* v___y_2563_; uint8_t v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; uint8_t v___y_2575_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; 
v___f_2502_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2503_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2504_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2505_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2412_) == 1)
{
lean_object* v_val_2650_; lean_object* v_nextCmdSnap_x3f_2651_; 
v_val_2650_ = lean_ctor_get(v_old_x3f_2412_, 0);
v_nextCmdSnap_x3f_2651_ = lean_ctor_get(v_val_2650_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2651_) == 0)
{
goto v___jp_2617_;
}
else
{
lean_object* v_toSnapshot_2652_; lean_object* v_stx_2653_; lean_object* v_parserState_2654_; lean_object* v_elabSnap_2655_; lean_object* v_val_2656_; lean_object* v___x_2657_; 
v_toSnapshot_2652_ = lean_ctor_get(v_val_2650_, 0);
v_stx_2653_ = lean_ctor_get(v_val_2650_, 1);
v_parserState_2654_ = lean_ctor_get(v_val_2650_, 2);
v_elabSnap_2655_ = lean_ctor_get(v_val_2650_, 3);
v_val_2656_ = lean_ctor_get(v_nextCmdSnap_x3f_2651_, 0);
lean_inc(v_val_2656_);
v___x_2657_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2656_);
if (lean_obj_tag(v___x_2657_) == 1)
{
lean_object* v_val_2658_; lean_object* v_nextCmdSnap_x3f_2659_; 
v_val_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_val_2658_);
lean_dec_ref(v___x_2657_);
v_nextCmdSnap_x3f_2659_ = lean_ctor_get(v_val_2658_, 4);
lean_inc(v_nextCmdSnap_x3f_2659_);
lean_dec(v_val_2658_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2659_) == 0)
{
goto v___jp_2617_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
v_val_2660_ = lean_ctor_get(v_nextCmdSnap_x3f_2659_, 0);
lean_inc(v_val_2660_);
lean_dec_ref(v_nextCmdSnap_x3f_2659_);
v___x_2661_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2660_);
if (lean_obj_tag(v___x_2661_) == 1)
{
lean_object* v_val_2662_; lean_object* v_parserState_2663_; lean_object* v_pos_2664_; uint8_t v___x_2665_; 
v_val_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref(v___x_2661_);
v_parserState_2663_ = lean_ctor_get(v_val_2662_, 2);
lean_inc_ref(v_parserState_2663_);
lean_dec(v_val_2662_);
v_pos_2664_ = lean_ctor_get(v_parserState_2663_, 0);
lean_inc(v_pos_2664_);
lean_dec_ref(v_parserState_2663_);
v___x_2665_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2664_, v_a_2418_);
lean_dec(v_pos_2664_);
if (v___x_2665_ == 0)
{
goto v___jp_2617_;
}
else
{
lean_inc(v_val_2656_);
lean_inc_ref(v_elabSnap_2655_);
lean_inc_ref_n(v_parserState_2654_, 2);
lean_inc(v_stx_2653_);
lean_inc_ref(v_toSnapshot_2652_);
lean_dec_ref(v_old_x3f_2412_);
lean_dec(v_parseCancelTk_2417_);
lean_dec_ref(v_cmdState_2414_);
lean_dec_ref(v_parserState_2413_);
v_toSnapshot_2421_ = v_toSnapshot_2652_;
v_stx_2422_ = v_stx_2653_;
v_parserState_2423_ = v_parserState_2654_;
v_elabSnap_2424_ = v_elabSnap_2655_;
v_val_2425_ = v_val_2656_;
v_newParserState_2426_ = v_parserState_2654_;
goto v___jp_2420_;
}
}
else
{
lean_dec(v___x_2661_);
goto v___jp_2617_;
}
}
}
else
{
lean_dec(v___x_2657_);
goto v___jp_2617_;
}
}
}
else
{
goto v___jp_2617_;
}
v___jp_2420_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_resultSnap_2429_; lean_object* v_task_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2453_; 
v___x_2427_ = lean_io_promise_new();
v___x_2428_ = l_IO_CancelToken_new();
v_resultSnap_2429_ = lean_ctor_get(v_elabSnap_2424_, 2);
lean_inc_ref(v_resultSnap_2429_);
v_task_2430_ = lean_ctor_get(v_resultSnap_2429_, 3);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_resultSnap_2429_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; lean_object* v_unused_2455_; lean_object* v_unused_2456_; 
v_unused_2454_ = lean_ctor_get(v_resultSnap_2429_, 2);
lean_dec(v_unused_2454_);
v_unused_2455_ = lean_ctor_get(v_resultSnap_2429_, 1);
lean_dec(v_unused_2455_);
v_unused_2456_ = lean_ctor_get(v_resultSnap_2429_, 0);
lean_dec(v_unused_2456_);
v___x_2432_ = v_resultSnap_2429_;
v_isShared_2433_ = v_isSharedCheck_2453_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_task_2430_);
lean_dec(v_resultSnap_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2453_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v_toProcessingContext_2439_; lean_object* v_pos_2440_; lean_object* v_endPos_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2434_ = lean_box(v_sync_2416_);
lean_inc_ref(v_a_2418_);
lean_inc(v___x_2428_);
lean_inc(v___x_2427_);
lean_inc_ref(v_newParserState_2426_);
v___f_2435_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 8, 6);
lean_closure_set(v___f_2435_, 0, v_val_2425_);
lean_closure_set(v___f_2435_, 1, v_newParserState_2426_);
lean_closure_set(v___f_2435_, 2, v___x_2427_);
lean_closure_set(v___f_2435_, 3, v___x_2434_);
lean_closure_set(v___f_2435_, 4, v___x_2428_);
lean_closure_set(v___f_2435_, 5, v_a_2418_);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = 1;
v___x_2438_ = l_BaseIO_chainTask___redArg(v_task_2430_, v___f_2435_, v___x_2436_, v___x_2437_);
v_toProcessingContext_2439_ = lean_ctor_get(v_a_2418_, 0);
v_pos_2440_ = lean_ctor_get(v_newParserState_2426_, 0);
lean_inc(v_pos_2440_);
lean_dec_ref(v_newParserState_2426_);
v_endPos_2441_ = lean_ctor_get(v_toProcessingContext_2439_, 3);
v___x_2442_ = lean_box(0);
lean_inc(v_endPos_2441_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v_pos_2440_);
lean_ctor_set(v___x_2443_, 1, v_endPos_2441_);
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
v___x_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2428_);
v___x_2446_ = l_IO_Promise_result_x21___redArg(v___x_2427_);
lean_dec(v___x_2427_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 3, v___x_2446_);
lean_ctor_set(v___x_2432_, 2, v___x_2445_);
lean_ctor_set(v___x_2432_, 1, v___x_2444_);
lean_ctor_set(v___x_2432_, 0, v___x_2442_);
v___x_2448_ = v___x_2432_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
v___x_2450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2450_, 0, v_toSnapshot_2421_);
lean_ctor_set(v___x_2450_, 1, v_stx_2422_);
lean_ctor_set(v___x_2450_, 2, v_parserState_2423_);
lean_ctor_set(v___x_2450_, 3, v_elabSnap_2424_);
lean_ctor_set(v___x_2450_, 4, v___x_2449_);
v___x_2451_ = lean_io_promise_resolve(v___x_2450_, v_prom_2415_);
lean_dec(v_prom_2415_);
return v___x_2451_;
}
}
}
v___jp_2457_:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_box(0);
return v___x_2458_;
}
v___jp_2459_:
{
goto v___jp_2457_;
}
v___jp_2461_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2465_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2466_ = l_Lean_Name_str___override(v___y_2463_, v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2468_ = l_Lean_Name_str___override(v___x_2466_, v___x_2467_);
v___x_2469_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2470_ = l_Lean_Name_str___override(v___x_2468_, v___x_2469_);
v___x_2471_ = l_Lean_Name_str___override(v___x_2470_, v___x_2467_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = l_Lean_Name_num___override(v___x_2471_, v___x_2472_);
v___x_2474_ = l_Lean_Name_str___override(v___x_2473_, v___x_2467_);
v___x_2475_ = l_Lean_Name_str___override(v___x_2474_, v___x_2469_);
v___x_2476_ = l_Lean_Name_str___override(v___x_2475_, v___x_2467_);
v___x_2477_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2478_ = l_Lean_Name_str___override(v___x_2476_, v___x_2477_);
v___x_2479_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___closed__5));
v___x_2480_ = l_Lean_Name_str___override(v___x_2478_, v___x_2479_);
v___x_2481_ = l_Lean_Name_toString(v___x_2480_, v___y_2464_);
v___x_2482_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2485_ = 0;
v___x_2486_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2486_, 0, v___x_2481_);
lean_ctor_set(v___x_2486_, 1, v___x_2482_);
lean_ctor_set(v___x_2486_, 2, v___x_2483_);
lean_ctor_set(v___x_2486_, 3, v___x_2484_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*4, v___x_2485_);
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2486_, 3);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2486_);
lean_ctor_set(v___x_2489_, 1, v_cmdState_2414_);
v___x_2490_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2483_, v___x_2489_);
v___x_2491_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2483_, v___x_2486_);
v___x_2492_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2486_);
lean_ctor_set(v___x_2493_, 1, v___x_2488_);
lean_ctor_set(v___x_2493_, 2, v___x_2490_);
lean_ctor_set(v___x_2493_, 3, v___x_2491_);
lean_ctor_set(v___x_2493_, 4, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2486_);
lean_ctor_set(v___x_2494_, 1, v___x_2487_);
lean_ctor_set(v___x_2494_, 2, v___y_2462_);
lean_ctor_set(v___x_2494_, 3, v___x_2493_);
lean_ctor_set(v___x_2494_, 4, v___x_2483_);
v___x_2495_ = lean_io_promise_resolve(v___x_2494_, v_prom_2415_);
lean_dec(v_prom_2415_);
v___x_2496_ = lean_box(0);
return v___x_2496_;
}
v___jp_2497_:
{
v___y_2462_ = v___y_2498_;
v___y_2463_ = v___y_2499_;
v___y_2464_ = v___y_2500_;
goto v___jp_2461_;
}
v___jp_2506_:
{
lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2524_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2523_);
v___x_2525_ = l_Lean_Parser_isTerminalCommand(v___y_2509_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_io_promise_new();
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
v___x_2528_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2524_, v___y_2515_, v___y_2514_, v___y_2510_, v_a_2418_, v___y_2522_, v___y_2516_, v___y_2513_, v___y_2518_, v___y_2507_, v___y_2519_, v___y_2520_, v___y_2512_, v_prom_2415_, v___x_2505_, v___f_2504_, v___f_2503_, v___f_2502_, v___y_2517_, v___y_2521_, v_cmdState_2414_, v___y_2508_, v___y_2511_, v_old_x3f_2412_, v_parseCancelTk_2417_, v___x_2527_);
lean_dec_ref(v___y_2508_);
lean_dec(v_prom_2415_);
lean_dec(v___y_2519_);
lean_dec(v___y_2515_);
v___y_2460_ = v___x_2528_;
goto v___jp_2459_;
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_box(0);
v___x_2530_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2524_, v___y_2515_, v___y_2514_, v___y_2510_, v_a_2418_, v___y_2522_, v___y_2516_, v___y_2513_, v___y_2518_, v___y_2507_, v___y_2519_, v___y_2520_, v___y_2512_, v_prom_2415_, v___x_2505_, v___f_2504_, v___f_2503_, v___f_2502_, v___y_2517_, v___y_2521_, v_cmdState_2414_, v___y_2508_, v___y_2511_, v_old_x3f_2412_, v_parseCancelTk_2417_, v___x_2529_);
lean_dec_ref(v___y_2508_);
lean_dec(v_prom_2415_);
lean_dec(v___y_2519_);
lean_dec(v___y_2515_);
v___y_2460_ = v___x_2530_;
goto v___jp_2459_;
}
}
v___jp_2531_:
{
lean_object* v___x_2548_; 
lean_inc(v___y_2545_);
v___x_2548_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2545_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_box(0);
v___y_2507_ = v___y_2532_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2545_;
v___y_2510_ = v___y_2534_;
v___y_2511_ = v___y_2535_;
v___y_2512_ = v_snd_2547_;
v___y_2513_ = v___y_2536_;
v___y_2514_ = v___y_2537_;
v___y_2515_ = v___y_2538_;
v___y_2516_ = v___y_2539_;
v___y_2517_ = v___y_2540_;
v___y_2518_ = v_fst_2546_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2542_;
v___y_2521_ = v___y_2543_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___x_2549_;
goto v___jp_2506_;
}
else
{
lean_object* v_val_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
v_val_2550_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v___x_2548_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_val_2550_);
lean_dec(v___x_2548_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_inc(v_val_2550_);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_val_2550_);
lean_ctor_set(v___x_2554_, 1, v_val_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
v___y_2507_ = v___y_2532_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2545_;
v___y_2510_ = v___y_2534_;
v___y_2511_ = v___y_2535_;
v___y_2512_ = v_snd_2547_;
v___y_2513_ = v___y_2536_;
v___y_2514_ = v___y_2537_;
v___y_2515_ = v___y_2538_;
v___y_2516_ = v___y_2539_;
v___y_2517_ = v___y_2540_;
v___y_2518_ = v_fst_2546_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2542_;
v___y_2521_ = v___y_2543_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___x_2556_;
goto v___jp_2506_;
}
}
}
}
v___jp_2559_:
{
if (v___y_2575_ == 0)
{
lean_inc(v___y_2574_);
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
v___y_2545_ = v___y_2574_;
v_fst_2546_ = v___y_2574_;
v_snd_2547_ = v___y_2573_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref(v___y_2573_);
v___x_2576_ = lean_box(0);
v___x_2577_ = l_Lean_Parser_instInhabitedModuleParserState_default;
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
v___y_2545_ = v___y_2574_;
v_fst_2546_ = v___x_2576_;
v_snd_2547_ = v___x_2577_;
goto v___jp_2531_;
}
}
v___jp_2578_:
{
uint8_t v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = l_IO_CancelToken_isSet(v_parseCancelTk_2417_);
v___x_2590_ = 1;
if (v___x_2589_ == 0)
{
lean_dec(v___y_2587_);
if (v_sync_2416_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2591_ = lean_io_promise_new();
v___x_2592_ = lean_io_promise_new();
v___x_2593_ = lean_io_promise_new();
v___x_2594_ = lean_io_promise_new();
v___x_2595_ = l_Lean_internal_cmdlineSnapshots;
v___x_2596_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2586_, v___x_2595_);
lean_dec_ref(v___y_2586_);
if (v___x_2596_ == 0)
{
v___y_2560_ = v___x_2591_;
v___y_2561_ = v___y_2580_;
v___y_2562_ = v___x_2589_;
v___y_2563_ = v___x_2595_;
v___y_2564_ = v___x_2590_;
v___y_2565_ = v___y_2579_;
v___y_2566_ = v___x_2594_;
v___y_2567_ = v___y_2581_;
v___y_2568_ = v___y_2582_;
v___y_2569_ = v___x_2592_;
v___y_2570_ = v___x_2593_;
v___y_2571_ = v___y_2583_;
v___y_2572_ = v___y_2584_;
v___y_2573_ = v___y_2585_;
v___y_2574_ = v___y_2588_;
v___y_2575_ = v___x_2596_;
goto v___jp_2559_;
}
else
{
uint8_t v___x_2597_; 
lean_inc(v___y_2588_);
v___x_2597_ = l_Lean_Parser_isTerminalCommand(v___y_2588_);
if (v___x_2597_ == 0)
{
v___y_2560_ = v___x_2591_;
v___y_2561_ = v___y_2580_;
v___y_2562_ = v___x_2589_;
v___y_2563_ = v___x_2595_;
v___y_2564_ = v___x_2590_;
v___y_2565_ = v___y_2579_;
v___y_2566_ = v___x_2594_;
v___y_2567_ = v___y_2581_;
v___y_2568_ = v___y_2582_;
v___y_2569_ = v___x_2592_;
v___y_2570_ = v___x_2593_;
v___y_2571_ = v___y_2583_;
v___y_2572_ = v___y_2584_;
v___y_2573_ = v___y_2585_;
v___y_2574_ = v___y_2588_;
v___y_2575_ = v___x_2596_;
goto v___jp_2559_;
}
else
{
lean_inc(v___y_2588_);
v___y_2532_ = v___x_2591_;
v___y_2533_ = v___y_2580_;
v___y_2534_ = v___x_2589_;
v___y_2535_ = v___x_2595_;
v___y_2536_ = v___x_2590_;
v___y_2537_ = v___y_2579_;
v___y_2538_ = v___x_2594_;
v___y_2539_ = v___y_2581_;
v___y_2540_ = v___y_2582_;
v___y_2541_ = v___x_2592_;
v___y_2542_ = v___x_2593_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2588_;
v_fst_2546_ = v___y_2588_;
v_snd_2547_ = v___y_2585_;
goto v___jp_2531_;
}
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
v___x_2598_ = lean_box(v___x_2589_);
v___x_2599_ = lean_box(v___x_2590_);
lean_inc_ref(v_a_2418_);
v___f_2600_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__11___boxed), 18, 17);
lean_closure_set(v___f_2600_, 0, v___y_2579_);
lean_closure_set(v___f_2600_, 1, v___x_2598_);
lean_closure_set(v___f_2600_, 2, v_a_2418_);
lean_closure_set(v___f_2600_, 3, v___y_2584_);
lean_closure_set(v___f_2600_, 4, v___y_2581_);
lean_closure_set(v___f_2600_, 5, v___x_2599_);
lean_closure_set(v___f_2600_, 6, v_prom_2415_);
lean_closure_set(v___f_2600_, 7, v___x_2505_);
lean_closure_set(v___f_2600_, 8, v___f_2504_);
lean_closure_set(v___f_2600_, 9, v___f_2503_);
lean_closure_set(v___f_2600_, 10, v___f_2502_);
lean_closure_set(v___f_2600_, 11, v___y_2582_);
lean_closure_set(v___f_2600_, 12, v___y_2583_);
lean_closure_set(v___f_2600_, 13, v_cmdState_2414_);
lean_closure_set(v___f_2600_, 14, v___y_2580_);
lean_closure_set(v___f_2600_, 15, v_old_x3f_2412_);
lean_closure_set(v___f_2600_, 16, v_parseCancelTk_2417_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = lean_io_as_task(v___f_2600_, v___x_2601_);
lean_dec_ref(v___x_2602_);
goto v___jp_2457_;
}
}
else
{
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v_parseCancelTk_2417_);
if (lean_obj_tag(v_old_x3f_2412_) == 1)
{
lean_object* v_val_2603_; lean_object* v___x_2604_; lean_object* v_children_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_val_2603_ = lean_ctor_get(v_old_x3f_2412_, 0);
lean_inc(v_val_2603_);
lean_dec_ref(v_old_x3f_2412_);
v___x_2604_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_val_2603_);
v_children_2605_ = lean_ctor_get(v___x_2604_, 1);
lean_inc_ref(v_children_2605_);
lean_dec_ref(v___x_2604_);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_array_get_size(v_children_2605_);
v___x_2608_ = lean_nat_dec_lt(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec_ref(v_children_2605_);
v___y_2462_ = v___y_2585_;
v___y_2463_ = v___y_2587_;
v___y_2464_ = v___x_2590_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = lean_box(0);
v___x_2610_ = lean_nat_dec_le(v___x_2607_, v___x_2607_);
if (v___x_2610_ == 0)
{
if (v___x_2608_ == 0)
{
lean_dec_ref(v_children_2605_);
v___y_2462_ = v___y_2585_;
v___y_2463_ = v___y_2587_;
v___y_2464_ = v___x_2590_;
goto v___jp_2461_;
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = lean_usize_of_nat(v___x_2607_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2605_, v___x_2611_, v___x_2612_, v___x_2609_);
lean_dec_ref(v_children_2605_);
v___y_2498_ = v___y_2585_;
v___y_2499_ = v___y_2587_;
v___y_2500_ = v___x_2590_;
v___y_2501_ = v___x_2613_;
goto v___jp_2497_;
}
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2607_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_children_2605_, v___x_2614_, v___x_2615_, v___x_2609_);
lean_dec_ref(v_children_2605_);
v___y_2498_ = v___y_2585_;
v___y_2499_ = v___y_2587_;
v___y_2500_ = v___x_2590_;
v___y_2501_ = v___x_2616_;
goto v___jp_2497_;
}
}
}
else
{
lean_dec(v_old_x3f_2412_);
v___y_2462_ = v___y_2585_;
v___y_2463_ = v___y_2587_;
v___y_2464_ = v___x_2590_;
goto v___jp_2461_;
}
}
}
v___jp_2617_:
{
lean_object* v_env_2618_; lean_object* v_scopes_2619_; lean_object* v___x_2620_; lean_object* v_opts_2621_; lean_object* v_currNamespace_2622_; lean_object* v_openDecls_2623_; lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v_snd_2629_; 
v_env_2618_ = lean_ctor_get(v_cmdState_2414_, 0);
v_scopes_2619_ = lean_ctor_get(v_cmdState_2414_, 2);
v___x_2620_ = l_List_head_x21___redArg(v___x_2505_, v_scopes_2619_);
v_opts_2621_ = lean_ctor_get(v___x_2620_, 1);
lean_inc_ref_n(v_opts_2621_, 2);
v_currNamespace_2622_ = lean_ctor_get(v___x_2620_, 2);
lean_inc(v_currNamespace_2622_);
v_openDecls_2623_ = lean_ctor_get(v___x_2620_, 3);
lean_inc(v_openDecls_2623_);
lean_dec(v___x_2620_);
lean_inc_ref(v_env_2618_);
v___x_2624_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2624_, 0, v_env_2618_);
lean_ctor_set(v___x_2624_, 1, v_opts_2621_);
lean_ctor_set(v___x_2624_, 2, v_currNamespace_2622_);
lean_ctor_set(v___x_2624_, 3, v_openDecls_2623_);
lean_inc_ref(v_parserState_2413_);
lean_inc_ref(v_a_2418_);
v___f_2625_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2625_, 0, v_a_2418_);
lean_closure_set(v___f_2625_, 1, v___x_2624_);
lean_closure_set(v___f_2625_, 2, v_parserState_2413_);
v___x_2626_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2627_ = lean_box(0);
v___x_2628_ = lean_profileit(v___x_2626_, v_opts_2621_, v___f_2625_, v___x_2627_);
v_snd_2629_ = lean_ctor_get(v___x_2628_, 1);
lean_inc(v_snd_2629_);
if (lean_obj_tag(v_old_x3f_2412_) == 1)
{
lean_object* v_val_2630_; lean_object* v_fst_2631_; lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v_pos_2634_; lean_object* v_toSnapshot_2635_; lean_object* v_stx_2636_; lean_object* v_parserState_2637_; lean_object* v_elabSnap_2638_; lean_object* v_nextCmdSnap_x3f_2639_; uint8_t v___x_2640_; 
v_val_2630_ = lean_ctor_get(v_old_x3f_2412_, 0);
v_fst_2631_ = lean_ctor_get(v___x_2628_, 0);
lean_inc_n(v_fst_2631_, 2);
lean_dec(v___x_2628_);
v_fst_2632_ = lean_ctor_get(v_snd_2629_, 0);
lean_inc(v_fst_2632_);
v_snd_2633_ = lean_ctor_get(v_snd_2629_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_snd_2629_);
v_pos_2634_ = lean_ctor_get(v_parserState_2413_, 0);
lean_inc(v_pos_2634_);
lean_dec_ref(v_parserState_2413_);
v_toSnapshot_2635_ = lean_ctor_get(v_val_2630_, 0);
v_stx_2636_ = lean_ctor_get(v_val_2630_, 1);
v_parserState_2637_ = lean_ctor_get(v_val_2630_, 2);
v_elabSnap_2638_ = lean_ctor_get(v_val_2630_, 3);
v_nextCmdSnap_x3f_2639_ = lean_ctor_get(v_val_2630_, 4);
lean_inc(v_stx_2636_);
v___x_2640_ = l_Lean_Syntax_eqWithInfo(v_fst_2631_, v_stx_2636_);
if (v___x_2640_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2639_) == 0)
{
lean_inc(v_fst_2631_);
lean_inc_ref(v_opts_2621_);
lean_inc(v_fst_2632_);
v___y_2579_ = v_fst_2632_;
v___y_2580_ = v_opts_2621_;
v___y_2581_ = v___x_2627_;
v___y_2582_ = v_pos_2634_;
v___y_2583_ = v_fst_2631_;
v___y_2584_ = v_snd_2633_;
v___y_2585_ = v_fst_2632_;
v___y_2586_ = v_opts_2621_;
v___y_2587_ = v___x_2627_;
v___y_2588_ = v_fst_2631_;
goto v___jp_2578_;
}
else
{
lean_object* v_val_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_val_2641_ = lean_ctor_get(v_nextCmdSnap_x3f_2639_, 0);
v___x_2642_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2641_);
v___x_2643_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2642_, v_val_2641_);
lean_inc(v_fst_2631_);
lean_inc_ref(v_opts_2621_);
lean_inc(v_fst_2632_);
v___y_2579_ = v_fst_2632_;
v___y_2580_ = v_opts_2621_;
v___y_2581_ = v___x_2627_;
v___y_2582_ = v_pos_2634_;
v___y_2583_ = v_fst_2631_;
v___y_2584_ = v_snd_2633_;
v___y_2585_ = v_fst_2632_;
v___y_2586_ = v_opts_2621_;
v___y_2587_ = v___x_2627_;
v___y_2588_ = v_fst_2631_;
goto v___jp_2578_;
}
}
else
{
lean_inc(v_val_2630_);
lean_dec(v_pos_2634_);
lean_dec(v_snd_2633_);
lean_dec(v_fst_2631_);
lean_dec_ref(v_old_x3f_2412_);
lean_dec_ref(v_opts_2621_);
lean_dec(v_parseCancelTk_2417_);
lean_dec_ref(v_cmdState_2414_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2639_) == 1)
{
lean_object* v_val_2644_; 
lean_inc_ref(v_nextCmdSnap_x3f_2639_);
lean_inc_ref(v_elabSnap_2638_);
lean_inc_ref(v_parserState_2637_);
lean_inc(v_stx_2636_);
lean_inc_ref(v_toSnapshot_2635_);
lean_dec(v_val_2630_);
v_val_2644_ = lean_ctor_get(v_nextCmdSnap_x3f_2639_, 0);
lean_inc(v_val_2644_);
lean_dec_ref(v_nextCmdSnap_x3f_2639_);
v_toSnapshot_2421_ = v_toSnapshot_2635_;
v_stx_2422_ = v_stx_2636_;
v_parserState_2423_ = v_parserState_2637_;
v_elabSnap_2424_ = v_elabSnap_2638_;
v_val_2425_ = v_val_2644_;
v_newParserState_2426_ = v_fst_2632_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2645_; 
lean_dec(v_fst_2632_);
v___x_2645_ = lean_io_promise_resolve(v_val_2630_, v_prom_2415_);
lean_dec(v_prom_2415_);
return v___x_2645_;
}
}
}
else
{
lean_object* v_fst_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v_pos_2649_; 
v_fst_2646_ = lean_ctor_get(v___x_2628_, 0);
lean_inc_n(v_fst_2646_, 2);
lean_dec(v___x_2628_);
v_fst_2647_ = lean_ctor_get(v_snd_2629_, 0);
lean_inc_n(v_fst_2647_, 2);
v_snd_2648_ = lean_ctor_get(v_snd_2629_, 1);
lean_inc(v_snd_2648_);
lean_dec(v_snd_2629_);
v_pos_2649_ = lean_ctor_get(v_parserState_2413_, 0);
lean_inc(v_pos_2649_);
lean_dec_ref(v_parserState_2413_);
lean_inc_ref(v_opts_2621_);
v___y_2579_ = v_fst_2647_;
v___y_2580_ = v_opts_2621_;
v___y_2581_ = v___x_2627_;
v___y_2582_ = v_pos_2649_;
v___y_2583_ = v_fst_2646_;
v___y_2584_ = v_snd_2648_;
v___y_2585_ = v_fst_2647_;
v___y_2586_ = v_opts_2621_;
v___y_2587_ = v___x_2627_;
v___y_2588_ = v_fst_2646_;
goto v___jp_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__6(lean_object* v_oldResult_2666_, lean_object* v_newParserState_2667_, lean_object* v_val_2668_, uint8_t v_sync_2669_, lean_object* v_val_2670_, lean_object* v_a_2671_, lean_object* v_oldNext_2672_){
_start:
{
lean_object* v_cmdState_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_cmdState_2674_ = lean_ctor_get(v_oldResult_2666_, 1);
lean_inc_ref(v_cmdState_2674_);
lean_dec_ref(v_oldResult_2666_);
v___x_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_oldNext_2672_);
v___x_2676_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2675_, v_newParserState_2667_, v_cmdState_2674_, v_val_2668_, v_sync_2669_, v_val_2670_, v_a_2671_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v___x_2677_ = _args[0];
lean_object* v_val_2678_ = _args[1];
lean_object* v_fst_2679_ = _args[2];
lean_object* v_val_2680_ = _args[3];
lean_object* v_a_2681_ = _args[4];
lean_object* v_snd_2682_ = _args[5];
lean_object* v___x_2683_ = _args[6];
lean_object* v___x_2684_ = _args[7];
lean_object* v_fst_2685_ = _args[8];
lean_object* v_val_2686_ = _args[9];
lean_object* v_val_2687_ = _args[10];
lean_object* v_val_2688_ = _args[11];
lean_object* v_snd_2689_ = _args[12];
lean_object* v_prom_2690_ = _args[13];
lean_object* v___x_2691_ = _args[14];
lean_object* v___f_2692_ = _args[15];
lean_object* v___f_2693_ = _args[16];
lean_object* v___f_2694_ = _args[17];
lean_object* v_pos_2695_ = _args[18];
lean_object* v_fst_2696_ = _args[19];
lean_object* v_cmdState_2697_ = _args[20];
lean_object* v_opts_2698_ = _args[21];
lean_object* v___x_2699_ = _args[22];
lean_object* v_old_x3f_2700_ = _args[23];
lean_object* v_parseCancelTk_2701_ = _args[24];
lean_object* v_next_x3f_2702_ = _args[25];
lean_object* v___y_2703_ = _args[26];
_start:
{
uint8_t v_val_45499__boxed_2704_; uint8_t v___x_45502__boxed_2705_; lean_object* v_res_2706_; 
v_val_45499__boxed_2704_ = lean_unbox(v_val_2680_);
v___x_45502__boxed_2705_ = lean_unbox(v___x_2684_);
v_res_2706_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v___x_2677_, v_val_2678_, v_fst_2679_, v_val_45499__boxed_2704_, v_a_2681_, v_snd_2682_, v___x_2683_, v___x_45502__boxed_2705_, v_fst_2685_, v_val_2686_, v_val_2687_, v_val_2688_, v_snd_2689_, v_prom_2690_, v___x_2691_, v___f_2692_, v___f_2693_, v___f_2694_, v_pos_2695_, v_fst_2696_, v_cmdState_2697_, v_opts_2698_, v___x_2699_, v_old_x3f_2700_, v_parseCancelTk_2701_, v_next_x3f_2702_);
lean_dec_ref(v___x_2699_);
lean_dec_ref(v_opts_2698_);
lean_dec(v_prom_2690_);
lean_dec(v_val_2687_);
lean_dec_ref(v_a_2681_);
lean_dec(v_val_2678_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2707_, lean_object* v_parserState_2708_, lean_object* v_cmdState_2709_, lean_object* v_prom_2710_, lean_object* v_sync_2711_, lean_object* v_parseCancelTk_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v_sync_boxed_2715_; lean_object* v_res_2716_; 
v_sync_boxed_2715_ = lean_unbox(v_sync_2711_);
v_res_2716_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2707_, v_parserState_2708_, v_cmdState_2709_, v_prom_2710_, v_sync_boxed_2715_, v_parseCancelTk_2712_, v_a_2713_);
lean_dec_ref(v_a_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_as_2717_, size_t v_i_2718_, size_t v_stop_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___redArg(v_as_2717_, v_i_2718_, v_stop_2719_, v_b_2720_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2___boxed(lean_object* v_as_2724_, lean_object* v_i_2725_, lean_object* v_stop_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
size_t v_i_boxed_2730_; size_t v_stop_boxed_2731_; lean_object* v_res_2732_; 
v_i_boxed_2730_ = lean_unbox_usize(v_i_2725_);
lean_dec(v_i_2725_);
v_stop_boxed_2731_ = lean_unbox_usize(v_stop_2726_);
lean_dec(v_stop_2726_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(v_as_2724_, v_i_boxed_2730_, v_stop_boxed_2731_, v_b_2727_, v___y_2728_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v_as_2724_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2733_, lean_object* v_opt_2734_){
_start:
{
lean_object* v_name_2735_; lean_object* v_map_2736_; lean_object* v___x_2737_; 
v_name_2735_ = lean_ctor_get(v_opt_2734_, 0);
v_map_2736_ = lean_ctor_get(v_opts_2733_, 0);
v___x_2737_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2736_, v_name_2735_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_box(0);
return v___x_2738_;
}
else
{
lean_object* v_val_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2748_; 
v_val_2739_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2741_ = v___x_2737_;
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_val_2739_);
lean_dec(v___x_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
if (lean_obj_tag(v_val_2739_) == 0)
{
lean_object* v_v_2743_; lean_object* v___x_2745_; 
v_v_2743_ = lean_ctor_get(v_val_2739_, 0);
lean_inc_ref(v_v_2743_);
lean_dec_ref(v_val_2739_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v_v_2743_);
v___x_2745_ = v___x_2741_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_v_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
else
{
lean_object* v___x_2747_; 
lean_del_object(v___x_2741_);
lean_dec(v_val_2739_);
v___x_2747_ = lean_box(0);
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2749_, lean_object* v_opt_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2749_, v_opt_2750_);
lean_dec_ref(v_opt_2750_);
lean_dec_ref(v_opts_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2752_, lean_object* v_x_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2752_);
v___x_2755_ = lean_box(0);
v___x_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2756_, 0, v_x_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
return v___x_2756_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2763_ = l_Array_toPArray_x27___redArg(v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
if (lean_obj_tag(v_a_2764_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = l_List_reverse___redArg(v_a_2765_);
return v___x_2766_;
}
else
{
lean_object* v_head_2767_; lean_object* v_tail_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2781_; 
v_head_2767_ = lean_ctor_get(v_a_2764_, 0);
v_tail_2768_ = lean_ctor_get(v_a_2764_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_a_2764_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2770_ = v_a_2764_;
v_isShared_2771_ = v_isSharedCheck_2781_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_tail_2768_);
lean_inc(v_head_2767_);
lean_dec(v_a_2764_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2781_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2772_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v_head_2767_);
v___x_2774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
v___x_2775_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 1, v_a_2765_);
lean_ctor_set(v___x_2770_, 0, v___x_2776_);
v___x_2778_ = v___x_2770_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_a_2765_);
v___x_2778_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
v_a_2764_ = v_tail_2768_;
v_a_2765_ = v___x_2778_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2792_; double v___x_2793_; 
v___x_2792_ = lean_unsigned_to_nat(1000000000u);
v___x_2793_ = lean_float_of_nat(v___x_2792_);
return v___x_2793_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2801_ = l_Lean_MessageData_ofFormat(v___x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2802_, lean_object* v_stx_2803_, lean_object* v_origStx_2804_, lean_object* v_toProcessingContext_2805_, lean_object* v___x_2806_, lean_object* v_fileMap_2807_, lean_object* v_parserState_2808_, lean_object* v_a_2809_, lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_toProcessingContext_2814_; lean_object* v___x_2815_; 
v_toProcessingContext_2814_ = lean_ctor_get(v___y_2812_, 0);
lean_inc_ref(v_toProcessingContext_2814_);
lean_inc(v_stx_2803_);
v___x_2815_ = lean_apply_3(v_setupImports_2802_, v_stx_2803_, v_toProcessingContext_2814_, lean_box(0));
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_3025_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_3025_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_3025_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
if (lean_obj_tag(v_a_2816_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; 
lean_dec_ref(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_parserState_2808_);
lean_dec_ref(v_fileMap_2807_);
lean_dec(v___x_2806_);
lean_dec_ref(v_toProcessingContext_2805_);
lean_dec(v_origStx_2804_);
lean_dec(v_stx_2803_);
v_a_2820_ = lean_ctor_get(v_a_2816_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_a_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_3024_; 
v_a_2824_ = lean_ctor_get(v_a_2816_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_a_2816_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2826_ = v_a_2816_;
v_isShared_2827_ = v_isSharedCheck_3024_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v_a_2816_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_3024_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v_mainModuleName_2829_; lean_object* v_package_x3f_2830_; uint8_t v_isModule_2831_; lean_object* v_imports_2832_; lean_object* v_opts_2833_; uint32_t v_trustLevel_2834_; lean_object* v_importArts_2835_; lean_object* v_plugins_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2841_; 
v___x_2828_ = lean_io_mono_nanos_now();
v_mainModuleName_2829_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_mainModuleName_2829_);
v_package_x3f_2830_ = lean_ctor_get(v_a_2824_, 1);
lean_inc(v_package_x3f_2830_);
v_isModule_2831_ = lean_ctor_get_uint8(v_a_2824_, sizeof(void*)*6 + 4);
v_imports_2832_ = lean_ctor_get(v_a_2824_, 2);
lean_inc_ref(v_imports_2832_);
v_opts_2833_ = lean_ctor_get(v_a_2824_, 3);
lean_inc_ref(v_opts_2833_);
v_trustLevel_2834_ = lean_ctor_get_uint32(v_a_2824_, sizeof(void*)*6);
v_importArts_2835_ = lean_ctor_get(v_a_2824_, 4);
lean_inc(v_importArts_2835_);
v_plugins_2836_ = lean_ctor_get(v_a_2824_, 5);
lean_inc_ref(v_plugins_2836_);
lean_dec(v_a_2824_);
v___x_2837_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2803_);
v___x_2838_ = l_Lean_MessageLog_empty;
v___x_2839_ = 1;
lean_inc(v_stx_2803_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_stx_2803_);
v___x_2841_ = v___x_2826_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_stx_2803_);
v___x_2841_ = v_reuseFailAlloc_3023_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_origStx_2804_);
lean_inc_ref(v___x_2841_);
lean_inc_ref(v_opts_2833_);
v___x_2843_ = l_Lean_Elab_processHeaderCore(v___x_2837_, v_imports_2832_, v_isModule_2831_, v_opts_2833_, v___x_2838_, v_toProcessingContext_2805_, v_trustLevel_2834_, v_plugins_2836_, v___x_2839_, v_mainModuleName_2829_, v_package_x3f_2830_, v_importArts_2835_, v___x_2841_, v___x_2842_);
lean_dec(v___x_2837_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_3014_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_3014_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_3014_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_3013_; 
v_fst_2848_ = lean_ctor_get(v_a_2844_, 0);
v_snd_2849_ = lean_ctor_get(v_a_2844_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_a_2844_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2851_ = v_a_2844_;
v_isShared_2852_ = v_isSharedCheck_3013_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snd_2849_);
lean_inc(v_fst_2848_);
lean_dec(v_a_2844_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_3013_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v_traceState_2871_; 
v___x_2853_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2849_);
v___x_2854_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2849_);
v___x_2855_ = l_Lean_MessageLog_hasErrors(v_snd_2849_);
if (v___x_2855_ == 0)
{
double v___x_2963_; double v___x_2964_; double v___x_2965_; double v___x_2966_; double v___x_2967_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_del_object(v___x_2818_);
lean_dec_ref(v___x_2811_);
v___x_2963_ = lean_float_of_nat(v___x_2828_);
v___x_2964_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2965_ = lean_float_div(v___x_2963_, v___x_2964_);
v___x_2966_ = lean_float_of_nat(v___x_2853_);
v___x_2967_ = lean_float_div(v___x_2966_, v___x_2964_);
v___x_2984_ = l_Lean_trace_profiler_output;
v___x_2985_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2833_, v___x_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
if (v___x_2855_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2871_ = v___x_2986_;
goto v___jp_2870_;
}
else
{
goto v___jp_2968_;
}
}
else
{
lean_dec_ref(v___x_2985_);
goto v___jp_2968_;
}
v___jp_2968_:
{
uint64_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2969_ = 0ULL;
v___x_2970_ = lean_box(0);
v___x_2971_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2972_ = lean_box(0);
v___x_2973_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2974_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2974_, 0, v___x_2971_);
lean_ctor_set(v___x_2974_, 1, v___x_2972_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
lean_ctor_set_float(v___x_2974_, sizeof(void*)*3, v___x_2965_);
lean_ctor_set_float(v___x_2974_, sizeof(void*)*3 + 8, v___x_2967_);
lean_ctor_set_uint8(v___x_2974_, sizeof(void*)*3 + 16, v___x_2839_);
v___x_2975_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2976_ = lean_mk_empty_array_with_capacity(v___x_2806_);
v___x_2977_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2974_);
lean_ctor_set(v___x_2977_, 1, v___x_2975_);
lean_ctor_set(v___x_2977_, 2, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2970_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_unsigned_to_nat(1u);
v___x_2980_ = lean_mk_empty_array_with_capacity(v___x_2979_);
v___x_2981_ = lean_array_push(v___x_2980_, v___x_2978_);
v___x_2982_ = l_Array_toPArray_x27___redArg(v___x_2981_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set_uint64(v___x_2983_, sizeof(void*)*1, v___x_2969_);
v_traceState_2871_ = v___x_2983_;
goto v___jp_2870_;
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint64_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; size_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec(v___x_2853_);
lean_del_object(v___x_2851_);
lean_dec(v_snd_2849_);
lean_dec(v_fst_2848_);
lean_del_object(v___x_2846_);
lean_dec_ref(v___x_2841_);
lean_dec_ref(v_opts_2833_);
lean_dec(v___x_2828_);
lean_dec(v___x_2810_);
lean_dec_ref(v_parserState_2808_);
lean_dec_ref(v_fileMap_2807_);
lean_dec(v_stx_2803_);
v___x_2987_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2988_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2989_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2806_, 2);
v___x_2990_ = l_Lean_Name_num___override(v___x_2989_, v___x_2806_);
v___x_2991_ = l_Lean_Name_str___override(v___x_2990_, v___x_2987_);
v___x_2992_ = l_Lean_Name_str___override(v___x_2991_, v___x_2988_);
v___x_2993_ = l_Lean_Name_str___override(v___x_2992_, v___x_2987_);
v___x_2994_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2995_ = l_Lean_Name_str___override(v___x_2993_, v___x_2994_);
v___x_2996_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2997_ = l_Lean_Name_str___override(v___x_2995_, v___x_2996_);
v___x_2998_ = l_Lean_Name_toString(v___x_2997_, v___x_2839_);
v___x_2999_ = lean_box(0);
v___x_3000_ = 0ULL;
v___x_3001_ = lean_unsigned_to_nat(32u);
v___x_3002_ = lean_mk_empty_array_with_capacity(v___x_3001_);
v___x_3003_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3004_ = ((size_t)5ULL);
v___x_3005_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3002_);
lean_ctor_set(v___x_3005_, 2, v___x_2806_);
lean_ctor_set(v___x_3005_, 3, v___x_2806_);
lean_ctor_set_usize(v___x_3005_, 4, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
lean_ctor_set_uint64(v___x_3006_, sizeof(void*)*1, v___x_3000_);
v___x_3007_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3007_, 0, v___x_2998_);
lean_ctor_set(v___x_3007_, 1, v___x_2854_);
lean_ctor_set(v___x_3007_, 2, v___x_2999_);
lean_ctor_set(v___x_3007_, 3, v___x_3006_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*4, v___x_2855_);
v___x_3008_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2811_);
v___x_3009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
lean_ctor_set(v___x_3009_, 2, v___x_2999_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_3009_);
v___x_3011_ = v___x_2818_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
v___jp_2856_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2863_, 0, v___y_2862_);
v___x_2864_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2864_, 0, v___y_2859_);
lean_ctor_set(v___x_2864_, 1, v___x_2854_);
lean_ctor_set(v___x_2864_, 2, v___x_2863_);
lean_ctor_set(v___x_2864_, 3, v___y_2861_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*4, v___x_2855_);
v___x_2865_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2860_, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2866_, 0, v___y_2857_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
lean_ctor_set(v___x_2866_, 2, v___y_2858_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2866_);
v___x_2868_ = v___x_2846_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
v___jp_2870_:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Language_Lean_reparseOptions(v_opts_2833_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v_env_2879_; lean_object* v_messages_2880_; lean_object* v_scopes_2881_; lean_object* v_usedQuotCtxts_2882_; lean_object* v_nextMacroScope_2883_; lean_object* v_maxRecDepth_2884_; lean_object* v_ngen_2885_; lean_object* v_auxDeclNGen_2886_; lean_object* v_snapshotTasks_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2952_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2806_, 4);
v___x_2875_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2806_);
lean_ctor_set(v___x_2875_, 1, v___x_2806_);
lean_ctor_set(v___x_2875_, 2, v___x_2806_);
lean_ctor_set(v___x_2875_, 3, v___x_2806_);
lean_ctor_set(v___x_2875_, 4, v___x_2874_);
lean_ctor_set(v___x_2875_, 5, v___x_2874_);
lean_ctor_set(v___x_2875_, 6, v___x_2874_);
lean_ctor_set(v___x_2875_, 7, v___x_2874_);
lean_ctor_set(v___x_2875_, 8, v___x_2874_);
lean_ctor_set(v___x_2875_, 9, v___x_2874_);
v___x_2876_ = lean_io_promise_new();
v___x_2877_ = l_IO_CancelToken_new();
lean_inc(v_fst_2848_);
v___x_2878_ = l_Lean_Elab_Command_mkState(v_fst_2848_, v_snd_2849_, v_a_2873_);
v_env_2879_ = lean_ctor_get(v___x_2878_, 0);
v_messages_2880_ = lean_ctor_get(v___x_2878_, 1);
v_scopes_2881_ = lean_ctor_get(v___x_2878_, 2);
v_usedQuotCtxts_2882_ = lean_ctor_get(v___x_2878_, 3);
v_nextMacroScope_2883_ = lean_ctor_get(v___x_2878_, 4);
v_maxRecDepth_2884_ = lean_ctor_get(v___x_2878_, 5);
v_ngen_2885_ = lean_ctor_get(v___x_2878_, 6);
v_auxDeclNGen_2886_ = lean_ctor_get(v___x_2878_, 7);
v_snapshotTasks_2887_ = lean_ctor_get(v___x_2878_, 10);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; lean_object* v_unused_2954_; 
v_unused_2953_ = lean_ctor_get(v___x_2878_, 9);
lean_dec(v_unused_2953_);
v_unused_2954_ = lean_ctor_get(v___x_2878_, 8);
lean_dec(v_unused_2954_);
v___x_2889_ = v___x_2878_;
v_isShared_2890_ = v_isSharedCheck_2952_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_snapshotTasks_2887_);
lean_inc(v_auxDeclNGen_2886_);
lean_inc(v_ngen_2885_);
lean_inc(v_maxRecDepth_2884_);
lean_inc(v_nextMacroScope_2883_);
lean_inc(v_usedQuotCtxts_2882_);
lean_inc(v_scopes_2881_);
lean_inc(v_messages_2880_);
lean_inc(v_env_2879_);
lean_dec(v___x_2878_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2952_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2891_ = lean_box(0);
v___x_2892_ = l_Lean_Options_empty;
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_box(0);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2897_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2897_, 0, v_fst_2848_);
lean_ctor_set(v___x_2897_, 1, v___x_2891_);
lean_ctor_set(v___x_2897_, 2, v_fileMap_2807_);
lean_ctor_set(v___x_2897_, 3, v___x_2875_);
lean_ctor_set(v___x_2897_, 4, v___x_2892_);
lean_ctor_set(v___x_2897_, 5, v___x_2893_);
lean_ctor_set(v___x_2897_, 6, v___x_2894_);
lean_ctor_set(v___x_2897_, 7, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
v___x_2899_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2803_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_stx_2803_);
lean_ctor_set(v___x_2851_, 0, v___x_2899_);
v___x_2901_ = v___x_2851_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_stx_2803_);
v___x_2901_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
v___x_2903_ = lean_unsigned_to_nat(2u);
v___x_2904_ = l_Lean_Syntax_getArg(v_stx_2803_, v___x_2903_);
lean_dec(v_stx_2803_);
v___x_2905_ = l_Lean_Syntax_getArgs(v___x_2904_);
lean_dec(v___x_2904_);
v___x_2906_ = lean_array_to_list(v___x_2905_);
v___x_2907_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2906_, v___x_2894_);
v___x_2908_ = l_List_toPArray_x27___redArg(v___x_2907_);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2902_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2898_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2895_);
v___x_2912_ = lean_array_push(v___x_2911_, v___x_2910_);
v___x_2913_ = l_Array_toPArray_x27___redArg(v___x_2912_);
lean_dec_ref(v___x_2912_);
lean_inc_ref(v___x_2913_);
v___x_2914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2914_, 0, v___x_2874_);
lean_ctor_set(v___x_2914_, 1, v___x_2874_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
lean_ctor_set_uint8(v___x_2914_, sizeof(void*)*3, v___x_2839_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 9, v_traceState_2871_);
lean_ctor_set(v___x_2889_, 8, v___x_2914_);
v___x_2916_ = v___x_2889_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_env_2879_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_messages_2880_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v_scopes_2881_);
lean_ctor_set(v_reuseFailAlloc_2950_, 3, v_usedQuotCtxts_2882_);
lean_ctor_set(v_reuseFailAlloc_2950_, 4, v_nextMacroScope_2883_);
lean_ctor_set(v_reuseFailAlloc_2950_, 5, v_maxRecDepth_2884_);
lean_ctor_set(v_reuseFailAlloc_2950_, 6, v_ngen_2885_);
lean_ctor_set(v_reuseFailAlloc_2950_, 7, v_auxDeclNGen_2886_);
lean_ctor_set(v_reuseFailAlloc_2950_, 8, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2950_, 9, v_traceState_2871_);
lean_ctor_set(v_reuseFailAlloc_2950_, 10, v_snapshotTasks_2887_);
v___x_2916_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; lean_object* v_size_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint64_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
lean_inc(v___x_2877_);
lean_inc(v___x_2876_);
lean_inc_ref(v___x_2916_);
v___x_2917_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2891_, v_parserState_2808_, v___x_2916_, v___x_2876_, v___x_2839_, v___x_2877_, v_a_2809_);
v___x_2918_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2919_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2920_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2806_, 3);
v___x_2921_ = l_Lean_Name_num___override(v___x_2920_, v___x_2806_);
v___x_2922_ = lean_unsigned_to_nat(32u);
v___x_2923_ = lean_mk_empty_array_with_capacity(v___x_2922_);
v___x_2924_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2925_ = ((size_t)5ULL);
v___x_2926_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2923_);
lean_ctor_set(v___x_2926_, 2, v___x_2806_);
lean_ctor_set(v___x_2926_, 3, v___x_2806_);
lean_ctor_set_usize(v___x_2926_, 4, v___x_2925_);
v_size_2927_ = lean_ctor_get(v___x_2913_, 2);
lean_inc(v_size_2927_);
v___x_2928_ = l_Lean_Name_str___override(v___x_2921_, v___x_2918_);
v___x_2929_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2810_);
v___x_2930_ = l_Lean_Name_str___override(v___x_2928_, v___x_2919_);
v___x_2931_ = l_Lean_Name_str___override(v___x_2930_, v___x_2918_);
v___x_2932_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2933_ = l_Lean_Name_str___override(v___x_2931_, v___x_2932_);
v___x_2934_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2935_ = l_Lean_Name_str___override(v___x_2933_, v___x_2934_);
v___x_2936_ = l_Lean_Name_toString(v___x_2935_, v___x_2839_);
v___x_2937_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2938_ = 0ULL;
v___x_2939_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2939_, 0, v___x_2926_);
lean_ctor_set_uint64(v___x_2939_, sizeof(void*)*1, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2877_);
v___x_2941_ = l_IO_Promise_result_x21___redArg(v___x_2876_);
lean_dec(v___x_2876_);
v___x_2942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2810_);
lean_ctor_set(v___x_2942_, 1, v___x_2929_);
lean_ctor_set(v___x_2942_, 2, v___x_2940_);
lean_ctor_set(v___x_2942_, 3, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2916_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_inc_ref(v___x_2939_);
lean_inc_ref(v___x_2936_);
v___x_2945_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2945_, 0, v___x_2936_);
lean_ctor_set(v___x_2945_, 1, v___x_2937_);
lean_ctor_set(v___x_2945_, 2, v___x_2891_);
lean_ctor_set(v___x_2945_, 3, v___x_2939_);
lean_ctor_set_uint8(v___x_2945_, sizeof(void*)*4, v___x_2855_);
v___x_2946_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2947_ = lean_nat_dec_lt(v___x_2806_, v_size_2927_);
lean_dec(v_size_2927_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v___x_2913_);
lean_dec(v___x_2806_);
v___x_2948_ = l_outOfBounds___redArg(v___x_2946_);
v___y_2857_ = v___x_2945_;
v___y_2858_ = v___x_2944_;
v___y_2859_ = v___x_2936_;
v___y_2860_ = v___x_2841_;
v___y_2861_ = v___x_2939_;
v___y_2862_ = v___x_2948_;
goto v___jp_2856_;
}
else
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2946_, v___x_2913_, v___x_2806_);
lean_dec(v___x_2806_);
lean_dec_ref(v___x_2913_);
v___y_2857_ = v___x_2945_;
v___y_2858_ = v___x_2944_;
v___y_2859_ = v___x_2936_;
v___y_2860_ = v___x_2841_;
v___y_2861_ = v___x_2939_;
v___y_2862_ = v___x_2949_;
goto v___jp_2856_;
}
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v_traceState_2871_);
lean_dec_ref(v___x_2854_);
lean_del_object(v___x_2851_);
lean_dec(v_snd_2849_);
lean_dec(v_fst_2848_);
lean_del_object(v___x_2846_);
lean_dec_ref(v___x_2841_);
lean_dec(v___x_2810_);
lean_dec_ref(v_parserState_2808_);
lean_dec_ref(v_fileMap_2807_);
lean_dec(v___x_2806_);
lean_dec(v_stx_2803_);
v_a_2955_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2872_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2872_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v___x_2841_);
lean_dec_ref(v_opts_2833_);
lean_dec(v___x_2828_);
lean_del_object(v___x_2818_);
lean_dec_ref(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_parserState_2808_);
lean_dec_ref(v_fileMap_2807_);
lean_dec(v___x_2806_);
lean_dec(v_stx_2803_);
v_a_3015_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2843_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2843_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
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
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec_ref(v_parserState_2808_);
lean_dec_ref(v_fileMap_2807_);
lean_dec(v___x_2806_);
lean_dec_ref(v_toProcessingContext_2805_);
lean_dec(v_origStx_2804_);
lean_dec(v_stx_2803_);
v_a_3026_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2815_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2815_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3034_, lean_object* v_stx_3035_, lean_object* v_origStx_3036_, lean_object* v_toProcessingContext_3037_, lean_object* v___x_3038_, lean_object* v_fileMap_3039_, lean_object* v_parserState_3040_, lean_object* v_a_3041_, lean_object* v___x_3042_, lean_object* v___x_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3034_, v_stx_3035_, v_origStx_3036_, v_toProcessingContext_3037_, v___x_3038_, v_fileMap_3039_, v_parserState_3040_, v_a_3041_, v___x_3042_, v___x_3043_, v___y_3044_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v_a_3041_);
return v_res_3046_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___f_3048_; 
v___x_3047_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3048_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3048_, 0, v___x_3047_);
return v___f_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3049_, lean_object* v_stx_3050_, lean_object* v_origStx_3051_, lean_object* v_parserState_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_toProcessingContext_3055_; lean_object* v_fileMap_3056_; lean_object* v_endPos_3057_; lean_object* v___x_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_toProcessingContext_3055_ = lean_ctor_get(v_a_3053_, 0);
v_fileMap_3056_ = lean_ctor_get(v_toProcessingContext_3055_, 2);
v_endPos_3057_ = lean_ctor_get(v_toProcessingContext_3055_, 3);
v___x_3058_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3059_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3060_ = lean_box(0);
v___x_3061_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3053_, 2);
lean_inc_ref(v_fileMap_3056_);
lean_inc_ref(v_toProcessingContext_3055_);
v___f_3062_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3062_, 0, v_setupImports_3049_);
lean_closure_set(v___f_3062_, 1, v_stx_3050_);
lean_closure_set(v___f_3062_, 2, v_origStx_3051_);
lean_closure_set(v___f_3062_, 3, v_toProcessingContext_3055_);
lean_closure_set(v___f_3062_, 4, v___x_3061_);
lean_closure_set(v___f_3062_, 5, v_fileMap_3056_);
lean_closure_set(v___f_3062_, 6, v_parserState_3052_);
lean_closure_set(v___f_3062_, 7, v_a_3053_);
lean_closure_set(v___f_3062_, 8, v___x_3060_);
lean_closure_set(v___f_3062_, 9, v___x_3058_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3067_, lean_object* v_stx_3068_, lean_object* v_origStx_3069_, lean_object* v_parserState_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3067_, v_stx_3068_, v_origStx_3069_, v_parserState_3070_, v_a_3071_);
lean_dec_ref(v_a_3071_);
return v_res_3073_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = 1;
v___x_3081_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3082_ = l_Lean_Name_toString(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3083_ = 0;
v___x_3084_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3085_ = lean_box(0);
v___x_3086_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3087_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3088_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___x_3086_);
lean_ctor_set(v___x_3088_, 2, v___x_3085_);
lean_ctor_set(v___x_3088_, 3, v___x_3084_);
lean_ctor_set_uint8(v___x_3088_, sizeof(void*)*4, v___x_3083_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3089_, lean_object* v_cmdState_3090_, lean_object* v_a_3091_, lean_object* v_toSnapshot_3092_, lean_object* v_newStx_3093_, lean_object* v_oldCmd_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v_diagnostics_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3123_; 
v___x_3096_ = lean_io_promise_new();
v___x_3097_ = l_IO_CancelToken_new();
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_oldCmd_3094_);
v___x_3099_ = 1;
lean_inc(v___x_3097_);
lean_inc(v___x_3096_);
lean_inc_ref(v_cmdState_3090_);
v___x_3100_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3098_, v_newParserState_3089_, v_cmdState_3090_, v___x_3096_, v___x_3099_, v___x_3097_, v_a_3091_);
v_diagnostics_3101_ = lean_ctor_get(v_toSnapshot_3092_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_toSnapshot_3092_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; lean_object* v_unused_3125_; lean_object* v_unused_3126_; 
v_unused_3124_ = lean_ctor_get(v_toSnapshot_3092_, 3);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_toSnapshot_3092_, 2);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_toSnapshot_3092_, 0);
lean_dec(v_unused_3126_);
v___x_3103_ = v_toSnapshot_3092_;
v_isShared_3104_ = v_isSharedCheck_3123_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_diagnostics_3101_);
lean_dec(v_toSnapshot_3092_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3123_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3105_ = lean_box(0);
v___x_3106_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3107_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3108_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3097_);
v___x_3110_ = l_IO_Promise_result_x21___redArg(v___x_3096_);
lean_dec(v___x_3096_);
v___x_3111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3105_);
lean_ctor_set(v___x_3111_, 1, v___x_3106_);
lean_ctor_set(v___x_3111_, 2, v___x_3109_);
lean_ctor_set(v___x_3111_, 3, v___x_3110_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_cmdState_3090_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
v___x_3114_ = 0;
v___x_3115_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_newStx_3093_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 3, v___x_3108_);
lean_ctor_set(v___x_3103_, 2, v___x_3105_);
lean_ctor_set(v___x_3103_, 0, v___x_3107_);
v___x_3118_ = v___x_3103_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_diagnostics_3101_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v___x_3108_);
v___x_3118_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*4, v___x_3114_);
v___x_3119_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3116_, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3115_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
lean_ctor_set(v___x_3120_, 2, v___x_3113_);
v___x_3121_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3105_, v___x_3120_);
return v___x_3121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3127_, lean_object* v_cmdState_3128_, lean_object* v_a_3129_, lean_object* v_toSnapshot_3130_, lean_object* v_newStx_3131_, lean_object* v_oldCmd_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3127_, v_cmdState_3128_, v_a_3129_, v_toSnapshot_3130_, v_newStx_3131_, v_oldCmd_3132_);
lean_dec_ref(v_a_3129_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3135_, lean_object* v_a_3136_, lean_object* v_newStx_3137_, lean_object* v___x_3138_, lean_object* v_oldProcessed_3139_){
_start:
{
lean_object* v_result_x3f_3141_; 
v_result_x3f_3141_ = lean_ctor_get(v_oldProcessed_3139_, 2);
if (lean_obj_tag(v_result_x3f_3141_) == 1)
{
lean_object* v_val_3142_; lean_object* v_firstCmdSnap_3143_; lean_object* v_toSnapshot_3144_; lean_object* v_cmdState_3145_; lean_object* v_stx_x3f_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
v_val_3142_ = lean_ctor_get(v_result_x3f_3141_, 0);
lean_inc(v_val_3142_);
v_firstCmdSnap_3143_ = lean_ctor_get(v_val_3142_, 1);
lean_inc_ref(v_firstCmdSnap_3143_);
v_toSnapshot_3144_ = lean_ctor_get(v_oldProcessed_3139_, 0);
lean_inc_ref(v_toSnapshot_3144_);
lean_dec_ref(v_oldProcessed_3139_);
v_cmdState_3145_ = lean_ctor_get(v_val_3142_, 0);
lean_inc_ref(v_cmdState_3145_);
lean_dec(v_val_3142_);
v_stx_x3f_3146_ = lean_ctor_get(v_firstCmdSnap_3143_, 0);
lean_inc(v_stx_x3f_3146_);
lean_inc_ref(v_a_3136_);
v___f_3147_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3147_, 0, v_newParserState_3135_);
lean_closure_set(v___f_3147_, 1, v_cmdState_3145_);
lean_closure_set(v___f_3147_, 2, v_a_3136_);
lean_closure_set(v___f_3147_, 3, v_toSnapshot_3144_);
lean_closure_set(v___f_3147_, 4, v_newStx_3137_);
v___x_3148_ = lean_box(0);
v___x_3149_ = 1;
v___x_3150_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3143_, v___f_3147_, v_stx_x3f_3146_, v___x_3138_, v___x_3148_, v___x_3149_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v___x_3138_);
lean_dec_ref(v_newParserState_3135_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_newStx_3137_);
v___x_3152_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3151_, v_oldProcessed_3139_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3153_, lean_object* v_a_3154_, lean_object* v_newStx_3155_, lean_object* v___x_3156_, lean_object* v_oldProcessed_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3153_, v_a_3154_, v_newStx_3155_, v___x_3156_, v_oldProcessed_3157_);
lean_dec_ref(v_a_3154_);
return v_res_3159_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3160_ = 0;
v___x_3161_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3162_ = lean_box(0);
v___x_3163_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3164_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3165_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
lean_ctor_set(v___x_3165_, 1, v___x_3163_);
lean_ctor_set(v___x_3165_, 2, v___x_3162_);
lean_ctor_set(v___x_3165_, 3, v___x_3161_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*4, v___x_3160_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3166_, lean_object* v_a_3167_, lean_object* v_old_3168_, lean_object* v_newStx_3169_, lean_object* v_newParserState_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_result_x3f_3173_; 
v_result_x3f_3173_ = lean_ctor_get(v_old_3168_, 4);
lean_inc(v_result_x3f_3173_);
if (lean_obj_tag(v_result_x3f_3173_) == 1)
{
lean_object* v_val_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3228_; 
v_val_3174_ = lean_ctor_get(v_result_x3f_3173_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_result_x3f_3173_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3176_ = v_result_x3f_3173_;
v_isShared_3177_ = v_isSharedCheck_3228_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_val_3174_);
lean_dec(v_result_x3f_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3228_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v_processedSnap_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3226_; 
v_processedSnap_3178_ = lean_ctor_get(v_val_3174_, 1);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_val_3174_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v_val_3174_, 0);
lean_dec(v_unused_3227_);
v___x_3180_ = v_val_3174_;
v_isShared_3181_ = v_isSharedCheck_3226_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_processedSnap_3178_);
lean_dec(v_val_3174_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3226_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_toSnapshot_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3221_; 
v_toSnapshot_3182_ = lean_ctor_get(v_old_3168_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_old_3168_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; 
v_unused_3222_ = lean_ctor_get(v_old_3168_, 4);
lean_dec(v_unused_3222_);
v_unused_3223_ = lean_ctor_get(v_old_3168_, 3);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_old_3168_, 2);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_old_3168_, 1);
lean_dec(v_unused_3225_);
v___x_3184_ = v_old_3168_;
v_isShared_3185_ = v_isSharedCheck_3221_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_toSnapshot_3182_);
lean_dec(v_old_3168_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3221_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_pos_3186_; lean_object* v_endPos_3187_; lean_object* v_stx_x3f_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; lean_object* v___x_3194_; lean_object* v_diagnostics_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3217_; 
v_pos_3186_ = lean_ctor_get(v_newParserState_3170_, 0);
v_endPos_3187_ = lean_ctor_get(v_toProcessingContext_3166_, 3);
v_stx_x3f_3188_ = lean_ctor_get(v_processedSnap_3178_, 0);
lean_inc(v_stx_x3f_3188_);
lean_inc(v_endPos_3187_);
lean_inc(v_pos_3186_);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_pos_3186_);
lean_ctor_set(v___x_3189_, 1, v_endPos_3187_);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_inc_ref(v___x_3190_);
lean_inc(v_newStx_3169_);
lean_inc_ref(v_a_3167_);
lean_inc_ref(v_newParserState_3170_);
v___f_3191_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3191_, 0, v_newParserState_3170_);
lean_closure_set(v___f_3191_, 1, v_a_3167_);
lean_closure_set(v___f_3191_, 2, v_newStx_3169_);
lean_closure_set(v___f_3191_, 3, v___x_3190_);
v___x_3192_ = lean_box(0);
v___x_3193_ = 1;
v___x_3194_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3178_, v___f_3191_, v_stx_x3f_3188_, v___x_3190_, v___x_3192_, v___x_3193_);
v_diagnostics_3195_ = lean_ctor_get(v_toSnapshot_3182_, 1);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_toSnapshot_3182_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; lean_object* v_unused_3219_; lean_object* v_unused_3220_; 
v_unused_3218_ = lean_ctor_get(v_toSnapshot_3182_, 3);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_toSnapshot_3182_, 2);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_toSnapshot_3182_, 0);
lean_dec(v_unused_3220_);
v___x_3197_ = v_toSnapshot_3182_;
v_isShared_3198_ = v_isSharedCheck_3217_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_diagnostics_3195_);
lean_dec(v_toSnapshot_3182_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3217_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3199_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3200_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 1, v___x_3194_);
lean_ctor_set(v___x_3180_, 0, v_newParserState_3170_);
v___x_3202_ = v___x_3180_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_newParserState_3170_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3194_);
v___x_3202_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v___x_3202_);
v___x_3204_ = v___x_3176_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3205_ = 0;
v___x_3206_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3169_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_newStx_3169_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 3, v___x_3200_);
lean_ctor_set(v___x_3197_, 2, v___x_3192_);
lean_ctor_set(v___x_3197_, 0, v___x_3199_);
v___x_3209_ = v___x_3197_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_diagnostics_3195_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v___x_3200_);
v___x_3209_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
lean_ctor_set_uint8(v___x_3209_, sizeof(void*)*4, v___x_3205_);
v___x_3210_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3207_, v___x_3209_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 4, v___x_3204_);
lean_ctor_set(v___x_3184_, 3, v_newStx_3169_);
lean_ctor_set(v___x_3184_, 2, v_toProcessingContext_3166_);
lean_ctor_set(v___x_3184_, 1, v___x_3210_);
lean_ctor_set(v___x_3184_, 0, v___x_3206_);
v___x_3212_ = v___x_3184_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_toProcessingContext_3166_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v_newStx_3169_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v___x_3204_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
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
lean_dec(v_result_x3f_3173_);
lean_dec_ref(v_newParserState_3170_);
lean_dec(v_newStx_3169_);
lean_dec_ref(v_toProcessingContext_3166_);
return v_old_3168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3229_, lean_object* v_a_3230_, lean_object* v_old_3231_, lean_object* v_newStx_3232_, lean_object* v_newParserState_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3229_, v_a_3230_, v_old_3231_, v_newStx_3232_, v_newParserState_3233_, v___y_3234_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v_a_3230_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3237_, lean_object* v_setupImports_3238_, lean_object* v_old_x3f_3239_, lean_object* v___f_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
lean_inc_ref(v_toProcessingContext_3237_);
v___x_3243_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3237_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3313_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3313_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3313_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_snd_3248_; lean_object* v_fst_3249_; lean_object* v_fst_3250_; lean_object* v_snd_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3312_; 
v_snd_3248_ = lean_ctor_get(v_a_3244_, 1);
lean_inc(v_snd_3248_);
v_fst_3249_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_fst_3249_);
lean_dec(v_a_3244_);
v_fst_3250_ = lean_ctor_get(v_snd_3248_, 0);
v_snd_3251_ = lean_ctor_get(v_snd_3248_, 1);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_snd_3248_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3253_ = v_snd_3248_;
v_isShared_3254_ = v_isSharedCheck_3312_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_snd_3251_);
lean_inc(v_fst_3250_);
lean_dec(v_snd_3248_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3312_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
uint8_t v___x_3255_; 
v___x_3255_ = l_Lean_MessageLog_hasErrors(v_snd_3251_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___y_3258_; 
lean_inc(v_fst_3249_);
v___x_3256_ = l_Lean_Syntax_unsetTrailing(v_fst_3249_);
if (lean_obj_tag(v_old_x3f_3239_) == 1)
{
lean_object* v_val_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3295_; 
v_val_3279_ = lean_ctor_get(v_old_x3f_3239_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_old_x3f_3239_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3281_ = v_old_x3f_3239_;
v_isShared_3282_ = v_isSharedCheck_3295_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_val_3279_);
lean_dec(v_old_x3f_3239_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3295_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_stx_3283_; lean_object* v_result_x3f_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v_stx_3283_ = lean_ctor_get(v_val_3279_, 3);
v_result_x3f_3284_ = lean_ctor_get(v_val_3279_, 4);
lean_inc(v_stx_3283_);
v___x_3285_ = l_Lean_Syntax_unsetTrailing(v_stx_3283_);
lean_inc(v___x_3256_);
v___x_3286_ = l_Lean_Syntax_eqWithInfo(v___x_3256_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_inc(v_result_x3f_3284_);
lean_del_object(v___x_3281_);
lean_dec(v_val_3279_);
lean_dec_ref(v___f_3240_);
if (lean_obj_tag(v_result_x3f_3284_) == 0)
{
v___y_3258_ = v___y_3241_;
goto v___jp_3257_;
}
else
{
lean_object* v_val_3287_; lean_object* v_processedSnap_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_val_3287_ = lean_ctor_get(v_result_x3f_3284_, 0);
lean_inc(v_val_3287_);
lean_dec_ref(v_result_x3f_3284_);
v_processedSnap_3288_ = lean_ctor_get(v_val_3287_, 1);
lean_inc_ref(v_processedSnap_3288_);
lean_dec(v_val_3287_);
v___x_3289_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3290_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3289_, v_processedSnap_3288_);
v___y_3258_ = v___y_3241_;
goto v___jp_3257_;
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
lean_dec(v___x_3256_);
lean_del_object(v___x_3253_);
lean_dec(v_snd_3251_);
lean_del_object(v___x_3246_);
lean_dec_ref(v_setupImports_3238_);
lean_dec_ref(v_toProcessingContext_3237_);
lean_inc_ref(v___y_3241_);
v___x_3291_ = lean_apply_5(v___f_3240_, v_val_3279_, v_fst_3249_, v_fst_3250_, v___y_3241_, lean_box(0));
if (v_isShared_3282_ == 0)
{
lean_ctor_set_tag(v___x_3281_, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3291_);
v___x_3293_ = v___x_3281_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_dec_ref(v___f_3240_);
lean_dec(v_old_x3f_3239_);
v___y_3258_ = v___y_3241_;
goto v___jp_3257_;
}
v___jp_3257_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3259_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3251_);
lean_inc(v_fst_3250_);
lean_inc(v_fst_3249_);
v___x_3260_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3238_, v___x_3256_, v_fst_3249_, v_fst_3250_, v___y_3258_);
v___x_3261_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3262_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3263_ = lean_box(0);
v___x_3264_ = lean_unsigned_to_nat(32u);
v___x_3265_ = lean_mk_empty_array_with_capacity(v___x_3264_);
lean_dec_ref(v___x_3265_);
v___x_3266_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v___x_3260_);
v___x_3268_ = v___x_3253_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_fst_3250_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v___x_3260_);
v___x_3268_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3270_, 0, v___x_3261_);
lean_ctor_set(v___x_3270_, 1, v___x_3262_);
lean_ctor_set(v___x_3270_, 2, v___x_3263_);
lean_ctor_set(v___x_3270_, 3, v___x_3266_);
lean_ctor_set_uint8(v___x_3270_, sizeof(void*)*4, v___x_3255_);
lean_inc(v_fst_3249_);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_fst_3249_);
v___x_3272_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3272_, 0, v___x_3261_);
lean_ctor_set(v___x_3272_, 1, v___x_3259_);
lean_ctor_set(v___x_3272_, 2, v___x_3263_);
lean_ctor_set(v___x_3272_, 3, v___x_3266_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*4, v___x_3255_);
v___x_3273_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3271_, v___x_3272_);
v___x_3274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3270_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
lean_ctor_set(v___x_3274_, 2, v_toProcessingContext_3237_);
lean_ctor_set(v___x_3274_, 3, v_fst_3249_);
lean_ctor_set(v___x_3274_, 4, v___x_3269_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3274_);
v___x_3276_ = v___x_3246_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
lean_del_object(v___x_3253_);
lean_dec(v_fst_3250_);
lean_dec_ref(v___f_3240_);
lean_dec(v_old_x3f_3239_);
lean_dec_ref(v_setupImports_3238_);
v___x_3296_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3251_);
v___x_3297_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3298_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_unsigned_to_nat(32u);
v___x_3301_ = lean_mk_empty_array_with_capacity(v___x_3300_);
lean_dec_ref(v___x_3301_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3303_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3303_, 0, v___x_3297_);
lean_ctor_set(v___x_3303_, 1, v___x_3298_);
lean_ctor_set(v___x_3303_, 2, v___x_3299_);
lean_ctor_set(v___x_3303_, 3, v___x_3302_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*4, v___x_3255_);
lean_inc(v_fst_3249_);
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v_fst_3249_);
v___x_3305_ = 0;
v___x_3306_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3306_, 0, v___x_3297_);
lean_ctor_set(v___x_3306_, 1, v___x_3296_);
lean_ctor_set(v___x_3306_, 2, v___x_3299_);
lean_ctor_set(v___x_3306_, 3, v___x_3302_);
lean_ctor_set_uint8(v___x_3306_, sizeof(void*)*4, v___x_3305_);
v___x_3307_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3304_, v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3303_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
lean_ctor_set(v___x_3308_, 2, v_toProcessingContext_3237_);
lean_ctor_set(v___x_3308_, 3, v_fst_3249_);
lean_ctor_set(v___x_3308_, 4, v___x_3299_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3308_);
v___x_3310_ = v___x_3246_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec_ref(v___f_3240_);
lean_dec(v_old_x3f_3239_);
lean_dec_ref(v_setupImports_3238_);
lean_dec_ref(v_toProcessingContext_3237_);
v_a_3314_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3243_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3243_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3322_, lean_object* v_setupImports_3323_, lean_object* v_old_x3f_3324_, lean_object* v___f_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3322_, v_setupImports_3323_, v_old_x3f_3324_, v___f_3325_, v___y_3326_);
lean_dec_ref(v___y_3326_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3329_, lean_object* v_toProcessingContext_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3332_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3329_);
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3335_, 0, v_x_3331_);
lean_ctor_set(v___x_3335_, 1, v___x_3332_);
lean_ctor_set(v___x_3335_, 2, v_toProcessingContext_3330_);
lean_ctor_set(v___x_3335_, 3, v___x_3333_);
lean_ctor_set(v___x_3335_, 4, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3336_, lean_object* v_old_x3f_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v_toProcessingContext_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___f_3343_; lean_object* v___f_3344_; 
v_toProcessingContext_3340_ = lean_ctor_get(v_a_3338_, 0);
v___x_3341_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3338_);
lean_inc_ref_n(v_toProcessingContext_3340_, 3);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3342_, 0, v_toProcessingContext_3340_);
lean_closure_set(v___f_3342_, 1, v_a_3338_);
lean_inc(v_old_x3f_3337_);
v___f_3343_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3343_, 0, v_toProcessingContext_3340_);
lean_closure_set(v___f_3343_, 1, v_setupImports_3336_);
lean_closure_set(v___f_3343_, 2, v_old_x3f_3337_);
lean_closure_set(v___f_3343_, 3, v___f_3342_);
v___f_3344_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3344_, 0, v___x_3341_);
lean_closure_set(v___f_3344_, 1, v_toProcessingContext_3340_);
if (lean_obj_tag(v_old_x3f_3337_) == 1)
{
lean_object* v_val_3345_; lean_object* v_result_x3f_3346_; 
v_val_3345_ = lean_ctor_get(v_old_x3f_3337_, 0);
lean_inc(v_val_3345_);
lean_dec_ref(v_old_x3f_3337_);
v_result_x3f_3346_ = lean_ctor_get(v_val_3345_, 4);
if (lean_obj_tag(v_result_x3f_3346_) == 1)
{
lean_object* v_stx_3347_; lean_object* v_val_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v_stx_3347_ = lean_ctor_get(v_val_3345_, 3);
lean_inc(v_stx_3347_);
v_val_3348_ = lean_ctor_get(v_result_x3f_3346_, 0);
lean_inc(v_val_3345_);
v___x_3349_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3345_);
v___x_3350_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3349_);
if (lean_obj_tag(v___x_3350_) == 1)
{
lean_object* v_val_3351_; 
v_val_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_val_3351_);
lean_dec_ref(v___x_3350_);
if (lean_obj_tag(v_val_3351_) == 1)
{
lean_object* v_val_3352_; lean_object* v_firstCmdSnap_3353_; lean_object* v___x_3354_; 
v_val_3352_ = lean_ctor_get(v_val_3351_, 0);
lean_inc(v_val_3352_);
lean_dec_ref(v_val_3351_);
v_firstCmdSnap_3353_ = lean_ctor_get(v_val_3352_, 1);
lean_inc_ref(v_firstCmdSnap_3353_);
lean_dec(v_val_3352_);
v___x_3354_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3353_);
if (lean_obj_tag(v___x_3354_) == 1)
{
lean_object* v_val_3355_; lean_object* v_nextCmdSnap_x3f_3356_; 
v_val_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_val_3355_);
lean_dec_ref(v___x_3354_);
v_nextCmdSnap_x3f_3356_ = lean_ctor_get(v_val_3355_, 4);
lean_inc(v_nextCmdSnap_x3f_3356_);
lean_dec(v_val_3355_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3356_) == 0)
{
lean_object* v___x_3357_; 
lean_dec(v_stx_3347_);
lean_dec(v_val_3345_);
v___x_3357_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3357_;
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3359_; 
v_val_3358_ = lean_ctor_get(v_nextCmdSnap_x3f_3356_, 0);
lean_inc(v_val_3358_);
lean_dec_ref(v_nextCmdSnap_x3f_3356_);
v___x_3359_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3358_);
if (lean_obj_tag(v___x_3359_) == 1)
{
lean_object* v_val_3360_; lean_object* v_parserState_3361_; lean_object* v_pos_3362_; uint8_t v___x_3363_; 
v_val_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3360_);
lean_dec_ref(v___x_3359_);
v_parserState_3361_ = lean_ctor_get(v_val_3360_, 2);
lean_inc_ref(v_parserState_3361_);
lean_dec(v_val_3360_);
v_pos_3362_ = lean_ctor_get(v_parserState_3361_, 0);
lean_inc(v_pos_3362_);
lean_dec_ref(v_parserState_3361_);
v___x_3363_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3362_, v_a_3338_);
lean_dec(v_pos_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec(v_stx_3347_);
lean_dec(v_val_3345_);
v___x_3364_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3364_;
}
else
{
lean_object* v_parserState_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v___f_3344_);
lean_dec_ref(v___f_3343_);
v_parserState_3365_ = lean_ctor_get(v_val_3348_, 0);
lean_inc_ref(v_parserState_3365_);
lean_inc_ref(v_toProcessingContext_3340_);
v___x_3366_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3340_, v_a_3338_, v_val_3345_, v_stx_3347_, v_parserState_3365_, v_a_3338_);
return v___x_3366_;
}
}
else
{
lean_object* v___x_3367_; 
lean_dec(v___x_3359_);
lean_dec(v_stx_3347_);
lean_dec(v_val_3345_);
v___x_3367_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3367_;
}
}
}
else
{
lean_object* v___x_3368_; 
lean_dec(v___x_3354_);
lean_dec(v_stx_3347_);
lean_dec(v_val_3345_);
v___x_3368_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3368_;
}
}
else
{
lean_object* v___x_3369_; 
lean_dec(v_val_3351_);
lean_dec(v_stx_3347_);
lean_dec(v_val_3345_);
v___x_3369_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3369_;
}
}
else
{
lean_object* v___x_3370_; 
lean_dec(v___x_3350_);
lean_dec(v_stx_3347_);
lean_dec(v_val_3345_);
v___x_3370_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3370_;
}
}
else
{
lean_object* v___x_3371_; 
lean_dec(v_val_3345_);
v___x_3371_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3371_;
}
}
else
{
lean_object* v___x_3372_; 
lean_dec(v_old_x3f_3337_);
v___x_3372_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3344_, v___f_3343_, v_a_3338_);
return v___x_3372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3373_, lean_object* v_old_x3f_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3373_, v_old_x3f_3374_, v_a_3375_);
lean_dec_ref(v_a_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3378_, lean_object* v_old_x3f_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v___x_3382_; 
lean_inc(v_old_x3f_3379_);
v___x_3382_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3382_, 0, v_setupImports_3378_);
lean_closure_set(v___x_3382_, 1, v_old_x3f_3379_);
if (lean_obj_tag(v_old_x3f_3379_) == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = lean_box(0);
v___x_3384_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3382_, v___x_3383_, v_a_3380_);
return v___x_3384_;
}
else
{
lean_object* v_val_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3394_; 
v_val_3385_ = lean_ctor_get(v_old_x3f_3379_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_old_x3f_3379_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3387_ = v_old_x3f_3379_;
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_val_3385_);
lean_dec(v_old_x3f_3379_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_ictx_3389_; lean_object* v___x_3391_; 
v_ictx_3389_ = lean_ctor_get(v_val_3385_, 2);
lean_inc_ref(v_ictx_3389_);
lean_dec(v_val_3385_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v_ictx_3389_);
v___x_3391_ = v___x_3387_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_ictx_3389_);
v___x_3391_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3382_, v___x_3391_, v_a_3380_);
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3395_, lean_object* v_old_x3f_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_Language_Lean_process(v_setupImports_3395_, v_old_x3f_3396_, v_a_3397_);
lean_dec_ref(v_a_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3400_, lean_object* v_parserState_3401_, lean_object* v_commandState_3402_, lean_object* v_old_x3f_3403_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3413_; 
v___x_3405_ = lean_io_promise_new();
v___x_3406_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3403_) == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_box(0);
v___y_3413_ = v___x_3427_;
goto v___jp_3412_;
}
else
{
lean_object* v_val_3428_; lean_object* v_snd_3429_; lean_object* v___x_3430_; 
v_val_3428_ = lean_ctor_get(v_old_x3f_3403_, 0);
v_snd_3429_ = lean_ctor_get(v_val_3428_, 1);
lean_inc(v_snd_3429_);
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_snd_3429_);
v___y_3413_ = v___x_3430_;
goto v___jp_3412_;
}
v___jp_3407_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3408_, v___y_3409_, v_inputCtx_3400_);
lean_dec(v___x_3410_);
v___x_3411_ = l_IO_Promise_result_x21___redArg(v___x_3405_);
lean_dec(v___x_3405_);
return v___x_3411_;
}
v___jp_3412_:
{
uint8_t v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = 1;
v___x_3415_ = lean_box(v___x_3414_);
lean_inc(v___x_3405_);
v___x_3416_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 8, 6);
lean_closure_set(v___x_3416_, 0, v___y_3413_);
lean_closure_set(v___x_3416_, 1, v_parserState_3401_);
lean_closure_set(v___x_3416_, 2, v_commandState_3402_);
lean_closure_set(v___x_3416_, 3, v___x_3405_);
lean_closure_set(v___x_3416_, 4, v___x_3415_);
lean_closure_set(v___x_3416_, 5, v___x_3406_);
if (lean_obj_tag(v_old_x3f_3403_) == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_box(0);
v___y_3408_ = v___x_3416_;
v___y_3409_ = v___x_3417_;
goto v___jp_3407_;
}
else
{
lean_object* v_val_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3426_; 
v_val_3418_ = lean_ctor_get(v_old_x3f_3403_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_old_x3f_3403_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3420_ = v_old_x3f_3403_;
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_val_3418_);
lean_dec(v_old_x3f_3403_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_fst_3422_; lean_object* v___x_3424_; 
v_fst_3422_ = lean_ctor_get(v_val_3418_, 0);
lean_inc(v_fst_3422_);
lean_dec(v_val_3418_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v_fst_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_fst_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
v___y_3408_ = v___x_3416_;
v___y_3409_ = v___x_3424_;
goto v___jp_3407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3431_, lean_object* v_parserState_3432_, lean_object* v_commandState_3433_, lean_object* v_old_x3f_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3431_, v_parserState_3432_, v_commandState_3433_, v_old_x3f_3434_);
lean_dec_ref(v_inputCtx_3431_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3437_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3438_; 
v_nextCmdSnap_x3f_3438_ = lean_ctor_get(v_snap_3437_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3438_) == 1)
{
lean_object* v_val_3439_; lean_object* v___x_3440_; 
lean_inc_ref(v_nextCmdSnap_x3f_3438_);
lean_dec_ref(v_snap_3437_);
v_val_3439_ = lean_ctor_get(v_nextCmdSnap_x3f_3438_, 0);
lean_inc(v_val_3439_);
lean_dec_ref(v_nextCmdSnap_x3f_3438_);
v___x_3440_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3439_);
v_snap_3437_ = v___x_3440_;
goto _start;
}
else
{
lean_object* v_elabSnap_3442_; lean_object* v_resultSnap_3443_; lean_object* v___x_3444_; lean_object* v_cmdState_3445_; lean_object* v___x_3446_; 
v_elabSnap_3442_ = lean_ctor_get(v_snap_3437_, 3);
lean_inc_ref(v_elabSnap_3442_);
lean_dec_ref(v_snap_3437_);
v_resultSnap_3443_ = lean_ctor_get(v_elabSnap_3442_, 2);
lean_inc_ref(v_resultSnap_3443_);
lean_dec_ref(v_elabSnap_3442_);
v___x_3444_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3443_);
v_cmdState_3445_ = lean_ctor_get(v___x_3444_, 1);
lean_inc_ref(v_cmdState_3445_);
lean_dec(v___x_3444_);
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_cmdState_3445_);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3447_){
_start:
{
lean_object* v_result_x3f_3448_; 
v_result_x3f_3448_ = lean_ctor_get(v_snap_3447_, 4);
lean_inc(v_result_x3f_3448_);
lean_dec_ref(v_snap_3447_);
if (lean_obj_tag(v_result_x3f_3448_) == 0)
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_box(0);
return v___x_3449_;
}
else
{
lean_object* v_val_3450_; lean_object* v_processedSnap_3451_; lean_object* v___x_3452_; lean_object* v_result_x3f_3453_; 
v_val_3450_ = lean_ctor_get(v_result_x3f_3448_, 0);
lean_inc(v_val_3450_);
lean_dec_ref(v_result_x3f_3448_);
v_processedSnap_3451_ = lean_ctor_get(v_val_3450_, 1);
lean_inc_ref(v_processedSnap_3451_);
lean_dec(v_val_3450_);
v___x_3452_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3451_);
v_result_x3f_3453_ = lean_ctor_get(v___x_3452_, 2);
lean_inc(v_result_x3f_3453_);
lean_dec(v___x_3452_);
if (lean_obj_tag(v_result_x3f_3453_) == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_box(0);
return v___x_3454_;
}
else
{
lean_object* v_val_3455_; lean_object* v_firstCmdSnap_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_val_3455_ = lean_ctor_get(v_result_x3f_3453_, 0);
lean_inc(v_val_3455_);
lean_dec_ref(v_result_x3f_3453_);
v_firstCmdSnap_3456_ = lean_ctor_get(v_val_3455_, 1);
lean_inc_ref(v_firstCmdSnap_3456_);
lean_dec(v_val_3455_);
v___x_3457_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3456_);
v___x_3458_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3457_);
return v___x_3458_;
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

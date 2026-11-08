// Lean compiler output
// Module: Lean.Language.Lean
// Imports: public import Lean.Language.Util public import Lean.Language.Lean.Types public import Lean.Language.Lean.Util public import Lean.Elab.Import
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
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_IO_CancelToken_new();
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
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
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Elab_Command_runModuleLintersAsync(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
extern lean_object* l_Lean_internal_cmdlineSnapshots;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_ofPrefix(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_Parser_instInhabitedModuleParserState_default;
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_eqWithInfo(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotLeaf;
extern lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_parseHeader(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
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
lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
lean_object* l_Lean_List_toPArray_x27___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
extern lean_object* l_Lean_trace_profiler_serve;
extern lean_object* l_Lean_instInhabitedTraceState_default;
lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0 = (const lean_object*)&l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg();
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object*);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__0_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "info"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(237, 108, 214, 181, 226, 69, 54, 12)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snapshotTree"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 136, 72, 78, 187, 126, 217, 153)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parseCmd"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3;
static const lean_array_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parsing"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_import"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 157, 171, 65, 170, 18, 92, 252)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(12, 104, 192, 143, 94, 68, 237, 67)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "processHeader"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___lam__0(lean_object* v_00_u03b1_14_, lean_object* v_act_15_, lean_object* v_ctx_16_){
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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg(){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = ((lean_object*)(l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0));
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___boxed(lean_object* v___dummy_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg();
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(lean_object* v_m_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = ((lean_object*)(l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0));
return v___f_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg(lean_object* v_act_26_, lean_object* v_oldInputCtx_x3f_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___y_31_; 
if (lean_obj_tag(v_oldInputCtx_x3f_27_) == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(0);
v___y_31_ = v___x_34_;
goto v___jp_30_;
}
else
{
lean_object* v_val_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_45_; 
v_val_35_ = lean_ctor_get(v_oldInputCtx_x3f_27_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_oldInputCtx_x3f_27_);
if (v_isSharedCheck_45_ == 0)
{
v___x_37_ = v_oldInputCtx_x3f_27_;
v_isShared_38_ = v_isSharedCheck_45_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_val_35_);
lean_dec(v_oldInputCtx_x3f_27_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_45_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v_inputString_39_; lean_object* v_inputString_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v_inputString_39_ = lean_ctor_get(v_val_35_, 0);
lean_inc_ref(v_inputString_39_);
lean_dec(v_val_35_);
v_inputString_40_ = lean_ctor_get(v_a_28_, 0);
v___x_41_ = l_String_firstDiffPos(v_inputString_39_, v_inputString_40_);
lean_dec_ref(v_inputString_39_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_41_);
v___x_43_ = v___x_37_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
v___y_31_ = v___x_43_;
goto v___jp_30_;
}
}
}
v___jp_30_:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_inc_ref(v_a_28_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v_a_28_);
lean_ctor_set(v___x_32_, 1, v___y_31_);
v___x_33_ = lean_apply_2(v_act_26_, v___x_32_, lean_box(0));
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg___boxed(lean_object* v_act_46_, lean_object* v_oldInputCtx_x3f_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_46_, v_oldInputCtx_x3f_47_, v_a_48_);
lean_dec_ref(v_a_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run(lean_object* v_00_u03b1_51_, lean_object* v_act_52_, lean_object* v_oldInputCtx_x3f_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_52_, v_oldInputCtx_x3f_53_, v_a_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___boxed(lean_object* v_00_u03b1_57_, lean_object* v_act_58_, lean_object* v_oldInputCtx_x3f_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Language_Lean_LeanProcessingM_run(v_00_u03b1_57_, v_act_58_, v_oldInputCtx_x3f_59_, v_a_60_);
lean_dec_ref(v_a_60_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_Lean_isBeforeEditPos(lean_object* v_pos_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_firstDiffPos_x3f_66_; 
v_firstDiffPos_x3f_66_ = lean_ctor_get(v_a_64_, 1);
if (lean_obj_tag(v_firstDiffPos_x3f_66_) == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_val_68_ = lean_ctor_get(v_firstDiffPos_x3f_66_, 0);
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = lean_nat_add(v_pos_63_, v___x_69_);
v___x_71_ = lean_nat_dec_le(v___x_70_, v_val_68_);
lean_dec(v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object* v_pos_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_72_, v_a_73_);
lean_dec_ref(v_a_73_);
lean_dec(v_pos_72_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13(void){
_start:
{
uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = 1;
v___x_109_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12));
v___x_110_ = l_Lean_Name_toString(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_unsigned_to_nat(32u);
v___x_112_ = lean_mk_empty_array_with_capacity(v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15(void){
_start:
{
size_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((size_t)5ULL);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_unsigned_to_nat(32u);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_116_);
v___x_118_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_119_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_115_);
lean_ctor_set(v___x_119_, 3, v___x_115_);
lean_ctor_set_usize(v___x_119_, 4, v___x_114_);
return v___x_119_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16(void){
_start:
{
lean_object* v___x_120_; uint64_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15);
v___x_121_ = 0ULL;
v___x_122_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint64(v___x_122_, sizeof(void*)*1, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(lean_object* v_ex_123_, lean_object* v_act_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
lean_inc_ref(v_a_125_);
v___x_127_ = lean_apply_2(v_act_124_, v_a_125_, lean_box(0));
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; 
lean_dec(v_ex_123_);
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
return v_a_128_;
}
else
{
lean_object* v_a_129_; lean_object* v_toProcessingContext_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_129_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_127_, 1);
v_toProcessingContext_130_ = lean_ctor_get(v_a_125_, 0);
v___x_131_ = lean_io_error_to_string(v_a_129_);
v___x_132_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_131_, v_toProcessingContext_130_);
v___x_133_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13);
v___x_134_ = lean_box(0);
v___x_135_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_136_ = 0;
v___x_137_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_137_, 0, v___x_133_);
lean_ctor_set(v___x_137_, 1, v___x_132_);
lean_ctor_set(v___x_137_, 2, v___x_134_);
lean_ctor_set(v___x_137_, 3, v___x_135_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*4, v___x_136_);
v___x_138_ = lean_apply_1(v_ex_123_, v___x_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___boxed(lean_object* v_ex_139_, lean_object* v_act_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_139_, v_act_140_, v_a_141_);
lean_dec_ref(v_a_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object* v_00_u03b1_144_, lean_object* v_ex_145_, lean_object* v_act_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_145_, v_act_146_, v_a_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed(lean_object* v_00_u03b1_150_, lean_object* v_ex_151_, lean_object* v_act_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(v_00_u03b1_150_, v_ex_151_, v_act_152_, v_a_153_);
lean_dec_ref(v_a_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(lean_object* v_o_159_, lean_object* v_k_160_, uint8_t v_v_161_){
_start:
{
lean_object* v_map_162_; uint8_t v_hasTrace_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_177_; 
v_map_162_ = lean_ctor_get(v_o_159_, 0);
v_hasTrace_163_ = lean_ctor_get_uint8(v_o_159_, sizeof(void*)*1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_o_159_);
if (v_isSharedCheck_177_ == 0)
{
v___x_165_ = v_o_159_;
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_map_162_);
lean_dec(v_o_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_177_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_167_, 0, v_v_161_);
lean_inc(v_k_160_);
v___x_168_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_160_, v___x_167_, v_map_162_);
if (v_hasTrace_163_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_172_; 
v___x_169_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_170_ = l_Lean_Name_isPrefixOf(v___x_169_, v_k_160_);
lean_dec(v_k_160_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_168_);
v___x_172_ = v___x_165_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_168_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v___x_170_);
return v___x_172_;
}
}
else
{
lean_object* v___x_175_; 
lean_dec(v_k_160_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_168_);
v___x_175_ = v___x_165_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, sizeof(void*)*1, v_hasTrace_163_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___boxed(lean_object* v_o_178_, lean_object* v_k_179_, lean_object* v_v_180_){
_start:
{
uint8_t v_v_boxed_181_; lean_object* v_res_182_; 
v_v_boxed_181_ = lean_unbox(v_v_180_);
v_res_182_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_o_178_, v_k_179_, v_v_boxed_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(lean_object* v_o_183_, lean_object* v_k_184_, lean_object* v_v_185_){
_start:
{
lean_object* v_map_186_; uint8_t v_hasTrace_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_201_; 
v_map_186_ = lean_ctor_get(v_o_183_, 0);
v_hasTrace_187_ = lean_ctor_get_uint8(v_o_183_, sizeof(void*)*1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_o_183_);
if (v_isSharedCheck_201_ == 0)
{
v___x_189_ = v_o_183_;
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_map_186_);
lean_dec(v_o_183_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_191_, 0, v_v_185_);
lean_inc(v_k_184_);
v___x_192_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_184_, v___x_191_, v_map_186_);
if (v_hasTrace_187_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_196_; 
v___x_193_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_194_ = l_Lean_Name_isPrefixOf(v___x_193_, v_k_184_);
lean_dec(v_k_184_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_196_ = v___x_189_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_192_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*1, v___x_194_);
return v___x_196_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_k_184_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_199_ = v___x_189_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_200_, sizeof(void*)*1, v_hasTrace_187_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(lean_object* v_o_202_, lean_object* v_k_203_, lean_object* v_v_204_){
_start:
{
lean_object* v_map_205_; uint8_t v_hasTrace_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_220_; 
v_map_205_ = lean_ctor_get(v_o_202_, 0);
v_hasTrace_206_ = lean_ctor_get_uint8(v_o_202_, sizeof(void*)*1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_o_202_);
if (v_isSharedCheck_220_ == 0)
{
v___x_208_ = v_o_202_;
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_map_205_);
lean_dec(v_o_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_v_204_);
lean_inc(v_k_203_);
v___x_211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_203_, v___x_210_, v_map_205_);
if (v_hasTrace_206_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_215_; 
v___x_212_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_213_ = l_Lean_Name_isPrefixOf(v___x_212_, v_k_203_);
lean_dec(v_k_203_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_215_ = v___x_208_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_211_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*1, v___x_213_);
return v___x_215_;
}
}
else
{
lean_object* v___x_218_; 
lean_dec(v_k_203_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_218_ = v___x_208_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*1, v_hasTrace_206_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption(lean_object* v_opts_228_, lean_object* v_decl_229_, lean_object* v_name_230_, lean_object* v_val_231_){
_start:
{
lean_object* v_defValue_233_; 
v_defValue_233_ = lean_ctor_get(v_decl_229_, 2);
lean_inc_ref(v_defValue_233_);
lean_dec_ref(v_decl_229_);
switch(lean_obj_tag(v_defValue_233_))
{
case 1:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
lean_dec_ref_known(v_defValue_233_, 0);
v___x_234_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__0));
v___x_235_ = lean_string_dec_eq(v_val_231_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__1));
v___x_237_ = lean_string_dec_eq(v_val_231_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_name_230_);
lean_dec_ref(v_opts_228_);
v___x_238_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_239_ = lean_string_append(v___x_238_, v_val_231_);
lean_dec_ref(v_val_231_);
v___x_240_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__3));
v___x_241_ = lean_string_append(v___x_239_, v___x_240_);
v___x_242_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_val_231_);
v___x_244_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_228_, v_name_230_, v___x_235_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v_val_231_);
v___x_246_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_228_, v_name_230_, v___x_235_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
case 3:
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_272_; 
v_isSharedCheck_272_ = !lean_is_exclusive(v_defValue_233_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v_defValue_233_, 0);
lean_dec(v_unused_273_);
v___x_249_ = v_defValue_233_;
v_isShared_250_ = v_isSharedCheck_272_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_defValue_233_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_272_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_string_utf8_byte_size(v_val_231_);
lean_inc_ref(v_val_231_);
v___x_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_253_, 0, v_val_231_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
v___x_254_ = l_String_Slice_toNat_x3f(v___x_253_);
lean_dec_ref_known(v___x_253_, 3);
if (lean_obj_tag(v___x_254_) == 1)
{
lean_object* v_val_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_val_231_);
v_val_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_val_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(v_opts_228_, v_name_230_, v_val_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 0);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v___x_254_);
lean_dec(v_name_230_);
lean_dec_ref(v_opts_228_);
v___x_264_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_265_ = lean_string_append(v___x_264_, v_val_231_);
lean_dec_ref(v_val_231_);
v___x_266_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__4));
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 18);
lean_ctor_set(v___x_249_, 0, v___x_267_);
v___x_269_ = v___x_249_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_271_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
}
case 0:
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v_defValue_233_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_defValue_233_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v_defValue_233_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_defValue_233_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(v_opts_228_, v_name_230_, v_val_231_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
default: 
{
lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec_ref(v_defValue_233_);
lean_dec_ref(v_val_231_);
lean_dec_ref(v_opts_228_);
v___x_283_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__5));
v___x_284_ = 1;
v___x_285_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_230_, v___x_284_);
v___x_286_ = lean_string_append(v___x_283_, v___x_285_);
lean_dec_ref(v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__6));
v___x_288_ = lean_string_append(v___x_286_, v___x_287_);
v___x_289_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption___boxed(lean_object* v_opts_291_, lean_object* v_decl_292_, lean_object* v_name_293_, lean_object* v_val_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Language_Lean_setOption(v_opts_291_, v_decl_292_, v_name_293_, v_val_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(lean_object* v_o_297_, lean_object* v_k_298_, lean_object* v_v_299_){
_start:
{
lean_object* v_map_300_; uint8_t v_hasTrace_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_314_; 
v_map_300_ = lean_ctor_get(v_o_297_, 0);
v_hasTrace_301_ = lean_ctor_get_uint8(v_o_297_, sizeof(void*)*1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_o_297_);
if (v_isSharedCheck_314_ == 0)
{
v___x_303_ = v_o_297_;
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_map_300_);
lean_dec(v_o_297_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; 
lean_inc(v_k_298_);
v___x_305_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_298_, v_v_299_, v_map_300_);
if (v_hasTrace_301_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_309_; 
v___x_306_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_307_ = l_Lean_Name_isPrefixOf(v___x_306_, v_k_298_);
lean_dec(v_k_298_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_309_ = v___x_303_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_305_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_307_);
return v___x_309_;
}
}
else
{
lean_object* v___x_312_; 
lean_dec(v_k_298_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_312_ = v___x_303_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*1, v_hasTrace_301_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object* v_a_321_, lean_object* v_init_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_l_327_; lean_object* v_r_328_; lean_object* v___x_329_; 
v_k_325_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_k_325_);
v_v_326_ = lean_ctor_get(v_x_323_, 2);
lean_inc(v_v_326_);
v_l_327_ = lean_ctor_get(v_x_323_, 3);
lean_inc(v_l_327_);
v_r_328_ = lean_ctor_get(v_x_323_, 4);
lean_inc(v_r_328_);
lean_dec_ref_known(v_x_323_, 5);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_321_, v_init_322_, v_l_327_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_378_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_378_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_378_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_378_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_377_; 
v_a_334_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_377_ == 0)
{
v___x_336_ = v_a_330_;
v_isShared_337_ = v_isSharedCheck_377_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v_a_330_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_377_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_338_ = l_Lean_Name_getRoot(v_k_325_);
v___x_339_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1));
v___x_340_ = lean_box(0);
v___x_341_ = l_Lean_Name_replacePrefix(v_k_325_, v___x_339_, v___x_340_);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_321_, v___x_341_);
if (lean_obj_tag(v___x_342_) == 1)
{
lean_dec(v___x_338_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
if (lean_obj_tag(v_v_326_) == 0)
{
lean_object* v_val_343_; lean_object* v_v_344_; lean_object* v___x_345_; 
v_val_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v___x_342_, 1);
v_v_344_ = lean_ctor_get(v_v_326_, 0);
lean_inc_ref(v_v_344_);
lean_dec_ref_known(v_v_326_, 1);
v___x_345_ = l_Lean_Language_Lean_setOption(v_a_334_, v_val_343_, v___x_341_, v_v_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_init_322_ = v_a_346_;
v_x_323_ = v_r_328_;
goto _start;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_r_328_);
v_a_348_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_345_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_345_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v___x_356_; 
lean_dec_ref_known(v___x_342_, 1);
v___x_356_ = l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(v_a_334_, v___x_341_, v_v_326_);
v_init_322_ = v___x_356_;
v_x_323_ = v_r_328_;
goto _start;
}
}
else
{
uint8_t v___x_358_; 
lean_dec(v___x_342_);
lean_dec(v_v_326_);
v___x_358_ = lean_name_eq(v___x_338_, v___x_339_);
lean_dec(v___x_338_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec(v_a_334_);
lean_dec(v_r_328_);
v___x_359_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2));
v___x_360_ = 1;
lean_inc(v___x_341_);
v___x_361_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_341_, v___x_360_);
v___x_362_ = lean_string_append(v___x_359_, v___x_361_);
lean_dec_ref(v___x_361_);
v___x_363_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3));
v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
v___x_365_ = l_Lean_Name_append(v___x_339_, v___x_341_);
v___x_366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_365_, v___x_360_);
v___x_367_ = lean_string_append(v___x_364_, v___x_366_);
lean_dec_ref(v___x_366_);
v___x_368_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4));
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 18);
lean_ctor_set(v___x_336_, 0, v___x_369_);
v___x_371_ = v___x_336_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 1);
lean_ctor_set(v___x_332_, 0, v___x_371_);
v___x_373_ = v___x_332_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_dec(v___x_341_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
v_init_322_ = v_a_334_;
v_x_323_ = v_r_328_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_r_328_);
lean_dec(v_v_326_);
lean_dec(v_k_325_);
return v___x_329_;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_init_322_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object* v_a_381_, lean_object* v_init_382_, lean_object* v_x_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_381_, v_init_382_, v_x_383_);
lean_dec(v_a_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object* v_opts_386_){
_start:
{
lean_object* v_opts_x27_388_; lean_object* v___x_389_; 
v_opts_x27_388_ = l_Lean_Options_empty;
v___x_389_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_map_391_; lean_object* v___x_392_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v_map_391_ = lean_ctor_get(v_opts_386_, 0);
lean_inc(v_map_391_);
lean_dec_ref(v_opts_386_);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_390_, v_opts_x27_388_, v_map_391_);
lean_dec(v_a_390_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_a_397_; lean_object* v___x_399_; 
v_a_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_a_397_);
lean_dec(v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_a_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_392_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_392_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_opts_386_);
v_a_410_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_389_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object* v_opts_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Language_Lean_reparseOptions(v_opts_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object* v_stx_429_){
_start:
{
lean_object* v_stx_431_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = l_Lean_Syntax_getArg(v_stx_429_, v___x_434_);
v___x_436_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3));
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
v_stx_431_ = v_stx_429_;
goto v___jp_430_;
}
else
{
lean_object* v___x_438_; lean_object* v_stx_439_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v_stx_439_ = l_Lean_Syntax_getArg(v_stx_429_, v___x_438_);
lean_dec(v_stx_429_);
v_stx_431_ = v_stx_439_;
goto v___jp_430_;
}
v___jp_430_:
{
uint8_t v___x_432_; lean_object* v___x_433_; 
v___x_432_ = 0;
v___x_433_ = l_Lean_Syntax_getPos_x3f(v_stx_431_, v___x_432_);
lean_dec(v_stx_431_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_440_, lean_object* v_decl_441_, lean_object* v_ref_442_){
_start:
{
lean_object* v_defValue_444_; lean_object* v_descr_445_; lean_object* v_deprecation_x3f_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_defValue_444_ = lean_ctor_get(v_decl_441_, 0);
v_descr_445_ = lean_ctor_get(v_decl_441_, 1);
v_deprecation_x3f_446_ = lean_ctor_get(v_decl_441_, 2);
v___x_447_ = lean_alloc_ctor(1, 0, 1);
v___x_448_ = lean_unbox(v_defValue_444_);
lean_ctor_set_uint8(v___x_447_, 0, v___x_448_);
lean_inc(v_deprecation_x3f_446_);
lean_inc_ref(v_descr_445_);
lean_inc_n(v_name_440_, 2);
v___x_449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_449_, 0, v_name_440_);
lean_ctor_set(v___x_449_, 1, v_ref_442_);
lean_ctor_set(v___x_449_, 2, v___x_447_);
lean_ctor_set(v___x_449_, 3, v_descr_445_);
lean_ctor_set(v___x_449_, 4, v_deprecation_x3f_446_);
v___x_450_ = lean_register_option(v_name_440_, v___x_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_450_, 0);
lean_dec(v_unused_459_);
v___x_452_ = v___x_450_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_dec(v___x_450_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_inc(v_defValue_444_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_name_440_);
lean_ctor_set(v___x_454_, 1, v_defValue_444_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
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
lean_dec(v_name_440_);
v_a_460_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_450_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_450_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_468_, lean_object* v_decl_469_, lean_object* v_ref_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_468_, v_decl_469_, v_ref_470_);
lean_dec_ref(v_decl_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_491_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_492_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_493_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_490_, v___x_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_495_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_unsigned_to_nat(32u);
v___x_497_ = lean_mk_empty_array_with_capacity(v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = ((size_t)5ULL);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_unsigned_to_nat(32u);
v___x_502_ = lean_mk_empty_array_with_capacity(v___x_501_);
v___x_503_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_504_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
lean_ctor_set(v___x_504_, 2, v___x_500_);
lean_ctor_set(v___x_504_, 3, v___x_500_);
lean_ctor_set_usize(v___x_504_, 4, v___x_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v_infoState_508_; lean_object* v_trees_509_; lean_object* v___x_510_; lean_object* v_infoState_511_; lean_object* v_env_512_; lean_object* v_messages_513_; lean_object* v_scopes_514_; lean_object* v_usedQuotCtxts_515_; lean_object* v_nextMacroScope_516_; lean_object* v_maxRecDepth_517_; lean_object* v_ngen_518_; lean_object* v_auxDeclNGen_519_; lean_object* v_traceState_520_; lean_object* v_snapshotTasks_521_; lean_object* v_prevLinterStates_522_; lean_object* v_codeQualityEntryTasks_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_544_; 
v___x_507_ = lean_st_ref_get(v___y_505_);
v_infoState_508_ = lean_ctor_get(v___x_507_, 8);
lean_inc_ref(v_infoState_508_);
lean_dec(v___x_507_);
v_trees_509_ = lean_ctor_get(v_infoState_508_, 2);
lean_inc_ref(v_trees_509_);
lean_dec_ref(v_infoState_508_);
v___x_510_ = lean_st_ref_take(v___y_505_);
v_infoState_511_ = lean_ctor_get(v___x_510_, 8);
v_env_512_ = lean_ctor_get(v___x_510_, 0);
v_messages_513_ = lean_ctor_get(v___x_510_, 1);
v_scopes_514_ = lean_ctor_get(v___x_510_, 2);
v_usedQuotCtxts_515_ = lean_ctor_get(v___x_510_, 3);
v_nextMacroScope_516_ = lean_ctor_get(v___x_510_, 4);
v_maxRecDepth_517_ = lean_ctor_get(v___x_510_, 5);
v_ngen_518_ = lean_ctor_get(v___x_510_, 6);
v_auxDeclNGen_519_ = lean_ctor_get(v___x_510_, 7);
v_traceState_520_ = lean_ctor_get(v___x_510_, 9);
v_snapshotTasks_521_ = lean_ctor_get(v___x_510_, 10);
v_prevLinterStates_522_ = lean_ctor_get(v___x_510_, 11);
v_codeQualityEntryTasks_523_ = lean_ctor_get(v___x_510_, 12);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_544_ == 0)
{
v___x_525_ = v___x_510_;
v_isShared_526_ = v_isSharedCheck_544_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_codeQualityEntryTasks_523_);
lean_inc(v_prevLinterStates_522_);
lean_inc(v_snapshotTasks_521_);
lean_inc(v_traceState_520_);
lean_inc(v_infoState_511_);
lean_inc(v_auxDeclNGen_519_);
lean_inc(v_ngen_518_);
lean_inc(v_maxRecDepth_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_usedQuotCtxts_515_);
lean_inc(v_scopes_514_);
lean_inc(v_messages_513_);
lean_inc(v_env_512_);
lean_dec(v___x_510_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_544_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
uint8_t v_enabled_527_; lean_object* v_assignment_528_; lean_object* v_lazyAssignment_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_542_; 
v_enabled_527_ = lean_ctor_get_uint8(v_infoState_511_, sizeof(void*)*3);
v_assignment_528_ = lean_ctor_get(v_infoState_511_, 0);
v_lazyAssignment_529_ = lean_ctor_get(v_infoState_511_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_infoState_511_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_infoState_511_, 2);
lean_dec(v_unused_543_);
v___x_531_ = v_infoState_511_;
v_isShared_532_ = v_isSharedCheck_542_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_lazyAssignment_529_);
lean_inc(v_assignment_528_);
lean_dec(v_infoState_511_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_542_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_assignment_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_lazyAssignment_529_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v___x_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_541_, sizeof(void*)*3, v_enabled_527_);
v___x_535_ = v_reuseFailAlloc_541_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 8, v___x_535_);
v___x_537_ = v___x_525_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_env_512_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_messages_513_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_scopes_514_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v_usedQuotCtxts_515_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_540_, 5, v_maxRecDepth_517_);
lean_ctor_set(v_reuseFailAlloc_540_, 6, v_ngen_518_);
lean_ctor_set(v_reuseFailAlloc_540_, 7, v_auxDeclNGen_519_);
lean_ctor_set(v_reuseFailAlloc_540_, 8, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_540_, 9, v_traceState_520_);
lean_ctor_set(v_reuseFailAlloc_540_, 10, v_snapshotTasks_521_);
lean_ctor_set(v_reuseFailAlloc_540_, 11, v_prevLinterStates_522_);
lean_ctor_set(v_reuseFailAlloc_540_, 12, v_codeQualityEntryTasks_523_);
v___x_537_ = v_reuseFailAlloc_540_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_st_ref_put(v___y_505_, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_trees_509_);
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_545_);
lean_dec(v___y_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_555_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_556_, lean_object* v_opt_557_){
_start:
{
lean_object* v_name_558_; lean_object* v_defValue_559_; lean_object* v_map_560_; lean_object* v___x_561_; 
v_name_558_ = lean_ctor_get(v_opt_557_, 0);
v_defValue_559_ = lean_ctor_get(v_opt_557_, 1);
v_map_560_ = lean_ctor_get(v_opts_556_, 0);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_560_, v_name_558_);
if (lean_obj_tag(v___x_561_) == 0)
{
uint8_t v___x_562_; 
v___x_562_ = lean_unbox(v_defValue_559_);
return v___x_562_;
}
else
{
lean_object* v_val_563_; 
v_val_563_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v___x_561_, 1);
if (lean_obj_tag(v_val_563_) == 1)
{
uint8_t v_v_564_; 
v_v_564_ = lean_ctor_get_uint8(v_val_563_, 0);
lean_dec_ref_known(v_val_563_, 0);
return v_v_564_;
}
else
{
uint8_t v___x_565_; 
lean_dec(v_val_563_);
v___x_565_ = lean_unbox(v_defValue_559_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_566_, lean_object* v_opt_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_566_, v_opt_567_);
lean_dec_ref(v_opt_567_);
lean_dec_ref(v_opts_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l_Lean_Language_Snapshot_transform(v_val_572_, v___y_573_);
v___x_575_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_577_, v___y_578_);
lean_dec_ref(v___y_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_580_, lean_object* v_val_581_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_inc_ref(v_val_581_);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_582_, 0, v_val_581_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_inst_580_);
lean_ctor_set(v___x_583_, 1, v_val_581_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___f_582_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_585_, lean_object* v_revCmds_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_588_);
lean_dec_ref(v___x_590_);
lean_inc(v_stx_585_);
v___x_591_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_585_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_603_; 
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_604_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_603_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_603_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_Parser_isTerminalCommand(v_stx_585_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec(v_revCmds_586_);
v___x_596_ = lean_box(0);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_del_object(v___x_593_);
v___x_600_ = l_List_reverse___redArg(v_revCmds_586_);
v___x_601_ = lean_array_mk(v___x_600_);
v___x_602_ = l_Lean_Elab_Command_runModuleLintersAsync(v___x_601_, v___y_587_, v___y_588_);
return v___x_602_;
}
}
}
else
{
lean_dec(v_revCmds_586_);
lean_dec(v_stx_585_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_605_, lean_object* v_revCmds_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_605_, v_revCmds_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_610_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_611_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_ctor_set(v___x_616_, 2, v___x_615_);
lean_ctor_set(v___x_616_, 3, v___x_615_);
lean_ctor_set(v___x_616_, 4, v___x_614_);
lean_ctor_set(v___x_616_, 5, v___x_614_);
lean_ctor_set(v___x_616_, 6, v___x_614_);
lean_ctor_set(v___x_616_, 7, v___x_614_);
lean_ctor_set(v___x_616_, 8, v___x_614_);
lean_ctor_set(v___x_616_, 9, v___x_614_);
lean_ctor_set(v___x_616_, 10, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_unsigned_to_nat(32u);
v___x_618_ = lean_mk_empty_array_with_capacity(v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = ((size_t)5ULL);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_unsigned_to_nat(32u);
v___x_623_ = lean_mk_empty_array_with_capacity(v___x_622_);
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_625_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_621_);
lean_ctor_set(v___x_625_, 3, v___x_621_);
lean_ctor_set_usize(v___x_625_, 4, v___x_620_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_box(1);
v___x_627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_626_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_env_634_; uint8_t v___x_635_; lean_object* v_env_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_scopes_639_; lean_object* v___x_640_; lean_object* v_opts_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_633_ = lean_st_ref_get(v___y_631_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
v___x_635_ = 0;
v_env_636_ = l_Lean_Environment_setRecordingDeps(v_env_634_, v___x_635_);
v___x_637_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_638_ = lean_st_ref_get(v___y_631_);
v_scopes_639_ = lean_ctor_get(v___x_638_, 2);
lean_inc(v_scopes_639_);
lean_dec(v___x_638_);
v___x_640_ = l_List_head_x21___redArg(v___x_637_, v_scopes_639_);
lean_dec(v_scopes_639_);
v_opts_641_ = lean_ctor_get(v___x_640_, 1);
lean_inc_ref(v_opts_641_);
lean_dec(v___x_640_);
v___x_642_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_643_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_644_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_644_, 0, v_env_636_);
lean_ctor_set(v___x_644_, 1, v___x_642_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
lean_ctor_set(v___x_644_, 3, v_opts_641_);
v___x_645_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_msgData_630_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_647_, v___y_648_);
lean_dec(v___y_648_);
return v_res_650_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 1)
{
lean_object* v_pre_653_; 
v_pre_653_ = lean_ctor_get(v_x_652_, 0);
if (lean_obj_tag(v_pre_653_) == 0)
{
lean_object* v_str_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_str_654_ = lean_ctor_get(v_x_652_, 1);
v___x_655_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_656_ = lean_string_dec_eq(v_str_654_, v___x_655_);
if (v___x_656_ == 0)
{
return v___x_656_;
}
else
{
return v_suppressElabErrors_651_;
}
}
else
{
uint8_t v___x_657_; 
v___x_657_ = 0;
return v___x_657_;
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_659_, lean_object* v_x_660_){
_start:
{
uint8_t v_suppressElabErrors_boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v_suppressElabErrors_boxed_661_ = lean_unbox(v_suppressElabErrors_659_);
v_res_662_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_661_, v_x_660_);
lean_dec(v_x_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_665_, lean_object* v_msgData_666_, uint8_t v_severity_667_, uint8_t v_isSilent_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; uint8_t v___y_679_; lean_object* v___y_680_; lean_object* v___y_738_; uint8_t v___y_739_; uint8_t v___y_740_; lean_object* v___y_741_; uint8_t v___y_764_; uint8_t v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___y_771_; uint8_t v___y_772_; uint8_t v___x_787_; uint8_t v___y_789_; uint8_t v___x_799_; 
v___x_787_ = 2;
v___x_799_ = l_Lean_instBEqMessageSeverity_beq(v_severity_667_, v___x_787_);
if (v___x_799_ == 0)
{
v___y_789_ = v___x_799_;
goto v___jp_788_;
}
else
{
uint8_t v___x_800_; 
lean_inc_ref(v_msgData_666_);
v___x_800_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_666_);
if (v___x_800_ == 0)
{
v___y_789_ = v___x_800_;
goto v___jp_788_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref(v_msgData_666_);
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
v___jp_672_:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_Command_getScope___redArg(v___y_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_currNamespace_683_; lean_object* v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v_currNamespace_683_ = lean_ctor_get(v_a_682_, 2);
lean_inc(v_currNamespace_683_);
lean_dec(v_a_682_);
v___x_684_ = l_Lean_Elab_Command_getScope___redArg(v___y_680_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_720_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_720_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_720_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_720_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_openDecls_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_env_694_; lean_object* v_messages_695_; lean_object* v_scopes_696_; lean_object* v_usedQuotCtxts_697_; lean_object* v_nextMacroScope_698_; lean_object* v_maxRecDepth_699_; lean_object* v_ngen_700_; lean_object* v_auxDeclNGen_701_; lean_object* v_infoState_702_; lean_object* v_traceState_703_; lean_object* v_snapshotTasks_704_; lean_object* v_prevLinterStates_705_; lean_object* v_codeQualityEntryTasks_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_719_; 
v_openDecls_689_ = lean_ctor_get(v_a_685_, 3);
lean_inc(v_openDecls_689_);
lean_dec(v_a_685_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_currNamespace_683_);
lean_ctor_set(v___x_690_, 1, v_openDecls_689_);
v___x_691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___y_674_);
lean_inc_ref(v___y_676_);
lean_inc_ref(v___y_678_);
v___x_692_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_692_, 0, v___y_678_);
lean_ctor_set(v___x_692_, 1, v___y_675_);
lean_ctor_set(v___x_692_, 2, v___y_677_);
lean_ctor_set(v___x_692_, 3, v___y_676_);
lean_ctor_set(v___x_692_, 4, v___x_691_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*5, v___y_679_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*5 + 1, v___y_673_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*5 + 2, v_isSilent_668_);
v___x_693_ = lean_st_ref_take(v___y_680_);
v_env_694_ = lean_ctor_get(v___x_693_, 0);
v_messages_695_ = lean_ctor_get(v___x_693_, 1);
v_scopes_696_ = lean_ctor_get(v___x_693_, 2);
v_usedQuotCtxts_697_ = lean_ctor_get(v___x_693_, 3);
v_nextMacroScope_698_ = lean_ctor_get(v___x_693_, 4);
v_maxRecDepth_699_ = lean_ctor_get(v___x_693_, 5);
v_ngen_700_ = lean_ctor_get(v___x_693_, 6);
v_auxDeclNGen_701_ = lean_ctor_get(v___x_693_, 7);
v_infoState_702_ = lean_ctor_get(v___x_693_, 8);
v_traceState_703_ = lean_ctor_get(v___x_693_, 9);
v_snapshotTasks_704_ = lean_ctor_get(v___x_693_, 10);
v_prevLinterStates_705_ = lean_ctor_get(v___x_693_, 11);
v_codeQualityEntryTasks_706_ = lean_ctor_get(v___x_693_, 12);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_719_ == 0)
{
v___x_708_ = v___x_693_;
v_isShared_709_ = v_isSharedCheck_719_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_codeQualityEntryTasks_706_);
lean_inc(v_prevLinterStates_705_);
lean_inc(v_snapshotTasks_704_);
lean_inc(v_traceState_703_);
lean_inc(v_infoState_702_);
lean_inc(v_auxDeclNGen_701_);
lean_inc(v_ngen_700_);
lean_inc(v_maxRecDepth_699_);
lean_inc(v_nextMacroScope_698_);
lean_inc(v_usedQuotCtxts_697_);
lean_inc(v_scopes_696_);
lean_inc(v_messages_695_);
lean_inc(v_env_694_);
lean_dec(v___x_693_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_719_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_box(0);
v___x_711_ = l_Lean_MessageLog_add(v___x_692_, v_messages_695_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_env_694_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_scopes_696_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_usedQuotCtxts_697_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_nextMacroScope_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_maxRecDepth_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_ngen_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_auxDeclNGen_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_infoState_702_);
lean_ctor_set(v_reuseFailAlloc_718_, 9, v_traceState_703_);
lean_ctor_set(v_reuseFailAlloc_718_, 10, v_snapshotTasks_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 11, v_prevLinterStates_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 12, v_codeQualityEntryTasks_706_);
v___x_713_ = v_reuseFailAlloc_718_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_st_ref_put(v___y_680_, v___x_713_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_710_);
v___x_716_ = v___x_687_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_710_);
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
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_currNamespace_683_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_674_);
v_a_721_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_684_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_684_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v___y_677_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___y_674_);
v_a_729_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_681_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_681_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
v___jp_737_:
{
lean_object* v_fileName_742_; lean_object* v_fileMap_743_; uint8_t v_suppressElabErrors_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_762_; 
v_fileName_742_ = lean_ctor_get(v___y_669_, 0);
v_fileMap_743_ = lean_ctor_get(v___y_669_, 1);
v_suppressElabErrors_744_ = lean_ctor_get_uint8(v___y_669_, sizeof(void*)*10);
v___x_745_ = lean_box(v_suppressElabErrors_744_);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 2, 1);
lean_closure_set(v___f_746_, 0, v___x_745_);
v___x_747_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_666_);
v___x_748_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_747_, v___y_670_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_762_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_762_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_762_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_inc_ref_n(v_fileMap_743_, 2);
v___x_753_ = l_Lean_FileMap_toPosition(v_fileMap_743_, v___y_738_);
lean_dec(v___y_738_);
v___x_754_ = l_Lean_FileMap_toPosition(v_fileMap_743_, v___y_741_);
lean_dec(v___y_741_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_744_ == 0)
{
lean_del_object(v___x_751_);
lean_dec_ref(v___f_746_);
v___y_673_ = v___y_739_;
v___y_674_ = v_a_749_;
v___y_675_ = v___x_753_;
v___y_676_ = v___x_756_;
v___y_677_ = v___x_755_;
v___y_678_ = v_fileName_742_;
v___y_679_ = v___y_740_;
v___y_680_ = v___y_670_;
goto v___jp_672_;
}
else
{
uint8_t v___x_757_; 
lean_inc(v_a_749_);
v___x_757_ = l_Lean_MessageData_hasTag(v___f_746_, v_a_749_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_dec_ref_known(v___x_755_, 1);
lean_dec_ref(v___x_753_);
lean_dec(v_a_749_);
v___x_758_ = lean_box(0);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_758_);
v___x_760_ = v___x_751_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_del_object(v___x_751_);
v___y_673_ = v___y_739_;
v___y_674_ = v_a_749_;
v___y_675_ = v___x_753_;
v___y_676_ = v___x_756_;
v___y_677_ = v___x_755_;
v___y_678_ = v_fileName_742_;
v___y_679_ = v___y_740_;
v___y_680_ = v___y_670_;
goto v___jp_672_;
}
}
}
}
v___jp_763_:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Syntax_getTailPos_x3f(v___y_766_, v___y_765_);
lean_dec(v___y_766_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_inc(v___y_767_);
v___y_738_ = v___y_767_;
v___y_739_ = v___y_764_;
v___y_740_ = v___y_765_;
v___y_741_ = v___y_767_;
goto v___jp_737_;
}
else
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_768_, 1);
v___y_738_ = v___y_767_;
v___y_739_ = v___y_764_;
v___y_740_ = v___y_765_;
v___y_741_ = v_val_769_;
goto v___jp_737_;
}
}
v___jp_770_:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Elab_Command_getRef___redArg(v___y_669_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_ref_775_; lean_object* v___x_776_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v_ref_775_ = l_Lean_replaceRef(v_ref_665_, v_a_774_);
lean_dec(v_a_774_);
v___x_776_ = l_Lean_Syntax_getPos_x3f(v_ref_775_, v___y_771_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___y_764_ = v___y_772_;
v___y_765_ = v___y_771_;
v___y_766_ = v_ref_775_;
v___y_767_ = v___x_777_;
goto v___jp_763_;
}
else
{
lean_object* v_val_778_; 
v_val_778_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v___x_776_, 1);
v___y_764_ = v___y_772_;
v___y_765_ = v___y_771_;
v___y_766_ = v_ref_775_;
v___y_767_ = v_val_778_;
goto v___jp_763_;
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v_msgData_666_);
v_a_779_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_773_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_773_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
v___jp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_scopes_792_; lean_object* v___x_793_; lean_object* v_opts_794_; uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_790_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_791_ = lean_st_ref_get(v___y_670_);
v_scopes_792_ = lean_ctor_get(v___x_791_, 2);
lean_inc(v_scopes_792_);
lean_dec(v___x_791_);
v___x_793_ = l_List_head_x21___redArg(v___x_790_, v_scopes_792_);
lean_dec(v_scopes_792_);
v_opts_794_ = lean_ctor_get(v___x_793_, 1);
lean_inc_ref(v_opts_794_);
lean_dec(v___x_793_);
v___x_795_ = 1;
v___x_796_ = l_Lean_instBEqMessageSeverity_beq(v_severity_667_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_opts_794_);
v___y_771_ = v___y_789_;
v___y_772_ = v_severity_667_;
goto v___jp_770_;
}
else
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = l_Lean_warningAsError;
v___x_798_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_794_, v___x_797_);
lean_dec_ref(v_opts_794_);
if (v___x_798_ == 0)
{
v___y_771_ = v___y_789_;
v___y_772_ = v_severity_667_;
goto v___jp_770_;
}
else
{
v___y_771_ = v___y_789_;
v___y_772_ = v___x_787_;
goto v___jp_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_803_, lean_object* v_msgData_804_, lean_object* v_severity_805_, lean_object* v_isSilent_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_severity_boxed_810_; uint8_t v_isSilent_boxed_811_; lean_object* v_res_812_; 
v_severity_boxed_810_ = lean_unbox(v_severity_805_);
v_isSilent_boxed_811_ = lean_unbox(v_isSilent_806_);
v_res_812_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_803_, v_msgData_804_, v_severity_boxed_810_, v_isSilent_boxed_811_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_ref_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_813_, uint8_t v_severity_814_, uint8_t v_isSilent_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Elab_Command_getRef___redArg(v___y_816_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_820_, v_msgData_813_, v_severity_814_, v_isSilent_815_, v___y_816_, v___y_817_);
lean_dec(v_a_820_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v_msgData_813_);
v_a_822_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_819_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_819_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_830_, lean_object* v_severity_831_, lean_object* v_isSilent_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_severity_boxed_836_; uint8_t v_isSilent_boxed_837_; lean_object* v_res_838_; 
v_severity_boxed_836_ = lean_unbox(v_severity_831_);
v_isSilent_boxed_837_ = lean_unbox(v_isSilent_832_);
v_res_838_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_830_, v_severity_boxed_836_, v_isSilent_boxed_837_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
uint8_t v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; 
v___x_843_ = 2;
v___x_844_ = 0;
v___x_845_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_839_, v___x_843_, v___x_844_, v___y_840_, v___y_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_851_, lean_object* v_msgData_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; 
v___x_856_ = 2;
v___x_857_ = 0;
v___x_858_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_851_, v_msgData_852_, v___x_856_, v___x_857_, v___y_853_, v___y_854_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_859_, lean_object* v_msgData_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_859_, v_msgData_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v_ref_859_);
return v_res_864_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
if (lean_obj_tag(v_ex_868_) == 0)
{
lean_object* v_ref_875_; lean_object* v_msg_876_; lean_object* v___x_877_; 
v_ref_875_ = lean_ctor_get(v_ex_868_, 0);
lean_inc(v_ref_875_);
v_msg_876_ = lean_ctor_get(v_ex_868_, 1);
lean_inc_ref(v_msg_876_);
lean_dec_ref_known(v_ex_868_, 2);
v___x_877_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_875_, v_msg_876_, v___y_869_, v___y_870_);
lean_dec(v_ref_875_);
return v___x_877_;
}
else
{
lean_object* v_id_878_; uint8_t v___x_879_; 
v_id_878_ = lean_ctor_get(v_ex_868_, 0);
lean_inc(v_id_878_);
v___x_879_ = l_Lean_Elab_isAbortExceptionId(v_id_878_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_905_; 
v___x_880_ = l_Lean_Exception_isInterrupt(v_ex_868_);
v_isSharedCheck_905_ = !lean_is_exclusive(v_ex_868_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; lean_object* v_unused_907_; 
v_unused_906_ = lean_ctor_get(v_ex_868_, 1);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_ex_868_, 0);
lean_dec(v_unused_907_);
v___x_882_ = v_ex_868_;
v_isShared_883_ = v_isSharedCheck_905_;
goto v_resetjp_881_;
}
else
{
lean_dec(v_ex_868_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_905_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
if (v___x_880_ == 0)
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_InternalExceptionId_getName(v_id_878_);
lean_dec(v_id_878_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_del_object(v___x_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_887_ = l_Lean_MessageData_ofName(v_a_885_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_888_, v___y_869_, v___y_870_);
return v___x_889_;
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_904_; 
v_a_890_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_904_ == 0)
{
v___x_892_ = v___x_884_;
v_isShared_893_ = v_isSharedCheck_904_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_884_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_904_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_ref_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v_ref_894_ = lean_ctor_get(v___y_869_, 7);
v___x_895_ = lean_io_error_to_string(v_a_890_);
v___x_896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
v___x_897_ = l_Lean_MessageData_ofFormat(v___x_896_);
lean_inc(v_ref_894_);
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 0);
lean_ctor_set(v___x_882_, 1, v___x_897_);
lean_ctor_set(v___x_882_, 0, v_ref_894_);
v___x_899_ = v___x_882_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_ref_894_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_899_);
v___x_901_ = v___x_892_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
else
{
lean_del_object(v___x_882_);
lean_dec(v_id_878_);
goto v___jp_872_;
}
}
}
else
{
lean_dec(v_id_878_);
lean_dec_ref_known(v_ex_868_, 2);
goto v___jp_872_;
}
}
v___jp_872_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_917_ = lean_apply_3(v_x_913_, v___y_914_, v___y_915_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
return v___x_917_;
}
else
{
lean_object* v_a_918_; uint8_t v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
v___x_919_ = l_Lean_Exception_isInterrupt(v_a_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_920_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_918_, v___y_914_, v___y_915_);
return v___x_920_;
}
else
{
lean_dec(v_a_918_);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_926_, lean_object* v___x_927_, lean_object* v_val_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_a_932_; lean_object* v___x_934_; 
v___x_934_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_926_, v___x_927_, v_val_928_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v_a_932_ = v_a_935_;
goto v___jp_931_;
}
else
{
lean_object* v___x_936_; 
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = lean_box(0);
v_a_932_ = v___x_936_;
goto v___jp_931_;
}
v___jp_931_:
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v_a_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_937_, lean_object* v___x_938_, lean_object* v_val_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_937_, v___x_938_, v_val_939_, v___y_940_);
lean_dec_ref(v___y_940_);
lean_dec(v_val_939_);
lean_dec_ref(v___x_938_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_943_, lean_object* v_x_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_get_set_stderr(v_h_943_);
lean_inc_ref(v___y_945_);
v___x_948_ = lean_apply_2(v_x_944_, v___y_945_, lean_box(0));
v___x_949_ = lean_get_set_stderr(v___x_947_);
lean_dec_ref(v___x_949_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_950_, v_x_951_, v___y_952_);
lean_dec_ref(v___y_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_955_, lean_object* v_h_956_, lean_object* v_x_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_956_, v_x_957_, v___y_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_961_, lean_object* v_h_962_, lean_object* v_x_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_961_, v_h_962_, v_x_963_, v___y_964_);
lean_dec_ref(v___y_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_967_, lean_object* v_x_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_get_set_stdin(v_h_967_);
lean_inc_ref(v___y_969_);
v___x_972_ = lean_apply_2(v_x_968_, v___y_969_, lean_box(0));
v___x_973_ = lean_get_set_stdin(v___x_971_);
lean_dec_ref(v___x_973_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_974_, v_x_975_, v___y_976_);
lean_dec_ref(v___y_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_981_ = lean_panic_fn_borrowed(v___x_980_, v_msg_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_982_, lean_object* v_x_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_get_set_stdout(v_h_982_);
lean_inc_ref(v___y_984_);
v___x_987_ = lean_apply_2(v_x_983_, v___y_984_, lean_box(0));
v___x_988_ = lean_get_set_stdout(v___x_986_);
lean_dec_ref(v___x_988_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_989_, v_x_990_, v___y_991_);
lean_dec_ref(v___y_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_994_, lean_object* v_h_995_, lean_object* v_x_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_995_, v_x_996_, v___y_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1000_, lean_object* v_h_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1000_, v_h_1001_, v_x_1002_, v___y_1003_);
lean_dec_ref(v___y_1003_);
return v_res_1005_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = l_ByteArray_empty;
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1012_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1013_ = lean_unsigned_to_nat(46u);
v___x_1014_ = lean_unsigned_to_nat(193u);
v___x_1015_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1016_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1017_ = l_mkPanicMessageWithDecl(v___x_1016_, v___x_1015_, v___x_1014_, v___x_1013_, v___x_1012_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1018_, uint8_t v_isolateStderr_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___y_1032_; 
v___x_1026_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1027_ = lean_st_mk_ref(v___x_1026_);
v___x_1028_ = lean_st_mk_ref(v___x_1026_);
v___x_1029_ = l_IO_FS_Stream_ofBuffer(v___x_1027_);
lean_inc(v___x_1028_);
v___x_1030_ = l_IO_FS_Stream_ofBuffer(v___x_1028_);
if (v_isolateStderr_1019_ == 0)
{
v___y_1032_ = v_x_1018_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1041_; 
lean_inc_ref(v___x_1030_);
v___x_1041_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1041_, 0, lean_box(0));
lean_closure_set(v___x_1041_, 1, v___x_1030_);
lean_closure_set(v___x_1041_, 2, v_x_1018_);
v___y_1032_ = v___x_1041_;
goto v___jp_1031_;
}
v___jp_1022_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___y_1024_);
lean_ctor_set(v___x_1025_, 1, v___y_1023_);
return v___x_1025_;
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v_data_1036_; uint8_t v___x_1037_; 
v___x_1033_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1033_, 0, lean_box(0));
lean_closure_set(v___x_1033_, 1, v___x_1030_);
lean_closure_set(v___x_1033_, 2, v___y_1032_);
v___x_1034_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1029_, v___x_1033_, v___y_1020_);
v___x_1035_ = lean_st_ref_get(v___x_1028_);
lean_dec(v___x_1028_);
v_data_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref(v_data_1036_);
lean_dec(v___x_1035_);
v___x_1037_ = lean_string_validate_utf8(v_data_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref(v_data_1036_);
v___x_1038_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1039_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1038_);
v___y_1023_ = v___x_1034_;
v___y_1024_ = v___x_1039_;
goto v___jp_1022_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_string_from_utf8_unchecked(v_data_1036_);
v___y_1023_ = v___x_1034_;
v___y_1024_ = v___x_1040_;
goto v___jp_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1042_, lean_object* v_isolateStderr_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v_isolateStderr_boxed_1046_; lean_object* v_res_1047_; 
v_isolateStderr_boxed_1046_ = lean_unbox(v_isolateStderr_1043_);
v_res_1047_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1042_, v_isolateStderr_boxed_1046_, v___y_1044_);
lean_dec_ref(v___y_1044_);
return v_res_1047_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = 1;
v___x_1057_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1058_ = l_Lean_Name_toString(v___x_1057_, v___x_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1059_, lean_object* v_revCmds_1060_, lean_object* v_cmdState_1061_, lean_object* v_beginPos_1062_, lean_object* v_snap_1063_, lean_object* v_cancelTk_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_env_1067_; lean_object* v_scopes_1068_; lean_object* v_usedQuotCtxts_1069_; lean_object* v_nextMacroScope_1070_; lean_object* v_maxRecDepth_1071_; lean_object* v_ngen_1072_; lean_object* v_auxDeclNGen_1073_; lean_object* v_infoState_1074_; lean_object* v_prevLinterStates_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1158_; 
v_env_1067_ = lean_ctor_get(v_cmdState_1061_, 0);
v_scopes_1068_ = lean_ctor_get(v_cmdState_1061_, 2);
v_usedQuotCtxts_1069_ = lean_ctor_get(v_cmdState_1061_, 3);
v_nextMacroScope_1070_ = lean_ctor_get(v_cmdState_1061_, 4);
v_maxRecDepth_1071_ = lean_ctor_get(v_cmdState_1061_, 5);
v_ngen_1072_ = lean_ctor_get(v_cmdState_1061_, 6);
v_auxDeclNGen_1073_ = lean_ctor_get(v_cmdState_1061_, 7);
v_infoState_1074_ = lean_ctor_get(v_cmdState_1061_, 8);
v_prevLinterStates_1075_ = lean_ctor_get(v_cmdState_1061_, 11);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_cmdState_1061_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; 
v_unused_1159_ = lean_ctor_get(v_cmdState_1061_, 12);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_cmdState_1061_, 10);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_cmdState_1061_, 9);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_cmdState_1061_, 1);
lean_dec(v_unused_1162_);
v___x_1077_ = v_cmdState_1061_;
v_isShared_1078_ = v_isSharedCheck_1158_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_prevLinterStates_1075_);
lean_inc(v_infoState_1074_);
lean_inc(v_auxDeclNGen_1073_);
lean_inc(v_ngen_1072_);
lean_inc(v_maxRecDepth_1071_);
lean_inc(v_nextMacroScope_1070_);
lean_inc(v_usedQuotCtxts_1069_);
lean_inc(v_scopes_1068_);
lean_inc(v_env_1067_);
lean_dec(v_cmdState_1061_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1158_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___f_1079_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1079_, 0, v_stx_1059_);
lean_closure_set(v___f_1079_, 1, v_revCmds_1060_);
v___x_1080_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1081_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1082_ = l_List_head_x21___redArg(v___x_1080_, v_scopes_1068_);
v___x_1083_ = l_Lean_MessageLog_empty;
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1086_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 12, v___x_1086_);
lean_ctor_set(v___x_1077_, 10, v___x_1086_);
lean_ctor_set(v___x_1077_, 9, v___x_1085_);
lean_ctor_set(v___x_1077_, 1, v___x_1083_);
v___x_1088_ = v___x_1077_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_env_1067_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_scopes_1068_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_usedQuotCtxts_1069_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_nextMacroScope_1070_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_maxRecDepth_1071_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_ngen_1072_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v_auxDeclNGen_1073_);
lean_ctor_set(v_reuseFailAlloc_1157_, 8, v_infoState_1074_);
lean_ctor_set(v_reuseFailAlloc_1157_, 9, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1157_, 10, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1157_, 11, v_prevLinterStates_1075_);
lean_ctor_set(v_reuseFailAlloc_1157_, 12, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v_toProcessingContext_1090_; lean_object* v_fileName_1091_; lean_object* v_fileMap_1092_; lean_object* v_opts_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; uint8_t v___y_1101_; lean_object* v_env_1102_; lean_object* v_scopes_1103_; lean_object* v_usedQuotCtxts_1104_; lean_object* v_nextMacroScope_1105_; lean_object* v_maxRecDepth_1106_; lean_object* v_ngen_1107_; lean_object* v_auxDeclNGen_1108_; lean_object* v_infoState_1109_; lean_object* v_traceState_1110_; lean_object* v_snapshotTasks_1111_; lean_object* v_prevLinterStates_1112_; lean_object* v_codeQualityEntryTasks_1113_; lean_object* v_messages_1114_; lean_object* v___y_1123_; 
v___x_1089_ = lean_st_mk_ref(v___x_1088_);
v_toProcessingContext_1090_ = lean_ctor_get(v_a_1065_, 0);
v_fileName_1091_ = lean_ctor_get(v_toProcessingContext_1090_, 1);
v_fileMap_1092_ = lean_ctor_get(v_toProcessingContext_1090_, 2);
v_opts_1093_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_opts_1093_);
lean_dec(v___x_1082_);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Lean_firstFrontendMacroScope;
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_internal_cmdlineSnapshots;
v___x_1099_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1093_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1156_; 
lean_inc_ref(v_snap_1063_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_snap_1063_);
v___y_1123_ = v___x_1156_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v___x_1095_;
goto v___jp_1122_;
}
v___jp_1100_:
{
lean_object* v_new_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_new_1115_ = lean_ctor_get(v_snap_1063_, 1);
lean_inc(v_new_1115_);
lean_dec_ref(v_snap_1063_);
v___x_1116_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1116_, 0, v_env_1102_);
lean_ctor_set(v___x_1116_, 1, v_messages_1114_);
lean_ctor_set(v___x_1116_, 2, v_scopes_1103_);
lean_ctor_set(v___x_1116_, 3, v_usedQuotCtxts_1104_);
lean_ctor_set(v___x_1116_, 4, v_nextMacroScope_1105_);
lean_ctor_set(v___x_1116_, 5, v_maxRecDepth_1106_);
lean_ctor_set(v___x_1116_, 6, v_ngen_1107_);
lean_ctor_set(v___x_1116_, 7, v_auxDeclNGen_1108_);
lean_ctor_set(v___x_1116_, 8, v_infoState_1109_);
lean_ctor_set(v___x_1116_, 9, v_traceState_1110_);
lean_ctor_set(v___x_1116_, 10, v_snapshotTasks_1111_);
lean_ctor_set(v___x_1116_, 11, v_prevLinterStates_1112_);
lean_ctor_set(v___x_1116_, 12, v_codeQualityEntryTasks_1113_);
v___x_1117_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1118_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1119_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
lean_ctor_set(v___x_1119_, 2, v___x_1095_);
lean_ctor_set(v___x_1119_, 3, v___x_1085_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*4, v___y_1101_);
v___x_1120_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1081_, v___x_1119_);
v___x_1121_ = lean_io_promise_resolve(v___x_1120_, v_new_1115_);
lean_dec(v_new_1115_);
return v___x_1116_;
}
v___jp_1122_:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v_fst_1132_; lean_object* v___x_1133_; lean_object* v_env_1134_; lean_object* v_messages_1135_; lean_object* v_scopes_1136_; lean_object* v_usedQuotCtxts_1137_; lean_object* v_nextMacroScope_1138_; lean_object* v_maxRecDepth_1139_; lean_object* v_ngen_1140_; lean_object* v_auxDeclNGen_1141_; lean_object* v_infoState_1142_; lean_object* v_traceState_1143_; lean_object* v_snapshotTasks_1144_; lean_object* v_prevLinterStates_1145_; lean_object* v_codeQualityEntryTasks_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_cancelTk_1064_);
v___x_1125_ = 0;
v___x_1126_ = 0;
lean_inc(v_beginPos_1062_);
lean_inc_ref(v_fileMap_1092_);
lean_inc_ref(v_fileName_1091_);
v___x_1127_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1127_, 0, v_fileName_1091_);
lean_ctor_set(v___x_1127_, 1, v_fileMap_1092_);
lean_ctor_set(v___x_1127_, 2, v___x_1084_);
lean_ctor_set(v___x_1127_, 3, v_beginPos_1062_);
lean_ctor_set(v___x_1127_, 4, v___x_1094_);
lean_ctor_set(v___x_1127_, 5, v___x_1095_);
lean_ctor_set(v___x_1127_, 6, v___x_1096_);
lean_ctor_set(v___x_1127_, 7, v___x_1097_);
lean_ctor_set(v___x_1127_, 8, v___y_1123_);
lean_ctor_set(v___x_1127_, 9, v___x_1124_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*10, v___x_1125_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*10 + 1, v___x_1126_);
lean_inc(v___x_1089_);
v___f_1128_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1128_, 0, v___f_1079_);
lean_closure_set(v___f_1128_, 1, v___x_1127_);
lean_closure_set(v___f_1128_, 2, v___x_1089_);
v___x_1129_ = l_Lean_Core_stderrAsMessages;
v___x_1130_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1093_, v___x_1129_);
lean_dec_ref(v_opts_1093_);
v___x_1131_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1128_, v___x_1130_, v_a_1065_);
v_fst_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_fst_1132_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = lean_st_ref_get(v___x_1089_);
lean_dec(v___x_1089_);
v_env_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_ref(v_env_1134_);
v_messages_1135_ = lean_ctor_get(v___x_1133_, 1);
lean_inc_ref(v_messages_1135_);
v_scopes_1136_ = lean_ctor_get(v___x_1133_, 2);
lean_inc(v_scopes_1136_);
v_usedQuotCtxts_1137_ = lean_ctor_get(v___x_1133_, 3);
lean_inc(v_usedQuotCtxts_1137_);
v_nextMacroScope_1138_ = lean_ctor_get(v___x_1133_, 4);
lean_inc(v_nextMacroScope_1138_);
v_maxRecDepth_1139_ = lean_ctor_get(v___x_1133_, 5);
lean_inc(v_maxRecDepth_1139_);
v_ngen_1140_ = lean_ctor_get(v___x_1133_, 6);
lean_inc_ref(v_ngen_1140_);
v_auxDeclNGen_1141_ = lean_ctor_get(v___x_1133_, 7);
lean_inc_ref(v_auxDeclNGen_1141_);
v_infoState_1142_ = lean_ctor_get(v___x_1133_, 8);
lean_inc_ref(v_infoState_1142_);
v_traceState_1143_ = lean_ctor_get(v___x_1133_, 9);
lean_inc_ref(v_traceState_1143_);
v_snapshotTasks_1144_ = lean_ctor_get(v___x_1133_, 10);
lean_inc_ref(v_snapshotTasks_1144_);
v_prevLinterStates_1145_ = lean_ctor_get(v___x_1133_, 11);
lean_inc(v_prevLinterStates_1145_);
v_codeQualityEntryTasks_1146_ = lean_ctor_get(v___x_1133_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1146_);
lean_dec(v___x_1133_);
v___x_1147_ = lean_string_utf8_byte_size(v_fst_1132_);
v___x_1148_ = lean_nat_dec_eq(v___x_1147_, v___x_1084_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_inc_ref(v_fileMap_1092_);
v___x_1149_ = l_Lean_FileMap_toPosition(v_fileMap_1092_, v_beginPos_1062_);
lean_dec(v_beginPos_1062_);
v___x_1150_ = 0;
v___x_1151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_fst_1132_);
v___x_1153_ = l_Lean_MessageData_ofFormat(v___x_1152_);
lean_inc_ref(v_fileName_1091_);
v___x_1154_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1154_, 0, v_fileName_1091_);
lean_ctor_set(v___x_1154_, 1, v___x_1149_);
lean_ctor_set(v___x_1154_, 2, v___x_1095_);
lean_ctor_set(v___x_1154_, 3, v___x_1151_);
lean_ctor_set(v___x_1154_, 4, v___x_1153_);
lean_ctor_set_uint8(v___x_1154_, sizeof(void*)*5, v___x_1125_);
lean_ctor_set_uint8(v___x_1154_, sizeof(void*)*5 + 1, v___x_1150_);
lean_ctor_set_uint8(v___x_1154_, sizeof(void*)*5 + 2, v___x_1125_);
v___x_1155_ = l_Lean_MessageLog_add(v___x_1154_, v_messages_1135_);
v___y_1101_ = v___x_1125_;
v_env_1102_ = v_env_1134_;
v_scopes_1103_ = v_scopes_1136_;
v_usedQuotCtxts_1104_ = v_usedQuotCtxts_1137_;
v_nextMacroScope_1105_ = v_nextMacroScope_1138_;
v_maxRecDepth_1106_ = v_maxRecDepth_1139_;
v_ngen_1107_ = v_ngen_1140_;
v_auxDeclNGen_1108_ = v_auxDeclNGen_1141_;
v_infoState_1109_ = v_infoState_1142_;
v_traceState_1110_ = v_traceState_1143_;
v_snapshotTasks_1111_ = v_snapshotTasks_1144_;
v_prevLinterStates_1112_ = v_prevLinterStates_1145_;
v_codeQualityEntryTasks_1113_ = v_codeQualityEntryTasks_1146_;
v_messages_1114_ = v___x_1155_;
goto v___jp_1100_;
}
else
{
lean_dec(v_fst_1132_);
lean_dec(v_beginPos_1062_);
v___y_1101_ = v___x_1125_;
v_env_1102_ = v_env_1134_;
v_scopes_1103_ = v_scopes_1136_;
v_usedQuotCtxts_1104_ = v_usedQuotCtxts_1137_;
v_nextMacroScope_1105_ = v_nextMacroScope_1138_;
v_maxRecDepth_1106_ = v_maxRecDepth_1139_;
v_ngen_1107_ = v_ngen_1140_;
v_auxDeclNGen_1108_ = v_auxDeclNGen_1141_;
v_infoState_1109_ = v_infoState_1142_;
v_traceState_1110_ = v_traceState_1143_;
v_snapshotTasks_1111_ = v_snapshotTasks_1144_;
v_prevLinterStates_1112_ = v_prevLinterStates_1145_;
v_codeQualityEntryTasks_1113_ = v_codeQualityEntryTasks_1146_;
v_messages_1114_ = v_messages_1135_;
goto v___jp_1100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1163_, lean_object* v_revCmds_1164_, lean_object* v_cmdState_1165_, lean_object* v_beginPos_1166_, lean_object* v_snap_1167_, lean_object* v_cancelTk_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1163_, v_revCmds_1164_, v_cmdState_1165_, v_beginPos_1166_, v_snap_1167_, v_cancelTk_1168_, v_a_1169_);
lean_dec_ref(v_a_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1172_, lean_object* v_h_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1173_, v_x_1174_, v___y_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_h_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1178_, v_h_1179_, v_x_1180_, v___y_1181_);
lean_dec_ref(v___y_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1184_, lean_object* v_x_1185_, uint8_t v_isolateStderr_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1185_, v_isolateStderr_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_x_1191_, lean_object* v_isolateStderr_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_isolateStderr_boxed_1195_; lean_object* v_res_1196_; 
v_isolateStderr_boxed_1195_ = lean_unbox(v_isolateStderr_1192_);
v_res_1196_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1190_, v_x_1191_, v_isolateStderr_boxed_1195_, v___y_1193_);
lean_dec_ref(v___y_1193_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1197_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1207_){
_start:
{
lean_object* v_toSnapshotTreeM_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_toSnapshotTreeM_1208_ = lean_ctor_get(v_a_1207_, 1);
lean_inc_ref(v_toSnapshotTreeM_1208_);
lean_dec_ref(v_a_1207_);
v___x_1209_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1210_ = lean_apply_1(v_toSnapshotTreeM_1208_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1211_){
_start:
{
lean_object* v_toSnapshot_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_toSnapshot_1212_ = lean_ctor_get(v_a_1211_, 0);
lean_inc_ref(v_toSnapshot_1212_);
lean_dec_ref(v_a_1211_);
v___x_1213_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1214_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1212_, v___x_1213_);
v___x_1215_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1219_ = l_Lean_Language_Snapshot_transform(v_a_1217_, v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1222_, lean_object* v_opt_1223_){
_start:
{
lean_object* v_name_1224_; lean_object* v_defValue_1225_; lean_object* v_map_1226_; lean_object* v___x_1227_; 
v_name_1224_ = lean_ctor_get(v_opt_1223_, 0);
v_defValue_1225_ = lean_ctor_get(v_opt_1223_, 1);
v_map_1226_ = lean_ctor_get(v_opts_1222_, 0);
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1226_, v_name_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_inc(v_defValue_1225_);
return v_defValue_1225_;
}
else
{
lean_object* v_val_1228_; 
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1227_, 1);
if (lean_obj_tag(v_val_1228_) == 3)
{
lean_object* v_v_1229_; 
v_v_1229_ = lean_ctor_get(v_val_1228_, 0);
lean_inc(v_v_1229_);
lean_dec_ref_known(v_val_1228_, 1);
return v_v_1229_;
}
else
{
lean_dec(v_val_1228_);
lean_inc(v_defValue_1225_);
return v_defValue_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1230_, lean_object* v_opt_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1230_, v_opt_1231_);
lean_dec_ref(v_opt_1231_);
lean_dec_ref(v_opts_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1235_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1233_, v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1242_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1243_ = l_Lean_Name_append(v___x_1242_, v___x_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1244_, lean_object* v___x_1245_, uint8_t v_val_1246_, lean_object* v_val_1247_, lean_object* v_val_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, uint8_t v___x_1251_, lean_object* v_a_1252_, lean_object* v_pos_1253_, lean_object* v___x_1254_, lean_object* v_infoSt_1255_){
_start:
{
lean_object* v___y_1258_; lean_object* v_msgLog_1259_; lean_object* v___y_1265_; lean_object* v_trees_1297_; lean_object* v_size_1298_; uint8_t v___x_1299_; 
v_trees_1297_ = lean_ctor_get(v_infoSt_1255_, 2);
v_size_1298_ = lean_ctor_get(v_trees_1297_, 2);
v___x_1299_ = lean_nat_dec_lt(v___x_1250_, v_size_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = l_outOfBounds___redArg(v___x_1254_);
v___y_1265_ = v___x_1300_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1254_, v_trees_1297_, v___x_1250_);
v___y_1265_ = v___x_1301_;
goto v___jp_1264_;
}
v___jp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1259_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1258_);
v___x_1262_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1262_, 0, v___x_1244_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1245_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*4, v_val_1246_);
v___x_1263_ = lean_io_promise_resolve(v___x_1262_, v_val_1247_);
return v___x_1263_;
}
v___jp_1264_:
{
lean_object* v_scopes_1266_; lean_object* v___x_1267_; lean_object* v_opts_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v_hasTrace_1272_; 
v_scopes_1266_ = lean_ctor_get(v_val_1248_, 2);
v___x_1267_ = l_List_head_x21___redArg(v___x_1249_, v_scopes_1266_);
v_opts_1268_ = lean_ctor_get(v___x_1267_, 1);
lean_inc_ref(v_opts_1268_);
lean_dec(v___x_1267_);
v___x_1269_ = l_Lean_MessageLog_empty;
v___x_1270_ = l_Lean_inheritedTraceOptions;
v___x_1271_ = lean_st_ref_get(v___x_1270_);
v_hasTrace_1272_ = lean_ctor_get_uint8(v_opts_1268_, sizeof(void*)*1);
if (v_hasTrace_1272_ == 0)
{
lean_dec(v___x_1271_);
lean_dec_ref(v_opts_1268_);
lean_dec(v___x_1250_);
v___y_1258_ = v___y_1265_;
v_msgLog_1259_ = v___x_1269_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1274_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1275_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1271_, v_opts_1268_, v___x_1275_);
lean_dec_ref(v_opts_1268_);
lean_dec(v___x_1271_);
if (v___x_1276_ == 0)
{
lean_dec(v___x_1250_);
v___y_1258_ = v___y_1265_;
v_msgLog_1259_ = v___x_1269_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_box(0);
lean_inc_ref(v___y_1265_);
v___x_1278_ = l_Lean_Elab_InfoTree_format(v___y_1265_, v___x_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; double v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_toProcessingContext_1283_; lean_object* v_fileName_1284_; lean_object* v_fileMap_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_float_of_nat(v___x_1250_);
v___x_1281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1282_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1282_, 0, v___x_1273_);
lean_ctor_set(v___x_1282_, 1, v___x_1277_);
lean_ctor_set(v___x_1282_, 2, v___x_1281_);
lean_ctor_set_float(v___x_1282_, sizeof(void*)*3, v___x_1280_);
lean_ctor_set_float(v___x_1282_, sizeof(void*)*3 + 8, v___x_1280_);
lean_ctor_set_uint8(v___x_1282_, sizeof(void*)*3 + 16, v___x_1251_);
v_toProcessingContext_1283_ = lean_ctor_get(v_a_1252_, 0);
v_fileName_1284_ = lean_ctor_get(v_toProcessingContext_1283_, 1);
v_fileMap_1285_ = lean_ctor_get(v_toProcessingContext_1283_, 2);
v___x_1286_ = l_Lean_MessageData_nil;
v___x_1287_ = l_Lean_MessageData_ofFormat(v_a_1279_);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_mk_empty_array_with_capacity(v___x_1288_);
v___x_1290_ = lean_array_push(v___x_1289_, v___x_1287_);
v___x_1291_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1282_);
lean_ctor_set(v___x_1291_, 1, v___x_1286_);
lean_ctor_set(v___x_1291_, 2, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1274_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_inc_ref(v_fileMap_1285_);
v___x_1293_ = l_Lean_FileMap_toPosition(v_fileMap_1285_, v_pos_1253_);
v___x_1294_ = 0;
lean_inc_ref(v_fileName_1284_);
v___x_1295_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1295_, 0, v_fileName_1284_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
lean_ctor_set(v___x_1295_, 2, v___x_1277_);
lean_ctor_set(v___x_1295_, 3, v___x_1281_);
lean_ctor_set(v___x_1295_, 4, v___x_1292_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*5, v_val_1246_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*5 + 1, v___x_1294_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*5 + 2, v_val_1246_);
v___x_1296_ = l_Lean_MessageLog_add(v___x_1295_, v___x_1269_);
v___y_1258_ = v___y_1265_;
v_msgLog_1259_ = v___x_1296_;
goto v___jp_1257_;
}
else
{
lean_dec_ref_known(v___x_1278_, 1);
lean_dec(v___x_1250_);
v___y_1258_ = v___y_1265_;
v_msgLog_1259_ = v___x_1269_;
goto v___jp_1257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v_val_1304_, lean_object* v_val_1305_, lean_object* v_val_1306_, lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v_a_1310_, lean_object* v_pos_1311_, lean_object* v___x_1312_, lean_object* v_infoSt_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_val_36808__boxed_1315_; uint8_t v___x_36813__boxed_1316_; lean_object* v_res_1317_; 
v_val_36808__boxed_1315_ = lean_unbox(v_val_1304_);
v___x_36813__boxed_1316_ = lean_unbox(v___x_1309_);
v_res_1317_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1302_, v___x_1303_, v_val_36808__boxed_1315_, v_val_1305_, v_val_1306_, v___x_1307_, v___x_1308_, v___x_36813__boxed_1316_, v_a_1310_, v_pos_1311_, v___x_1312_, v_infoSt_1313_);
lean_dec_ref(v_infoSt_1313_);
lean_dec_ref(v___x_1312_);
lean_dec(v_pos_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v_val_1306_);
lean_dec(v_val_1305_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v___x_1320_, uint8_t v_val_1321_, lean_object* v_as_1322_, size_t v_sz_1323_, size_t v_i_1324_, lean_object* v_b_1325_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_lt(v_i_1324_, v_sz_1323_);
if (v___x_1327_ == 0)
{
lean_dec_ref(v___x_1320_);
lean_dec_ref(v___x_1318_);
return v_b_1325_;
}
else
{
lean_object* v_snd_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1346_; 
v_snd_1328_ = lean_ctor_get(v_b_1325_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_b_1325_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_b_1325_, 0);
lean_dec(v_unused_1347_);
v___x_1330_ = v_b_1325_;
v_isShared_1331_ = v_isSharedCheck_1346_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_snd_1328_);
lean_dec(v_b_1325_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1346_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v_a_1332_; lean_object* v_msg_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v_a_1332_ = lean_array_uget_borrowed(v_as_1322_, v_i_1324_);
v_msg_1333_ = lean_ctor_get(v_a_1332_, 1);
v___x_1334_ = lean_box(0);
lean_inc_ref(v___x_1318_);
v___x_1335_ = l_Lean_FileMap_toPosition(v___x_1318_, v___x_1319_);
v___x_1336_ = 0;
v___x_1337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1333_);
lean_inc_ref(v___x_1320_);
v___x_1338_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1338_, 0, v___x_1320_);
lean_ctor_set(v___x_1338_, 1, v___x_1335_);
lean_ctor_set(v___x_1338_, 2, v___x_1334_);
lean_ctor_set(v___x_1338_, 3, v___x_1337_);
lean_ctor_set(v___x_1338_, 4, v_msg_1333_);
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*5, v_val_1321_);
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*5 + 1, v___x_1336_);
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*5 + 2, v_val_1321_);
v___x_1339_ = l_Lean_MessageLog_add(v___x_1338_, v_snd_1328_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v___x_1339_);
lean_ctor_set(v___x_1330_, 0, v___x_1334_);
v___x_1341_ = v___x_1330_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
size_t v___x_1342_; size_t v___x_1343_; 
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1324_, v___x_1342_);
v_i_1324_ = v___x_1343_;
v_b_1325_ = v___x_1341_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1348_, lean_object* v___x_1349_, lean_object* v___x_1350_, lean_object* v_val_1351_, lean_object* v_as_1352_, lean_object* v_sz_1353_, lean_object* v_i_1354_, lean_object* v_b_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v_val_36921__boxed_1357_; size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v_val_36921__boxed_1357_ = lean_unbox(v_val_1351_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1353_);
lean_dec(v_sz_1353_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1348_, v___x_1349_, v___x_1350_, v_val_36921__boxed_1357_, v_as_1352_, v_sz_boxed_1358_, v_i_boxed_1359_, v_b_1355_);
lean_dec_ref(v_as_1352_);
lean_dec(v___x_1349_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, uint8_t v_val_1364_, lean_object* v_as_1365_, size_t v_sz_1366_, size_t v_i_1367_, lean_object* v_b_1368_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_usize_dec_lt(v_i_1367_, v_sz_1366_);
if (v___x_1370_ == 0)
{
lean_dec_ref(v___x_1363_);
lean_dec_ref(v___x_1361_);
return v_b_1368_;
}
else
{
lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1389_; 
v_snd_1371_ = lean_ctor_get(v_b_1368_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_b_1368_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v_b_1368_, 0);
lean_dec(v_unused_1390_);
v___x_1373_ = v_b_1368_;
v_isShared_1374_ = v_isSharedCheck_1389_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_dec(v_b_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1389_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_a_1375_; lean_object* v_msg_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v_a_1375_ = lean_array_uget_borrowed(v_as_1365_, v_i_1367_);
v_msg_1376_ = lean_ctor_get(v_a_1375_, 1);
v___x_1377_ = lean_box(0);
lean_inc_ref(v___x_1361_);
v___x_1378_ = l_Lean_FileMap_toPosition(v___x_1361_, v___x_1362_);
v___x_1379_ = 0;
v___x_1380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1376_);
lean_inc_ref(v___x_1363_);
v___x_1381_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1381_, 0, v___x_1363_);
lean_ctor_set(v___x_1381_, 1, v___x_1378_);
lean_ctor_set(v___x_1381_, 2, v___x_1377_);
lean_ctor_set(v___x_1381_, 3, v___x_1380_);
lean_ctor_set(v___x_1381_, 4, v_msg_1376_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*5, v_val_1364_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*5 + 1, v___x_1379_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*5 + 2, v_val_1364_);
v___x_1382_ = l_Lean_MessageLog_add(v___x_1381_, v_snd_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1382_);
lean_ctor_set(v___x_1373_, 0, v___x_1377_);
v___x_1384_ = v___x_1373_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_add(v_i_1367_, v___x_1385_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1361_, v___x_1362_, v___x_1363_, v_val_1364_, v_as_1365_, v_sz_1366_, v___x_1386_, v___x_1384_);
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v_val_1394_, lean_object* v_as_1395_, lean_object* v_sz_1396_, lean_object* v_i_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v_val_36973__boxed_1400_; size_t v_sz_boxed_1401_; size_t v_i_boxed_1402_; lean_object* v_res_1403_; 
v_val_36973__boxed_1400_ = lean_unbox(v_val_1394_);
v_sz_boxed_1401_ = lean_unbox_usize(v_sz_1396_);
lean_dec(v_sz_1396_);
v_i_boxed_1402_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1391_, v___x_1392_, v___x_1393_, v_val_36973__boxed_1400_, v_as_1395_, v_sz_boxed_1401_, v_i_boxed_1402_, v_b_1398_);
lean_dec_ref(v_as_1395_);
lean_dec(v___x_1392_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1404_, lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, uint8_t v_val_1408_, lean_object* v_n_1409_, lean_object* v_b_1410_){
_start:
{
if (lean_obj_tag(v_n_1409_) == 0)
{
lean_object* v_cs_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v_sz_1415_; size_t v___x_1416_; lean_object* v___x_1417_; lean_object* v_fst_1418_; 
v_cs_1412_ = lean_ctor_get(v_n_1409_, 0);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_b_1410_);
v_sz_1415_ = lean_array_size(v_cs_1412_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1404_, v___x_1405_, v___x_1406_, v___x_1407_, v_val_1408_, v_cs_1412_, v_sz_1415_, v___x_1416_, v___x_1414_);
v_fst_1418_ = lean_ctor_get(v___x_1417_, 0);
if (lean_obj_tag(v_fst_1418_) == 0)
{
lean_object* v_snd_1419_; lean_object* v___x_1420_; 
v_snd_1419_ = lean_ctor_get(v___x_1417_, 1);
lean_inc(v_snd_1419_);
lean_dec_ref(v___x_1417_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_snd_1419_);
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; 
lean_inc_ref(v_fst_1418_);
lean_dec_ref(v___x_1417_);
v_val_1421_ = lean_ctor_get(v_fst_1418_, 0);
lean_inc(v_val_1421_);
lean_dec_ref_known(v_fst_1418_, 1);
return v_val_1421_;
}
}
else
{
lean_object* v_vs_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v_fst_1428_; 
v_vs_1422_ = lean_ctor_get(v_n_1409_, 0);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_b_1410_);
v_sz_1425_ = lean_array_size(v_vs_1422_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1405_, v___x_1406_, v___x_1407_, v_val_1408_, v_vs_1422_, v_sz_1425_, v___x_1426_, v___x_1424_);
v_fst_1428_ = lean_ctor_get(v___x_1427_, 0);
if (lean_obj_tag(v_fst_1428_) == 0)
{
lean_object* v_snd_1429_; lean_object* v___x_1430_; 
v_snd_1429_ = lean_ctor_get(v___x_1427_, 1);
lean_inc(v_snd_1429_);
lean_dec_ref(v___x_1427_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_snd_1429_);
return v___x_1430_;
}
else
{
lean_object* v_val_1431_; 
lean_inc_ref(v_fst_1428_);
lean_dec_ref(v___x_1427_);
v_val_1431_ = lean_ctor_get(v_fst_1428_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v_fst_1428_, 1);
return v_val_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1432_, lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v___x_1435_, uint8_t v_val_1436_, lean_object* v_as_1437_, size_t v_sz_1438_, size_t v_i_1439_, lean_object* v_b_1440_){
_start:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_lt(v_i_1439_, v_sz_1438_);
if (v___x_1442_ == 0)
{
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1433_);
return v_b_1440_;
}
else
{
lean_object* v_snd_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1461_; 
v_snd_1443_ = lean_ctor_get(v_b_1440_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_b_1440_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_b_1440_, 0);
lean_dec(v_unused_1462_);
v___x_1445_ = v_b_1440_;
v_isShared_1446_ = v_isSharedCheck_1461_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_snd_1443_);
lean_dec(v_b_1440_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1461_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_box(0);
v_a_1448_ = lean_array_uget_borrowed(v_as_1437_, v_i_1439_);
lean_inc(v_snd_1443_);
lean_inc_ref(v___x_1435_);
lean_inc_ref(v___x_1433_);
v___x_1449_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1432_, v___x_1433_, v___x_1434_, v___x_1435_, v_val_1436_, v_a_1448_, v_snd_1443_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1433_);
v___x_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1450_);
v___x_1452_ = v___x_1445_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_snd_1443_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; 
lean_dec(v_snd_1443_);
v_a_1454_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1449_, 1);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v_a_1454_);
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1456_ = v___x_1445_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_a_1454_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
size_t v___x_1457_; size_t v___x_1458_; 
v___x_1457_ = ((size_t)1ULL);
v___x_1458_ = lean_usize_add(v_i_1439_, v___x_1457_);
v_i_1439_ = v___x_1458_;
v_b_1440_ = v___x_1456_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1463_, lean_object* v___x_1464_, lean_object* v___x_1465_, lean_object* v___x_1466_, lean_object* v_val_1467_, lean_object* v_as_1468_, lean_object* v_sz_1469_, lean_object* v_i_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v_val_37024__boxed_1473_; size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_val_37024__boxed_1473_ = lean_unbox(v_val_1467_);
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1469_);
lean_dec(v_sz_1469_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1463_, v___x_1464_, v___x_1465_, v___x_1466_, v_val_37024__boxed_1473_, v_as_1468_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1471_);
lean_dec_ref(v_as_1468_);
lean_dec(v___x_1465_);
lean_dec_ref(v_init_1463_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v_val_1481_, lean_object* v_n_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v_val_37040__boxed_1485_; lean_object* v_res_1486_; 
v_val_37040__boxed_1485_ = lean_unbox(v_val_1481_);
v_res_1486_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1477_, v___x_1478_, v___x_1479_, v___x_1480_, v_val_37040__boxed_1485_, v_n_1482_, v_b_1483_);
lean_dec_ref(v_n_1482_);
lean_dec(v___x_1479_);
lean_dec_ref(v_init_1477_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1487_, lean_object* v___x_1488_, lean_object* v___x_1489_, uint8_t v_val_1490_, lean_object* v_as_1491_, size_t v_sz_1492_, size_t v_i_1493_, lean_object* v_b_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1493_, v_sz_1492_);
if (v___x_1496_ == 0)
{
lean_dec_ref(v___x_1489_);
lean_dec_ref(v___x_1487_);
return v_b_1494_;
}
else
{
lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1515_; 
v_snd_1497_ = lean_ctor_get(v_b_1494_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_b_1494_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_b_1494_, 0);
lean_dec(v_unused_1516_);
v___x_1499_ = v_b_1494_;
v_isShared_1500_ = v_isSharedCheck_1515_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_dec(v_b_1494_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1515_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_a_1501_; lean_object* v_msg_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v_a_1501_ = lean_array_uget_borrowed(v_as_1491_, v_i_1493_);
v_msg_1502_ = lean_ctor_get(v_a_1501_, 1);
v___x_1503_ = lean_box(0);
lean_inc_ref(v___x_1487_);
v___x_1504_ = l_Lean_FileMap_toPosition(v___x_1487_, v___x_1488_);
v___x_1505_ = 0;
v___x_1506_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1502_);
lean_inc_ref(v___x_1489_);
v___x_1507_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1507_, 0, v___x_1489_);
lean_ctor_set(v___x_1507_, 1, v___x_1504_);
lean_ctor_set(v___x_1507_, 2, v___x_1503_);
lean_ctor_set(v___x_1507_, 3, v___x_1506_);
lean_ctor_set(v___x_1507_, 4, v_msg_1502_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*5, v_val_1490_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*5 + 1, v___x_1505_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*5 + 2, v_val_1490_);
v___x_1508_ = l_Lean_MessageLog_add(v___x_1507_, v_snd_1497_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v___x_1508_);
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1510_ = v___x_1499_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1493_, v___x_1511_);
v_i_1493_ = v___x_1512_;
v_b_1494_ = v___x_1510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v_val_1520_, lean_object* v_as_1521_, lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_val_37122__boxed_1526_; size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_val_37122__boxed_1526_ = lean_unbox(v_val_1520_);
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1517_, v___x_1518_, v___x_1519_, v_val_37122__boxed_1526_, v_as_1521_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1524_);
lean_dec_ref(v_as_1521_);
lean_dec(v___x_1518_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1530_, lean_object* v___x_1531_, lean_object* v___x_1532_, uint8_t v_val_1533_, lean_object* v_as_1534_, size_t v_sz_1535_, size_t v_i_1536_, lean_object* v_b_1537_){
_start:
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_usize_dec_lt(v_i_1536_, v_sz_1535_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v___x_1532_);
lean_dec_ref(v___x_1530_);
return v_b_1537_;
}
else
{
lean_object* v_snd_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1558_; 
v_snd_1540_ = lean_ctor_get(v_b_1537_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_b_1537_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_b_1537_, 0);
lean_dec(v_unused_1559_);
v___x_1542_ = v_b_1537_;
v_isShared_1543_ = v_isSharedCheck_1558_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_snd_1540_);
lean_dec(v_b_1537_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1558_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_a_1544_; lean_object* v_msg_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v_a_1544_ = lean_array_uget_borrowed(v_as_1534_, v_i_1536_);
v_msg_1545_ = lean_ctor_get(v_a_1544_, 1);
v___x_1546_ = lean_box(0);
lean_inc_ref(v___x_1530_);
v___x_1547_ = l_Lean_FileMap_toPosition(v___x_1530_, v___x_1531_);
v___x_1548_ = 0;
v___x_1549_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1545_);
lean_inc_ref(v___x_1532_);
v___x_1550_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1550_, 0, v___x_1532_);
lean_ctor_set(v___x_1550_, 1, v___x_1547_);
lean_ctor_set(v___x_1550_, 2, v___x_1546_);
lean_ctor_set(v___x_1550_, 3, v___x_1549_);
lean_ctor_set(v___x_1550_, 4, v_msg_1545_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*5, v_val_1533_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*5 + 1, v___x_1548_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*5 + 2, v_val_1533_);
v___x_1551_ = l_Lean_MessageLog_add(v___x_1550_, v_snd_1540_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___x_1551_);
lean_ctor_set(v___x_1542_, 0, v___x_1546_);
v___x_1553_ = v___x_1542_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_i_1536_, v___x_1554_);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1530_, v___x_1531_, v___x_1532_, v_val_1533_, v_as_1534_, v_sz_1535_, v___x_1555_, v___x_1553_);
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1560_, lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_val_1563_, lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_val_37174__boxed_1569_; size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_val_37174__boxed_1569_ = lean_unbox(v_val_1563_);
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1560_, v___x_1561_, v___x_1562_, v_val_37174__boxed_1569_, v_as_1564_, v_sz_boxed_1570_, v_i_boxed_1571_, v_b_1567_);
lean_dec_ref(v_as_1564_);
lean_dec(v___x_1561_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1573_, lean_object* v___x_1574_, lean_object* v___x_1575_, uint8_t v_val_1576_, lean_object* v_t_1577_, lean_object* v_init_1578_){
_start:
{
lean_object* v_root_1580_; lean_object* v_tail_1581_; lean_object* v___x_1582_; 
v_root_1580_ = lean_ctor_get(v_t_1577_, 0);
v_tail_1581_ = lean_ctor_get(v_t_1577_, 1);
lean_inc_ref(v___x_1575_);
lean_inc_ref(v___x_1573_);
lean_inc_ref(v_init_1578_);
v___x_1582_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1578_, v___x_1573_, v___x_1574_, v___x_1575_, v_val_1576_, v_root_1580_, v_init_1578_);
lean_dec_ref(v_init_1578_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; 
lean_dec_ref(v___x_1575_);
lean_dec_ref(v___x_1573_);
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
return v_a_1583_;
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; lean_object* v_fst_1590_; 
v_a_1584_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v_a_1584_);
v_sz_1587_ = lean_array_size(v_tail_1581_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1573_, v___x_1574_, v___x_1575_, v_val_1576_, v_tail_1581_, v_sz_1587_, v___x_1588_, v___x_1586_);
v_fst_1590_ = lean_ctor_get(v___x_1589_, 0);
if (lean_obj_tag(v_fst_1590_) == 0)
{
lean_object* v_snd_1591_; 
v_snd_1591_ = lean_ctor_get(v___x_1589_, 1);
lean_inc(v_snd_1591_);
lean_dec_ref(v___x_1589_);
return v_snd_1591_;
}
else
{
lean_object* v_val_1592_; 
lean_inc_ref(v_fst_1590_);
lean_dec_ref(v___x_1589_);
v_val_1592_ = lean_ctor_get(v_fst_1590_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_fst_1590_, 1);
return v_val_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v_val_1596_, lean_object* v_t_1597_, lean_object* v_init_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v_val_37225__boxed_1600_; lean_object* v_res_1601_; 
v_val_37225__boxed_1600_ = lean_unbox(v_val_1596_);
v_res_1601_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1593_, v___x_1594_, v___x_1595_, v_val_37225__boxed_1600_, v_t_1597_, v_init_1598_);
lean_dec_ref(v_t_1597_);
lean_dec(v___x_1594_);
return v_res_1601_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = l_Lean_firstFrontendMacroScope;
v___x_1604_ = lean_nat_add(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1615_, lean_object* v_opts_1616_, lean_object* v___x_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, size_t v___x_1620_, uint8_t v___x_1621_, lean_object* v_env_1622_, lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v_pos_1625_, uint8_t v_val_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, uint8_t v___x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_toProcessingContext_1635_; lean_object* v_fileName_1636_; lean_object* v_fileMap_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint16_t v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_fileName_1662_; lean_object* v_fileMap_1663_; lean_object* v_currNamespace_1664_; lean_object* v_openDecls_1665_; lean_object* v_initHeartbeats_1666_; lean_object* v_maxHeartbeats_1667_; lean_object* v_quotContext_1668_; lean_object* v_currMacroScope_1669_; lean_object* v_cancelTk_x3f_1670_; lean_object* v_inheritedTraceOptions_1671_; lean_object* v_currRecDepth_1672_; lean_object* v_ref_1673_; uint8_t v_suppressElabErrors_1674_; uint8_t v_checkDeprecated_1675_; uint8_t v_isRecordingDeps_1676_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___y_1696_; lean_object* v_env_1717_; uint8_t v___x_1718_; uint16_t v___x_1719_; uint16_t v___x_1720_; uint16_t v___x_1721_; uint8_t v___x_1722_; 
v_toProcessingContext_1635_ = lean_ctor_get(v_a_1615_, 0);
v_fileName_1636_ = lean_ctor_get(v_toProcessingContext_1635_, 1);
v_fileMap_1637_ = lean_ctor_get(v_toProcessingContext_1635_, 2);
v___x_1638_ = lean_box(0);
v___x_1639_ = l_Lean_Core_getMaxHeartbeats(v_opts_1616_);
v___x_1640_ = l_Lean_firstFrontendMacroScope;
v___x_1641_ = lean_box(0);
v___x_1642_ = l_Lean_OptionFlags_ofOptions(v_opts_1616_);
v___x_1643_ = 0;
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1646_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1617_);
v___x_1647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1617_);
lean_ctor_set(v___x_1647_, 1, v___x_1644_);
lean_ctor_set(v___x_1647_, 2, v___x_1638_);
v___x_1648_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1649_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1650_ = lean_mk_empty_array_with_capacity(v___x_1618_);
v___x_1651_ = l_Lean_Options_empty;
lean_inc_n(v___x_1618_, 5);
lean_inc_ref_n(v___x_1650_, 5);
v___x_1652_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_ctor_set(v___x_1652_, 2, v___x_1650_);
lean_ctor_set(v___x_1652_, 3, v___x_1618_);
lean_ctor_set(v___x_1652_, 4, v___x_1618_);
lean_ctor_set(v___x_1652_, 5, v___x_1618_);
lean_ctor_set(v___x_1652_, 6, v___x_1650_);
lean_ctor_set(v___x_1652_, 7, v___x_1650_);
v___x_1653_ = lean_mk_empty_array_with_capacity(v___x_1619_);
lean_inc_ref(v___x_1653_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
lean_ctor_set(v___x_1655_, 2, v___x_1618_);
lean_ctor_set(v___x_1655_, 3, v___x_1618_);
lean_ctor_set_usize(v___x_1655_, 4, v___x_1620_);
v___x_1656_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1655_, 2);
v___x_1657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1655_);
lean_ctor_set(v___x_1657_, 2, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1658_, 0, v___x_1648_);
lean_ctor_set(v___x_1658_, 1, v___x_1648_);
lean_ctor_set(v___x_1658_, 2, v___x_1655_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3, v___x_1621_);
lean_inc_ref(v___x_1623_);
v___x_1659_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1659_, 0, v_env_1622_);
lean_ctor_set(v___x_1659_, 1, v___x_1645_);
lean_ctor_set(v___x_1659_, 2, v___x_1646_);
lean_ctor_set(v___x_1659_, 3, v___x_1647_);
lean_ctor_set(v___x_1659_, 4, v___x_1623_);
lean_ctor_set(v___x_1659_, 5, v___x_1649_);
lean_ctor_set(v___x_1659_, 6, v___x_1652_);
lean_ctor_set(v___x_1659_, 7, v___x_1657_);
lean_ctor_set(v___x_1659_, 8, v___x_1658_);
lean_ctor_set(v___x_1659_, 9, v___x_1650_);
v___x_1660_ = lean_st_mk_ref(v___x_1659_);
v___x_1693_ = lean_st_ref_get(v___x_1630_);
v___x_1694_ = lean_st_ref_get(v___x_1660_);
v_env_1717_ = lean_ctor_get(v___x_1694_, 0);
lean_inc_ref(v_env_1717_);
lean_dec(v___x_1694_);
v___x_1718_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1717_);
lean_dec_ref(v_env_1717_);
v___x_1719_ = 512;
v___x_1720_ = lean_uint16_land(v___x_1642_, v___x_1719_);
v___x_1721_ = 0;
v___x_1722_ = lean_uint16_dec_eq(v___x_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
if (v___x_1718_ == 0)
{
v___y_1696_ = v___x_1632_;
goto v___jp_1695_;
}
else
{
lean_inc(v___x_1618_);
lean_inc(v___x_1617_);
lean_inc_ref(v_fileMap_1637_);
lean_inc_ref(v_fileName_1636_);
v_fileName_1662_ = v_fileName_1636_;
v_fileMap_1663_ = v_fileMap_1637_;
v_currNamespace_1664_ = v___x_1617_;
v_openDecls_1665_ = v___x_1638_;
v_initHeartbeats_1666_ = v___x_1618_;
v_maxHeartbeats_1667_ = v___x_1639_;
v_quotContext_1668_ = v___x_1617_;
v_currMacroScope_1669_ = v___x_1640_;
v_cancelTk_x3f_1670_ = v___x_1631_;
v_inheritedTraceOptions_1671_ = v___x_1693_;
v_currRecDepth_1672_ = v___x_1618_;
v_ref_1673_ = v___x_1641_;
v_suppressElabErrors_1674_ = v_val_1626_;
v_checkDeprecated_1675_ = v___x_1643_;
v_isRecordingDeps_1676_ = v_val_1626_;
goto v___jp_1661_;
}
}
else
{
if (v___x_1718_ == 0)
{
lean_inc(v___x_1618_);
lean_inc(v___x_1617_);
lean_inc_ref(v_fileMap_1637_);
lean_inc_ref(v_fileName_1636_);
v_fileName_1662_ = v_fileName_1636_;
v_fileMap_1663_ = v_fileMap_1637_;
v_currNamespace_1664_ = v___x_1617_;
v_openDecls_1665_ = v___x_1638_;
v_initHeartbeats_1666_ = v___x_1618_;
v_maxHeartbeats_1667_ = v___x_1639_;
v_quotContext_1668_ = v___x_1617_;
v_currMacroScope_1669_ = v___x_1640_;
v_cancelTk_x3f_1670_ = v___x_1631_;
v_inheritedTraceOptions_1671_ = v___x_1693_;
v_currRecDepth_1672_ = v___x_1618_;
v_ref_1673_ = v___x_1641_;
v_suppressElabErrors_1674_ = v_val_1626_;
v_checkDeprecated_1675_ = v___x_1643_;
v_isRecordingDeps_1676_ = v_val_1626_;
goto v___jp_1661_;
}
else
{
v___y_1696_ = v_val_1626_;
goto v___jp_1695_;
}
}
v___jp_1661_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1677_ = l_Lean_maxRecDepth;
v___x_1678_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1616_, v___x_1677_);
lean_inc(v_currMacroScope_1669_);
lean_inc(v_openDecls_1665_);
v___x_1679_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1679_, 0, v_fileName_1662_);
lean_ctor_set(v___x_1679_, 1, v_fileMap_1663_);
lean_ctor_set(v___x_1679_, 2, v_opts_1616_);
lean_ctor_set(v___x_1679_, 3, v___x_1678_);
lean_ctor_set(v___x_1679_, 4, v_currNamespace_1664_);
lean_ctor_set(v___x_1679_, 5, v_openDecls_1665_);
lean_ctor_set(v___x_1679_, 6, v_initHeartbeats_1666_);
lean_ctor_set(v___x_1679_, 7, v_maxHeartbeats_1667_);
lean_ctor_set(v___x_1679_, 8, v_quotContext_1668_);
lean_ctor_set(v___x_1679_, 9, v_currMacroScope_1669_);
lean_ctor_set(v___x_1679_, 10, v_cancelTk_x3f_1670_);
lean_ctor_set(v___x_1679_, 11, v_inheritedTraceOptions_1671_);
lean_inc(v_ref_1673_);
v___x_1680_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_currRecDepth_1672_);
lean_ctor_set(v___x_1680_, 2, v_ref_1673_);
lean_ctor_set_uint16(v___x_1680_, sizeof(void*)*3, v___x_1642_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*3 + 2, v_suppressElabErrors_1674_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*3 + 3, v_checkDeprecated_1675_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*3 + 4, v_isRecordingDeps_1676_);
v___x_1681_ = l_Lean_Language_SnapshotTree_trace(v___x_1624_, v___x_1680_, v___x_1660_);
lean_dec_ref_known(v___x_1680_, 3);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1682_; lean_object* v_traceState_1683_; lean_object* v_traces_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref_known(v___x_1681_, 1);
lean_dec_ref(v___x_1629_);
v___x_1682_ = lean_st_ref_get(v___x_1660_);
lean_dec(v___x_1660_);
v_traceState_1683_ = lean_ctor_get(v___x_1682_, 4);
lean_inc_ref(v_traceState_1683_);
lean_dec(v___x_1682_);
v_traces_1684_ = lean_ctor_get(v_traceState_1683_, 0);
lean_inc_ref(v_traces_1684_);
lean_dec_ref(v_traceState_1683_);
v___x_1685_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1636_);
lean_inc_ref(v_fileMap_1637_);
v___x_1686_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1637_, v_pos_1625_, v_fileName_1636_, v_val_1626_, v_traces_1684_, v___x_1685_);
lean_dec_ref(v_traces_1684_);
v___x_1687_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1688_, 0, v___x_1627_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
lean_ctor_set(v___x_1688_, 2, v___x_1628_);
lean_ctor_set(v___x_1688_, 3, v___x_1623_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*4, v_val_1626_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1650_);
v___x_1690_ = lean_task_pure(v___x_1689_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec_ref_known(v___x_1681_, 1);
lean_dec(v___x_1660_);
lean_dec(v___x_1628_);
lean_dec_ref(v___x_1627_);
lean_dec_ref(v___x_1623_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1629_);
lean_ctor_set(v___x_1691_, 1, v___x_1650_);
v___x_1692_ = lean_task_pure(v___x_1691_);
return v___x_1692_;
}
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v_nextMacroScope_1699_; lean_object* v_ngen_1700_; lean_object* v_auxDeclNGen_1701_; lean_object* v_traceState_1702_; lean_object* v_recordedDeps_1703_; lean_object* v_messages_1704_; lean_object* v_infoState_1705_; lean_object* v_snapshotTasks_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1715_; 
v___x_1697_ = lean_st_ref_take(v___x_1660_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
v_nextMacroScope_1699_ = lean_ctor_get(v___x_1697_, 1);
v_ngen_1700_ = lean_ctor_get(v___x_1697_, 2);
v_auxDeclNGen_1701_ = lean_ctor_get(v___x_1697_, 3);
v_traceState_1702_ = lean_ctor_get(v___x_1697_, 4);
v_recordedDeps_1703_ = lean_ctor_get(v___x_1697_, 6);
v_messages_1704_ = lean_ctor_get(v___x_1697_, 7);
v_infoState_1705_ = lean_ctor_get(v___x_1697_, 8);
v_snapshotTasks_1706_ = lean_ctor_get(v___x_1697_, 9);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v___x_1697_, 5);
lean_dec(v_unused_1716_);
v___x_1708_ = v___x_1697_;
v_isShared_1709_ = v_isSharedCheck_1715_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snapshotTasks_1706_);
lean_inc(v_infoState_1705_);
lean_inc(v_messages_1704_);
lean_inc(v_recordedDeps_1703_);
lean_inc(v_traceState_1702_);
lean_inc(v_auxDeclNGen_1701_);
lean_inc(v_ngen_1700_);
lean_inc(v_nextMacroScope_1699_);
lean_inc(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1715_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = l_Lean_Kernel_enableDiag(v_env_1698_, v___y_1696_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 5, v___x_1649_);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_nextMacroScope_1699_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_ngen_1700_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_auxDeclNGen_1701_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_traceState_1702_);
lean_ctor_set(v_reuseFailAlloc_1714_, 5, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1714_, 6, v_recordedDeps_1703_);
lean_ctor_set(v_reuseFailAlloc_1714_, 7, v_messages_1704_);
lean_ctor_set(v_reuseFailAlloc_1714_, 8, v_infoState_1705_);
lean_ctor_set(v_reuseFailAlloc_1714_, 9, v_snapshotTasks_1706_);
v___x_1712_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_st_ref_put(v___x_1660_, v___x_1712_);
lean_inc(v___x_1618_);
lean_inc(v___x_1617_);
lean_inc_ref(v_fileMap_1637_);
lean_inc_ref(v_fileName_1636_);
v_fileName_1662_ = v_fileName_1636_;
v_fileMap_1663_ = v_fileMap_1637_;
v_currNamespace_1664_ = v___x_1617_;
v_openDecls_1665_ = v___x_1638_;
v_initHeartbeats_1666_ = v___x_1618_;
v_maxHeartbeats_1667_ = v___x_1639_;
v_quotContext_1668_ = v___x_1617_;
v_currMacroScope_1669_ = v___x_1640_;
v_cancelTk_x3f_1670_ = v___x_1631_;
v_inheritedTraceOptions_1671_ = v___x_1693_;
v_currRecDepth_1672_ = v___x_1618_;
v_ref_1673_ = v___x_1641_;
v_suppressElabErrors_1674_ = v_val_1626_;
v_checkDeprecated_1675_ = v___x_1643_;
v_isRecordingDeps_1676_ = v_val_1626_;
goto v___jp_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1723_ = _args[0];
lean_object* v_opts_1724_ = _args[1];
lean_object* v___x_1725_ = _args[2];
lean_object* v___x_1726_ = _args[3];
lean_object* v___x_1727_ = _args[4];
lean_object* v___x_1728_ = _args[5];
lean_object* v___x_1729_ = _args[6];
lean_object* v_env_1730_ = _args[7];
lean_object* v___x_1731_ = _args[8];
lean_object* v___x_1732_ = _args[9];
lean_object* v_pos_1733_ = _args[10];
lean_object* v_val_1734_ = _args[11];
lean_object* v___x_1735_ = _args[12];
lean_object* v___x_1736_ = _args[13];
lean_object* v___x_1737_ = _args[14];
lean_object* v___x_1738_ = _args[15];
lean_object* v___x_1739_ = _args[16];
lean_object* v___x_1740_ = _args[17];
lean_object* v_x_1741_ = _args[18];
lean_object* v___y_1742_ = _args[19];
_start:
{
size_t v___x_37285__boxed_1743_; uint8_t v___x_37286__boxed_1744_; uint8_t v_val_37289__boxed_1745_; uint8_t v___x_37295__boxed_1746_; lean_object* v_res_1747_; 
v___x_37285__boxed_1743_ = lean_unbox_usize(v___x_1728_);
lean_dec(v___x_1728_);
v___x_37286__boxed_1744_ = lean_unbox(v___x_1729_);
v_val_37289__boxed_1745_ = lean_unbox(v_val_1734_);
v___x_37295__boxed_1746_ = lean_unbox(v___x_1740_);
v_res_1747_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1723_, v_opts_1724_, v___x_1725_, v___x_1726_, v___x_1727_, v___x_37285__boxed_1743_, v___x_37286__boxed_1744_, v_env_1730_, v___x_1731_, v___x_1732_, v_pos_1733_, v_val_37289__boxed_1745_, v___x_1735_, v___x_1736_, v___x_1737_, v___x_1738_, v___x_1739_, v___x_37295__boxed_1746_, v_x_1741_);
lean_dec(v___x_1738_);
lean_dec(v_pos_1733_);
lean_dec(v___x_1727_);
lean_dec_ref(v_a_1723_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1748_, lean_object* v___x_1749_, lean_object* v_parserState_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v_toProcessingContext_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_toProcessingContext_1752_ = lean_ctor_get(v_a_1748_, 0);
v___x_1753_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1752_);
v___x_1754_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1752_, v___x_1749_, v_parserState_1750_, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1755_, lean_object* v___x_1756_, lean_object* v_parserState_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1755_, v___x_1756_, v_parserState_1757_, v_x_1758_);
lean_dec_ref(v_a_1755_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1761_, size_t v_i_1762_, size_t v_stop_1763_, lean_object* v_b_1764_){
_start:
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_usize_dec_eq(v_i_1762_, v_stop_1763_);
if (v___x_1766_ == 0)
{
lean_object* v___f_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; 
v___f_1767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1768_ = lean_array_uget_borrowed(v_as_1761_, v_i_1762_);
lean_inc(v___x_1768_);
v___x_1769_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1767_, v___x_1768_);
v___x_1770_ = ((size_t)1ULL);
v___x_1771_ = lean_usize_add(v_i_1762_, v___x_1770_);
v_i_1762_ = v___x_1771_;
v_b_1764_ = v___x_1769_;
goto _start;
}
else
{
return v_b_1764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1773_, lean_object* v_i_1774_, lean_object* v_stop_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_){
_start:
{
size_t v_i_boxed_1778_; size_t v_stop_boxed_1779_; lean_object* v_res_1780_; 
v_i_boxed_1778_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_stop_boxed_1779_ = lean_unbox_usize(v_stop_1775_);
lean_dec(v_stop_1775_);
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1773_, v_i_boxed_1778_, v_stop_boxed_1779_, v_b_1776_);
lean_dec_ref(v_as_1773_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1781_, lean_object* v_stx_1782_, lean_object* v_revCmds_1783_, lean_object* v_newParserState_1784_, lean_object* v_val_1785_, lean_object* v_sync_1786_, lean_object* v_val_1787_, lean_object* v_a_1788_, lean_object* v_oldNext_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v_sync_boxed_1791_; lean_object* v_res_1792_; 
v_sync_boxed_1791_ = lean_unbox(v_sync_1786_);
v_res_1792_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1781_, v_stx_1782_, v_revCmds_1783_, v_newParserState_1784_, v_val_1785_, v_sync_boxed_1791_, v_val_1787_, v_a_1788_, v_oldNext_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1793_, lean_object* v_stx_1794_, lean_object* v_revCmds_1795_, lean_object* v_newParserState_1796_, lean_object* v_val_1797_, uint8_t v_sync_1798_, lean_object* v_val_1799_, lean_object* v_a_1800_, lean_object* v_oldResult_1801_){
_start:
{
lean_object* v_task_1803_; lean_object* v___x_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; 
v_task_1803_ = lean_ctor_get(v_val_1793_, 3);
lean_inc_ref(v_task_1803_);
lean_dec_ref(v_val_1793_);
v___x_1804_ = lean_box(v_sync_1798_);
lean_inc_ref(v_a_1800_);
v___f_1805_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1805_, 0, v_oldResult_1801_);
lean_closure_set(v___f_1805_, 1, v_stx_1794_);
lean_closure_set(v___f_1805_, 2, v_revCmds_1795_);
lean_closure_set(v___f_1805_, 3, v_newParserState_1796_);
lean_closure_set(v___f_1805_, 4, v_val_1797_);
lean_closure_set(v___f_1805_, 5, v___x_1804_);
lean_closure_set(v___f_1805_, 6, v_val_1799_);
lean_closure_set(v___f_1805_, 7, v_a_1800_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = 1;
v___x_1808_ = l_BaseIO_chainTask___redArg(v_task_1803_, v___f_1805_, v___x_1806_, v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1809_, lean_object* v_stx_1810_, lean_object* v_revCmds_1811_, lean_object* v_newParserState_1812_, lean_object* v_val_1813_, lean_object* v_sync_1814_, lean_object* v_val_1815_, lean_object* v_a_1816_, lean_object* v_oldResult_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v_sync_boxed_1819_; lean_object* v_res_1820_; 
v_sync_boxed_1819_ = lean_unbox(v_sync_1814_);
v_res_1820_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1809_, v_stx_1810_, v_revCmds_1811_, v_newParserState_1812_, v_val_1813_, v_sync_boxed_1819_, v_val_1815_, v_a_1816_, v_oldResult_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1820_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1829_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1830_ = l_Lean_Name_append(v___x_1829_, v___x_1828_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1834_, lean_object* v_val_1835_, lean_object* v_fst_1836_, lean_object* v_revCmds_1837_, lean_object* v_fst_1838_, uint8_t v_val_1839_, lean_object* v_a_1840_, lean_object* v_snd_1841_, lean_object* v___x_1842_, uint8_t v___x_1843_, lean_object* v_fst_1844_, lean_object* v_val_1845_, lean_object* v_val_1846_, lean_object* v___x_1847_, lean_object* v___f_1848_, lean_object* v___f_1849_, lean_object* v___f_1850_, lean_object* v_pos_1851_, lean_object* v_cmdState_1852_, lean_object* v_val_1853_, lean_object* v___x_1854_, lean_object* v_opts_1855_, lean_object* v___x_1856_, lean_object* v_snd_1857_, lean_object* v_prom_1858_, lean_object* v_old_x3f_1859_, lean_object* v_parseCancelTk_1860_, lean_object* v_next_x3f_1861_){
_start:
{
lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v_snapshotTasks_1868_; lean_object* v___y_1869_; lean_object* v_traceTask_1870_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; size_t v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_env_1904_; lean_object* v_messages_1905_; lean_object* v_scopes_1906_; lean_object* v_infoState_1907_; lean_object* v_traceState_1908_; lean_object* v_snapshotTasks_1909_; lean_object* v_codeQualityEntryTasks_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_reportedCmdState_1921_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; size_t v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v_reportedCmdState_1978_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; size_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2036_; 
if (lean_obj_tag(v_next_x3f_1861_) == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref(v_parseCancelTk_1860_);
v___x_2089_ = lean_box(0);
v___y_2036_ = v___x_2089_;
goto v___jp_2035_;
}
else
{
lean_object* v_toProcessingContext_2090_; lean_object* v_val_2091_; lean_object* v_pos_2092_; lean_object* v_endPos_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_toProcessingContext_2090_ = lean_ctor_get(v_a_1840_, 0);
v_val_2091_ = lean_ctor_get(v_next_x3f_1861_, 0);
v_pos_2092_ = lean_ctor_get(v_fst_1838_, 0);
v_endPos_2093_ = lean_ctor_get(v_toProcessingContext_2090_, 3);
v___x_2094_ = lean_box(0);
lean_inc(v_endPos_2093_);
lean_inc(v_pos_2092_);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_pos_2092_);
lean_ctor_set(v___x_2095_, 1, v_endPos_2093_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_parseCancelTk_1860_);
v___x_2098_ = l_IO_Promise_result_x21___redArg(v_val_2091_);
v___x_2099_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2094_);
lean_ctor_set(v___x_2099_, 1, v___x_2096_);
lean_ctor_set(v___x_2099_, 2, v___x_2097_);
lean_ctor_set(v___x_2099_, 3, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
v___y_2036_ = v___x_2100_;
goto v___jp_2035_;
}
v___jp_1863_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1871_, 0, v___y_1864_);
lean_ctor_set(v___x_1871_, 1, v___x_1834_);
lean_ctor_set(v___x_1871_, 2, v___y_1869_);
lean_ctor_set(v___x_1871_, 3, v_traceTask_1870_);
v___x_1872_ = lean_array_push(v_snapshotTasks_1868_, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___y_1866_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_io_promise_resolve(v___x_1873_, v_val_1835_);
if (lean_obj_tag(v_next_x3f_1861_) == 1)
{
lean_object* v_val_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_val_1875_ = lean_ctor_get(v_next_x3f_1861_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_next_x3f_1861_, 1);
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_fst_1836_);
lean_ctor_set(v___x_1877_, 1, v_revCmds_1837_);
v___x_1878_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1876_, v_fst_1838_, v___y_1867_, v_val_1875_, v_val_1839_, v___y_1865_, v___x_1877_, v_a_1840_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; 
lean_dec_ref(v___y_1867_);
lean_dec_ref(v___y_1865_);
lean_dec(v_next_x3f_1861_);
lean_dec_ref(v_fst_1838_);
lean_dec(v_revCmds_1837_);
lean_dec(v_fst_1836_);
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
}
v___jp_1880_:
{
lean_object* v_snapshotTasks_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_snapshotTasks_1887_ = lean_ctor_get(v___y_1884_, 10);
lean_inc_ref(v_snapshotTasks_1887_);
v___x_1888_ = lean_mk_empty_array_with_capacity(v___y_1886_);
lean_dec(v___y_1886_);
lean_inc_ref(v___y_1883_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___y_1883_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_task_pure(v___x_1889_);
v___y_1864_ = v___y_1881_;
v___y_1865_ = v___y_1882_;
v___y_1866_ = v___y_1883_;
v___y_1867_ = v___y_1884_;
v_snapshotTasks_1868_ = v_snapshotTasks_1887_;
v___y_1869_ = v___y_1885_;
v_traceTask_1870_ = v___x_1890_;
goto v___jp_1863_;
}
v___jp_1891_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_opts_1931_; uint8_t v_hasTrace_1932_; 
v___x_1922_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1905_);
v___x_1923_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1923_, 0, v___y_1911_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_ctor_set(v___x_1923_, 2, v___y_1902_);
lean_ctor_set(v___x_1923_, 3, v_traceState_1908_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*4, v_val_1839_);
v___x_1924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_reportedCmdState_1921_);
lean_ctor_set(v___x_1924_, 2, v_codeQualityEntryTasks_1910_);
v___x_1925_ = lean_io_promise_resolve(v___x_1924_, v_val_1846_);
v___x_1926_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1907_);
lean_inc(v___y_1920_);
v___x_1927_ = l_BaseIO_chainTask___redArg(v___x_1926_, v___y_1915_, v___y_1920_, v___x_1843_);
v___x_1928_ = l_Lean_inheritedTraceOptions;
v___x_1929_ = lean_st_ref_get(v___x_1928_);
v___x_1930_ = l_List_head_x21___redArg(v___x_1847_, v_scopes_1906_);
lean_dec(v_scopes_1906_);
lean_dec_ref(v___x_1847_);
v_opts_1931_ = lean_ctor_get(v___x_1930_, 1);
lean_inc_ref(v_opts_1931_);
lean_dec(v___x_1930_);
v_hasTrace_1932_ = lean_ctor_get_uint8(v_opts_1931_, sizeof(void*)*1);
if (v_hasTrace_1932_ == 0)
{
lean_dec_ref(v_opts_1931_);
lean_dec(v___x_1929_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v_snapshotTasks_1909_);
lean_dec_ref(v_env_1904_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v_pos_1851_);
lean_dec_ref(v___f_1850_);
lean_dec_ref(v___f_1849_);
lean_dec_ref(v___f_1848_);
lean_dec(v___x_1842_);
v___y_1881_ = v___y_1916_;
v___y_1882_ = v___y_1900_;
v___y_1883_ = v___y_1918_;
v___y_1884_ = v___y_1903_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___y_1920_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1934_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1929_, v_opts_1931_, v___x_1933_);
lean_dec(v___x_1929_);
if (v___x_1934_ == 0)
{
lean_dec_ref(v_opts_1931_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v_snapshotTasks_1909_);
lean_dec_ref(v_env_1904_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v_pos_1851_);
lean_dec_ref(v___f_1850_);
lean_dec_ref(v___f_1849_);
lean_dec_ref(v___f_1848_);
lean_dec(v___x_1842_);
v___y_1881_ = v___y_1916_;
v___y_1882_ = v___y_1900_;
v___y_1883_ = v___y_1918_;
v___y_1884_ = v___y_1903_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___y_1920_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_inc_n(v___y_1920_, 3);
v___x_1935_ = lean_task_map(v___f_1848_, v___y_1917_, v___y_1920_, v___x_1843_);
lean_inc_n(v___y_1912_, 3);
lean_inc_n(v___y_1901_, 2);
lean_inc_n(v___y_1913_, 2);
v___x_1936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1936_, 0, v___y_1913_);
lean_ctor_set(v___x_1936_, 1, v___y_1901_);
lean_ctor_set(v___x_1936_, 2, v___y_1912_);
lean_ctor_set(v___x_1936_, 3, v___x_1935_);
v___x_1937_ = lean_task_map(v___f_1849_, v___y_1919_, v___y_1920_, v___x_1843_);
v___x_1938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1938_, 0, v___y_1913_);
lean_ctor_set(v___x_1938_, 1, v___y_1901_);
lean_ctor_set(v___x_1938_, 2, v___y_1912_);
lean_ctor_set(v___x_1938_, 3, v___x_1937_);
v___x_1939_ = lean_task_map(v___f_1850_, v___y_1914_, v___y_1920_, v___x_1843_);
v___x_1940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1940_, 0, v___y_1913_);
lean_ctor_set(v___x_1940_, 1, v___y_1901_);
lean_ctor_set(v___x_1940_, 2, v___y_1912_);
lean_ctor_set(v___x_1940_, 3, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(3u);
v___x_1942_ = lean_mk_empty_array_with_capacity(v___x_1941_);
v___x_1943_ = lean_array_push(v___x_1942_, v___x_1936_);
v___x_1944_ = lean_array_push(v___x_1943_, v___x_1938_);
v___x_1945_ = lean_array_push(v___x_1944_, v___x_1940_);
v___x_1946_ = l_Array_append___redArg(v___x_1945_, v_snapshotTasks_1909_);
lean_inc_ref(v___y_1918_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___y_1918_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_box_usize(v___y_1896_);
v___x_1949_ = lean_box(v___x_1843_);
v___x_1950_ = lean_box(v_val_1839_);
v___x_1951_ = lean_box(v___x_1934_);
lean_inc_ref(v___x_1947_);
lean_inc_ref(v___y_1895_);
lean_inc_ref(v_a_1840_);
v___f_1952_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1952_, 0, v_a_1840_);
lean_closure_set(v___f_1952_, 1, v_opts_1931_);
lean_closure_set(v___f_1952_, 2, v___x_1842_);
lean_closure_set(v___f_1952_, 3, v___y_1892_);
lean_closure_set(v___f_1952_, 4, v___y_1897_);
lean_closure_set(v___f_1952_, 5, v___x_1948_);
lean_closure_set(v___f_1952_, 6, v___x_1949_);
lean_closure_set(v___f_1952_, 7, v_env_1904_);
lean_closure_set(v___f_1952_, 8, v___y_1895_);
lean_closure_set(v___f_1952_, 9, v___x_1947_);
lean_closure_set(v___f_1952_, 10, v_pos_1851_);
lean_closure_set(v___f_1952_, 11, v___x_1950_);
lean_closure_set(v___f_1952_, 12, v___y_1894_);
lean_closure_set(v___f_1952_, 13, v___y_1893_);
lean_closure_set(v___f_1952_, 14, v___y_1899_);
lean_closure_set(v___f_1952_, 15, v___x_1928_);
lean_closure_set(v___f_1952_, 16, v___y_1898_);
lean_closure_set(v___f_1952_, 17, v___x_1951_);
v___x_1953_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1947_);
v___x_1954_ = lean_io_bind_task(v___x_1953_, v___f_1952_, v___y_1920_, v_val_1839_);
v___y_1864_ = v___y_1916_;
v___y_1865_ = v___y_1900_;
v___y_1866_ = v___y_1918_;
v___y_1867_ = v___y_1903_;
v_snapshotTasks_1868_ = v_snapshotTasks_1909_;
v___y_1869_ = v___y_1912_;
v_traceTask_1870_ = v___x_1954_;
goto v___jp_1863_;
}
}
}
v___jp_1955_:
{
lean_object* v_env_1979_; lean_object* v_messages_1980_; lean_object* v_scopes_1981_; lean_object* v_infoState_1982_; lean_object* v_traceState_1983_; lean_object* v_snapshotTasks_1984_; lean_object* v_codeQualityEntryTasks_1985_; 
v_env_1979_ = lean_ctor_get(v___y_1967_, 0);
lean_inc_ref(v_env_1979_);
v_messages_1980_ = lean_ctor_get(v___y_1967_, 1);
lean_inc_ref(v_messages_1980_);
v_scopes_1981_ = lean_ctor_get(v___y_1967_, 2);
lean_inc(v_scopes_1981_);
v_infoState_1982_ = lean_ctor_get(v___y_1967_, 8);
lean_inc_ref(v_infoState_1982_);
v_traceState_1983_ = lean_ctor_get(v___y_1967_, 9);
lean_inc_ref(v_traceState_1983_);
v_snapshotTasks_1984_ = lean_ctor_get(v___y_1967_, 10);
lean_inc_ref(v_snapshotTasks_1984_);
v_codeQualityEntryTasks_1985_ = lean_ctor_get(v___y_1967_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1985_);
v___y_1892_ = v___y_1956_;
v___y_1893_ = v___y_1957_;
v___y_1894_ = v___y_1958_;
v___y_1895_ = v___y_1959_;
v___y_1896_ = v___y_1961_;
v___y_1897_ = v___y_1960_;
v___y_1898_ = v___y_1962_;
v___y_1899_ = v___y_1963_;
v___y_1900_ = v___y_1964_;
v___y_1901_ = v___y_1965_;
v___y_1902_ = v___y_1966_;
v___y_1903_ = v___y_1967_;
v_env_1904_ = v_env_1979_;
v_messages_1905_ = v_messages_1980_;
v_scopes_1906_ = v_scopes_1981_;
v_infoState_1907_ = v_infoState_1982_;
v_traceState_1908_ = v_traceState_1983_;
v_snapshotTasks_1909_ = v_snapshotTasks_1984_;
v_codeQualityEntryTasks_1910_ = v_codeQualityEntryTasks_1985_;
v___y_1911_ = v___y_1968_;
v___y_1912_ = v___y_1969_;
v___y_1913_ = v___y_1970_;
v___y_1914_ = v___y_1971_;
v___y_1915_ = v___y_1972_;
v___y_1916_ = v___y_1973_;
v___y_1917_ = v___y_1974_;
v___y_1918_ = v___y_1975_;
v___y_1919_ = v___y_1976_;
v___y_1920_ = v___y_1977_;
v_reportedCmdState_1921_ = v_reportedCmdState_1978_;
goto v___jp_1891_;
}
v___jp_1986_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___f_2007_; uint8_t v___x_2008_; 
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___y_2002_);
lean_ctor_set(v___x_2003_, 1, v_val_1845_);
lean_inc_ref(v___y_1988_);
lean_inc_n(v_pos_1851_, 2);
lean_inc(v_revCmds_1837_);
lean_inc(v_fst_1836_);
v___x_2004_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1836_, v_revCmds_1837_, v_cmdState_1852_, v_pos_1851_, v___x_2003_, v___y_1988_, v_a_1840_);
v___x_2005_ = lean_box(v_val_1839_);
v___x_2006_ = lean_box(v___x_1843_);
lean_inc_ref(v_a_1840_);
lean_inc(v___y_1987_);
lean_inc_ref(v___x_1847_);
lean_inc_ref(v___x_2004_);
lean_inc_ref(v___y_1992_);
lean_inc_ref(v___y_1991_);
v___f_2007_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2007_, 0, v___y_1991_);
lean_closure_set(v___f_2007_, 1, v___y_1992_);
lean_closure_set(v___f_2007_, 2, v___x_2005_);
lean_closure_set(v___f_2007_, 3, v_val_1853_);
lean_closure_set(v___f_2007_, 4, v___x_2004_);
lean_closure_set(v___f_2007_, 5, v___x_1847_);
lean_closure_set(v___f_2007_, 6, v___y_1987_);
lean_closure_set(v___f_2007_, 7, v___x_2006_);
lean_closure_set(v___f_2007_, 8, v_a_1840_);
lean_closure_set(v___f_2007_, 9, v_pos_1851_);
lean_closure_set(v___f_2007_, 10, v___x_1854_);
v___x_2008_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1855_, v___x_1856_);
if (v___x_2008_ == 0)
{
lean_inc_ref(v___x_2004_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1989_);
lean_inc(v___y_1987_);
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1991_;
v___y_1959_ = v___y_1992_;
v___y_1960_ = v___y_1994_;
v___y_1961_ = v___y_1993_;
v___y_1962_ = v___y_1996_;
v___y_1963_ = v___y_1998_;
v___y_1964_ = v___y_1988_;
v___y_1965_ = v___y_1997_;
v___y_1966_ = v___y_1989_;
v___y_1967_ = v___x_2004_;
v___y_1968_ = v___y_1991_;
v___y_1969_ = v___y_1996_;
v___y_1970_ = v___y_1995_;
v___y_1971_ = v___y_1999_;
v___y_1972_ = v___f_2007_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_1990_;
v___y_1975_ = v___y_1998_;
v___y_1976_ = v___y_2001_;
v___y_1977_ = v___y_1987_;
v_reportedCmdState_1978_ = v___x_2004_;
goto v___jp_1955_;
}
else
{
uint8_t v___x_2009_; 
lean_inc(v_fst_1836_);
v___x_2009_ = l_Lean_Parser_isTerminalCommand(v_fst_1836_);
if (v___x_2009_ == 0)
{
lean_object* v_env_2010_; lean_object* v_messages_2011_; lean_object* v_scopes_2012_; lean_object* v_infoState_2013_; lean_object* v_traceState_2014_; lean_object* v_snapshotTasks_2015_; lean_object* v_codeQualityEntryTasks_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_env_2010_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref_n(v_env_2010_, 2);
v_messages_2011_ = lean_ctor_get(v___x_2004_, 1);
lean_inc_ref(v_messages_2011_);
v_scopes_2012_ = lean_ctor_get(v___x_2004_, 2);
lean_inc(v_scopes_2012_);
v_infoState_2013_ = lean_ctor_get(v___x_2004_, 8);
lean_inc_ref(v_infoState_2013_);
v_traceState_2014_ = lean_ctor_get(v___x_2004_, 9);
lean_inc_ref(v_traceState_2014_);
v_snapshotTasks_2015_ = lean_ctor_get(v___x_2004_, 10);
lean_inc_ref(v_snapshotTasks_2015_);
v_codeQualityEntryTasks_2016_ = lean_ctor_get(v___x_2004_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2016_);
v___x_2017_ = lean_mk_empty_array_with_capacity(v___y_1994_);
lean_inc_ref(v___x_2017_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_inc_n(v___y_1987_, 4);
v___x_2019_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2017_);
lean_ctor_set(v___x_2019_, 2, v___y_1987_);
lean_ctor_set(v___x_2019_, 3, v___y_1987_);
lean_ctor_set_usize(v___x_2019_, 4, v___y_1993_);
v___x_2020_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2019_, 2);
v___x_2021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2019_);
lean_ctor_set(v___x_2021_, 2, v___x_2020_);
v___x_2022_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2023_ = l_Lean_Options_empty;
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_mk_empty_array_with_capacity(v___y_1987_);
lean_inc_ref_n(v___x_2025_, 3);
lean_inc_n(v___x_1842_, 2);
v___x_2026_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2026_, 0, v___x_2022_);
lean_ctor_set(v___x_2026_, 1, v___x_2023_);
lean_ctor_set(v___x_2026_, 2, v___x_1842_);
lean_ctor_set(v___x_2026_, 3, v___x_2024_);
lean_ctor_set(v___x_2026_, 4, v___x_2024_);
lean_ctor_set(v___x_2026_, 5, v___x_2025_);
lean_ctor_set(v___x_2026_, 6, v___x_2025_);
lean_ctor_set(v___x_2026_, 7, v___x_2024_);
lean_ctor_set(v___x_2026_, 8, v___x_2024_);
lean_ctor_set(v___x_2026_, 9, v___x_2024_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10, v_val_1839_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10 + 1, v_val_1839_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10 + 2, v_val_1839_);
v___x_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___x_2024_);
v___x_2028_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2029_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2030_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1842_);
v___x_2031_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
lean_ctor_set(v___x_2032_, 2, v___x_2019_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*3, v___x_1843_);
v___x_2033_ = lean_box(0);
lean_inc_ref(v___y_1992_);
v___x_2034_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2034_, 0, v_env_2010_);
lean_ctor_set(v___x_2034_, 1, v___x_2021_);
lean_ctor_set(v___x_2034_, 2, v___x_2027_);
lean_ctor_set(v___x_2034_, 3, v___x_2020_);
lean_ctor_set(v___x_2034_, 4, v___x_2028_);
lean_ctor_set(v___x_2034_, 5, v___y_1987_);
lean_ctor_set(v___x_2034_, 6, v___x_2029_);
lean_ctor_set(v___x_2034_, 7, v___x_2030_);
lean_ctor_set(v___x_2034_, 8, v___x_2032_);
lean_ctor_set(v___x_2034_, 9, v___y_1992_);
lean_ctor_set(v___x_2034_, 10, v___x_2025_);
lean_ctor_set(v___x_2034_, 11, v___x_2033_);
lean_ctor_set(v___x_2034_, 12, v___x_2025_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1989_);
v___y_1892_ = v___y_1987_;
v___y_1893_ = v___y_1989_;
v___y_1894_ = v___y_1991_;
v___y_1895_ = v___y_1992_;
v___y_1896_ = v___y_1993_;
v___y_1897_ = v___y_1994_;
v___y_1898_ = v___y_1996_;
v___y_1899_ = v___y_1998_;
v___y_1900_ = v___y_1988_;
v___y_1901_ = v___y_1997_;
v___y_1902_ = v___y_1989_;
v___y_1903_ = v___x_2004_;
v_env_1904_ = v_env_2010_;
v_messages_1905_ = v_messages_2011_;
v_scopes_1906_ = v_scopes_2012_;
v_infoState_1907_ = v_infoState_2013_;
v_traceState_1908_ = v_traceState_2014_;
v_snapshotTasks_1909_ = v_snapshotTasks_2015_;
v_codeQualityEntryTasks_1910_ = v_codeQualityEntryTasks_2016_;
v___y_1911_ = v___y_1991_;
v___y_1912_ = v___y_1996_;
v___y_1913_ = v___y_1995_;
v___y_1914_ = v___y_1999_;
v___y_1915_ = v___f_2007_;
v___y_1916_ = v___y_2000_;
v___y_1917_ = v___y_1990_;
v___y_1918_ = v___y_1998_;
v___y_1919_ = v___y_2001_;
v___y_1920_ = v___y_1987_;
v_reportedCmdState_1921_ = v___x_2034_;
goto v___jp_1891_;
}
else
{
lean_inc_ref(v___x_2004_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1989_);
lean_inc(v___y_1987_);
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1991_;
v___y_1959_ = v___y_1992_;
v___y_1960_ = v___y_1994_;
v___y_1961_ = v___y_1993_;
v___y_1962_ = v___y_1996_;
v___y_1963_ = v___y_1998_;
v___y_1964_ = v___y_1988_;
v___y_1965_ = v___y_1997_;
v___y_1966_ = v___y_1989_;
v___y_1967_ = v___x_2004_;
v___y_1968_ = v___y_1991_;
v___y_1969_ = v___y_1996_;
v___y_1970_ = v___y_1995_;
v___y_1971_ = v___y_1999_;
v___y_1972_ = v___f_2007_;
v___y_1973_ = v___y_2000_;
v___y_1974_ = v___y_1990_;
v___y_1975_ = v___y_1998_;
v___y_1976_ = v___y_2001_;
v___y_1977_ = v___y_1987_;
v_reportedCmdState_1978_ = v___x_2004_;
goto v___jp_1955_;
}
}
}
v___jp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2037_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1841_);
v___x_2038_ = l_IO_CancelToken_new();
v___x_2039_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1842_);
v___x_2040_ = l_Lean_Name_str___override(v___x_1842_, v___x_2039_);
v___x_2041_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2042_ = l_Lean_Name_str___override(v___x_2040_, v___x_2041_);
v___x_2043_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2044_ = l_Lean_Name_str___override(v___x_2042_, v___x_2043_);
v___x_2045_ = l_Lean_Name_str___override(v___x_2044_, v___x_2041_);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = l_Lean_Name_num___override(v___x_2045_, v___x_2046_);
v___x_2048_ = l_Lean_Name_str___override(v___x_2047_, v___x_2041_);
v___x_2049_ = l_Lean_Name_str___override(v___x_2048_, v___x_2043_);
v___x_2050_ = l_Lean_Name_str___override(v___x_2049_, v___x_2041_);
v___x_2051_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2052_ = l_Lean_Name_str___override(v___x_2050_, v___x_2051_);
v___x_2053_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2054_ = l_Lean_Name_str___override(v___x_2052_, v___x_2053_);
v___x_2055_ = l_Lean_Name_toString(v___x_2054_, v___x_1843_);
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_unsigned_to_nat(32u);
v___x_2058_ = ((size_t)5ULL);
v___x_2059_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2055_, 2);
v___x_2060_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2060_, 0, v___x_2055_);
lean_ctor_set(v___x_2060_, 1, v___x_2037_);
lean_ctor_set(v___x_2060_, 2, v___x_2056_);
lean_ctor_set(v___x_2060_, 3, v___x_2059_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*4, v_val_1839_);
v___x_2061_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2062_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2062_, 0, v___x_2055_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_ctor_set(v___x_2062_, 2, v___x_2056_);
lean_ctor_set(v___x_2062_, 3, v___x_2059_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*4, v_val_1839_);
lean_inc(v_fst_1844_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_fst_1844_);
v___x_2064_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2063_);
lean_inc_ref(v___x_2038_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2038_);
v___x_2066_ = l_IO_Promise_result_x21___redArg(v_val_1845_);
lean_inc_ref(v___x_2066_);
lean_inc(v___x_2064_);
lean_inc_ref_n(v___x_2063_, 3);
v___x_2067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2063_);
lean_ctor_set(v___x_2067_, 1, v___x_2064_);
lean_ctor_set(v___x_2067_, 2, v___x_2065_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
v___x_2068_ = l_IO_Promise_result_x21___redArg(v_val_1846_);
lean_inc_ref(v___x_2068_);
lean_inc_n(v___x_1834_, 3);
v___x_2069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2063_);
lean_ctor_set(v___x_2069_, 1, v___x_1834_);
lean_ctor_set(v___x_2069_, 2, v___x_2056_);
lean_ctor_set(v___x_2069_, 3, v___x_2068_);
v___x_2070_ = l_IO_Promise_result_x21___redArg(v_val_1853_);
lean_inc_ref(v___x_2070_);
v___x_2071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2063_);
lean_ctor_set(v___x_2071_, 1, v___x_1834_);
lean_ctor_set(v___x_2071_, 2, v___x_2056_);
lean_ctor_set(v___x_2071_, 3, v___x_2070_);
v___x_2072_ = l_IO_Promise_result_x21___redArg(v_val_1835_);
v___x_2073_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2056_);
lean_ctor_set(v___x_2073_, 1, v___x_1834_);
lean_ctor_set(v___x_2073_, 2, v___x_2056_);
lean_ctor_set(v___x_2073_, 3, v___x_2072_);
lean_inc_ref(v___x_2062_);
v___x_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2062_);
lean_ctor_set(v___x_2074_, 1, v___x_2067_);
lean_ctor_set(v___x_2074_, 2, v___x_2069_);
lean_ctor_set(v___x_2074_, 3, v___x_2071_);
lean_ctor_set(v___x_2074_, 4, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2060_);
lean_ctor_set(v___x_2075_, 1, v_fst_1844_);
lean_ctor_set(v___x_2075_, 2, v_snd_1857_);
lean_ctor_set(v___x_2075_, 3, v___x_2074_);
lean_ctor_set(v___x_2075_, 4, v___y_2036_);
v___x_2076_ = lean_io_promise_resolve(v___x_2075_, v_prom_1858_);
if (lean_obj_tag(v_old_x3f_1859_) == 0)
{
v___y_1987_ = v___x_2046_;
v___y_1988_ = v___x_2038_;
v___y_1989_ = v___x_2056_;
v___y_1990_ = v___x_2066_;
v___y_1991_ = v___x_2055_;
v___y_1992_ = v___x_2059_;
v___y_1993_ = v___x_2058_;
v___y_1994_ = v___x_2057_;
v___y_1995_ = v___x_2063_;
v___y_1996_ = v___x_2056_;
v___y_1997_ = v___x_2064_;
v___y_1998_ = v___x_2062_;
v___y_1999_ = v___x_2070_;
v___y_2000_ = v___x_2056_;
v___y_2001_ = v___x_2068_;
v___y_2002_ = v___x_2056_;
goto v___jp_1986_;
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2088_; 
v_val_2077_ = lean_ctor_get(v_old_x3f_1859_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_old_x3f_1859_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2079_ = v_old_x3f_1859_;
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v_old_x3f_1859_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_elabSnap_2081_; lean_object* v_stx_2082_; lean_object* v_elabSnap_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v_elabSnap_2081_ = lean_ctor_get(v_val_2077_, 3);
lean_inc_ref(v_elabSnap_2081_);
v_stx_2082_ = lean_ctor_get(v_val_2077_, 1);
lean_inc(v_stx_2082_);
lean_dec(v_val_2077_);
v_elabSnap_2083_ = lean_ctor_get(v_elabSnap_2081_, 1);
lean_inc_ref(v_elabSnap_2083_);
lean_dec_ref(v_elabSnap_2081_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_stx_2082_);
lean_ctor_set(v___x_2084_, 1, v_elabSnap_2083_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2084_);
v___x_2086_ = v___x_2079_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v___y_1987_ = v___x_2046_;
v___y_1988_ = v___x_2038_;
v___y_1989_ = v___x_2056_;
v___y_1990_ = v___x_2066_;
v___y_1991_ = v___x_2055_;
v___y_1992_ = v___x_2059_;
v___y_1993_ = v___x_2058_;
v___y_1994_ = v___x_2057_;
v___y_1995_ = v___x_2063_;
v___y_1996_ = v___x_2056_;
v___y_1997_ = v___x_2064_;
v___y_1998_ = v___x_2062_;
v___y_1999_ = v___x_2070_;
v___y_2000_ = v___x_2056_;
v___y_2001_ = v___x_2068_;
v___y_2002_ = v___x_2086_;
goto v___jp_1986_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2102_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2101_);
return v___x_2102_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2106_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2107_, lean_object* v_revCmds_2108_, lean_object* v_fst_2109_, uint8_t v_val_2110_, lean_object* v_a_2111_, lean_object* v_snd_2112_, lean_object* v___x_2113_, uint8_t v___x_2114_, lean_object* v___x_2115_, lean_object* v___f_2116_, lean_object* v___f_2117_, lean_object* v___f_2118_, lean_object* v_pos_2119_, lean_object* v_cmdState_2120_, lean_object* v___x_2121_, lean_object* v_opts_2122_, lean_object* v_prom_2123_, lean_object* v_old_x3f_2124_, lean_object* v_parseCancelTk_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v_traceTask_2140_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2164_; lean_object* v___y_2165_; size_t v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v_env_2175_; lean_object* v_messages_2176_; lean_object* v_scopes_2177_; lean_object* v_infoState_2178_; lean_object* v_traceState_2179_; lean_object* v_snapshotTasks_2180_; lean_object* v_codeQualityEntryTasks_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v_reportedCmdState_2195_; lean_object* v___y_2230_; size_t v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v_reportedCmdState_2254_; lean_object* v___x_2262_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; size_t v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v_fst_2393_; lean_object* v_snd_2394_; uint8_t v___x_2406_; 
v___x_2127_ = lean_io_promise_new();
v___x_2128_ = lean_io_promise_new();
v___x_2129_ = lean_io_promise_new();
v___x_2130_ = lean_io_promise_new();
v___x_2262_ = l_Lean_internal_cmdlineSnapshots;
v___x_2406_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2122_, v___x_2262_);
if (v___x_2406_ == 0)
{
lean_inc_ref(v_fst_2109_);
lean_inc(v_fst_2107_);
v_fst_2393_ = v_fst_2107_;
v_snd_2394_ = v_fst_2109_;
goto v___jp_2392_;
}
else
{
uint8_t v___x_2407_; 
lean_inc(v_fst_2107_);
v___x_2407_ = l_Lean_Parser_isTerminalCommand(v_fst_2107_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2393_ = v___x_2408_;
v_snd_2394_ = v___x_2409_;
goto v___jp_2392_;
}
else
{
lean_inc_ref(v_fst_2109_);
lean_inc(v_fst_2107_);
v_fst_2393_ = v_fst_2107_;
v_snd_2394_ = v_fst_2109_;
goto v___jp_2392_;
}
}
v___jp_2131_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2141_, 0, v___y_2138_);
lean_ctor_set(v___x_2141_, 1, v___y_2136_);
lean_ctor_set(v___x_2141_, 2, v___y_2132_);
lean_ctor_set(v___x_2141_, 3, v_traceTask_2140_);
v___x_2142_ = lean_array_push(v_snapshotTasks_2134_, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___y_2137_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_io_promise_resolve(v___x_2143_, v___x_2130_);
lean_dec(v___x_2130_);
if (lean_obj_tag(v___y_2135_) == 1)
{
lean_object* v_val_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_val_2145_ = lean_ctor_get(v___y_2135_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___y_2135_, 1);
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_fst_2107_);
lean_ctor_set(v___x_2147_, 1, v_revCmds_2108_);
v___x_2148_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2146_, v_fst_2109_, v___y_2133_, v_val_2145_, v_val_2110_, v___y_2139_, v___x_2147_, v_a_2111_);
return v___x_2148_;
}
else
{
lean_object* v___x_2149_; 
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_fst_2109_);
lean_dec(v_revCmds_2108_);
lean_dec(v_fst_2107_);
v___x_2149_ = lean_box(0);
return v___x_2149_;
}
}
v___jp_2150_:
{
lean_object* v_snapshotTasks_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_snapshotTasks_2159_ = lean_ctor_get(v___y_2152_, 10);
lean_inc_ref(v_snapshotTasks_2159_);
v___x_2160_ = lean_mk_empty_array_with_capacity(v___y_2153_);
lean_dec(v___y_2153_);
lean_inc_ref(v___y_2156_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___y_2156_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_task_pure(v___x_2161_);
v___y_2132_ = v___y_2151_;
v___y_2133_ = v___y_2152_;
v_snapshotTasks_2134_ = v_snapshotTasks_2159_;
v___y_2135_ = v___y_2155_;
v___y_2136_ = v___y_2154_;
v___y_2137_ = v___y_2156_;
v___y_2138_ = v___y_2157_;
v___y_2139_ = v___y_2158_;
v_traceTask_2140_ = v___x_2162_;
goto v___jp_2131_;
}
v___jp_2163_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v_opts_2205_; uint8_t v_hasTrace_2206_; 
v___x_2196_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2176_);
v___x_2197_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2197_, 0, v___y_2182_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
lean_ctor_set(v___x_2197_, 2, v___y_2193_);
lean_ctor_set(v___x_2197_, 3, v_traceState_2179_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*4, v_val_2110_);
v___x_2198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set(v___x_2198_, 1, v_reportedCmdState_2195_);
lean_ctor_set(v___x_2198_, 2, v_codeQualityEntryTasks_2181_);
v___x_2199_ = lean_io_promise_resolve(v___x_2198_, v___x_2128_);
lean_dec(v___x_2128_);
v___x_2200_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2178_);
lean_inc(v___y_2190_);
v___x_2201_ = l_BaseIO_chainTask___redArg(v___x_2200_, v___y_2188_, v___y_2190_, v___x_2114_);
v___x_2202_ = l_Lean_inheritedTraceOptions;
v___x_2203_ = lean_st_ref_get(v___x_2202_);
v___x_2204_ = l_List_head_x21___redArg(v___x_2115_, v_scopes_2177_);
lean_dec(v_scopes_2177_);
lean_dec_ref(v___x_2115_);
v_opts_2205_ = lean_ctor_get(v___x_2204_, 1);
lean_inc_ref(v_opts_2205_);
lean_dec(v___x_2204_);
v_hasTrace_2206_ = lean_ctor_get_uint8(v_opts_2205_, sizeof(void*)*1);
if (v_hasTrace_2206_ == 0)
{
lean_dec_ref(v_opts_2205_);
lean_dec(v___x_2203_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v_snapshotTasks_2180_);
lean_dec_ref(v_env_2175_);
lean_dec(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_pos_2119_);
lean_dec_ref(v___f_2118_);
lean_dec_ref(v___f_2117_);
lean_dec_ref(v___f_2116_);
lean_dec(v___x_2113_);
v___y_2151_ = v___y_2173_;
v___y_2152_ = v___y_2174_;
v___y_2153_ = v___y_2190_;
v___y_2154_ = v___y_2183_;
v___y_2155_ = v___y_2191_;
v___y_2156_ = v___y_2186_;
v___y_2157_ = v___y_2187_;
v___y_2158_ = v___y_2189_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2208_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2203_, v_opts_2205_, v___x_2207_);
lean_dec(v___x_2203_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v_opts_2205_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v_snapshotTasks_2180_);
lean_dec_ref(v_env_2175_);
lean_dec(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_pos_2119_);
lean_dec_ref(v___f_2118_);
lean_dec_ref(v___f_2117_);
lean_dec_ref(v___f_2116_);
lean_dec(v___x_2113_);
v___y_2151_ = v___y_2173_;
v___y_2152_ = v___y_2174_;
v___y_2153_ = v___y_2190_;
v___y_2154_ = v___y_2183_;
v___y_2155_ = v___y_2191_;
v___y_2156_ = v___y_2186_;
v___y_2157_ = v___y_2187_;
v___y_2158_ = v___y_2189_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___f_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_inc_n(v___y_2190_, 3);
v___x_2209_ = lean_task_map(v___f_2116_, v___y_2194_, v___y_2190_, v___x_2114_);
lean_inc_n(v___y_2173_, 3);
lean_inc_n(v___y_2172_, 2);
lean_inc_n(v___y_2184_, 2);
v___x_2210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2210_, 0, v___y_2184_);
lean_ctor_set(v___x_2210_, 1, v___y_2172_);
lean_ctor_set(v___x_2210_, 2, v___y_2173_);
lean_ctor_set(v___x_2210_, 3, v___x_2209_);
v___x_2211_ = lean_task_map(v___f_2117_, v___y_2185_, v___y_2190_, v___x_2114_);
v___x_2212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2212_, 0, v___y_2184_);
lean_ctor_set(v___x_2212_, 1, v___y_2172_);
lean_ctor_set(v___x_2212_, 2, v___y_2173_);
lean_ctor_set(v___x_2212_, 3, v___x_2211_);
v___x_2213_ = lean_task_map(v___f_2118_, v___y_2192_, v___y_2190_, v___x_2114_);
v___x_2214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2184_);
lean_ctor_set(v___x_2214_, 1, v___y_2172_);
lean_ctor_set(v___x_2214_, 2, v___y_2173_);
lean_ctor_set(v___x_2214_, 3, v___x_2213_);
v___x_2215_ = lean_unsigned_to_nat(3u);
v___x_2216_ = lean_mk_empty_array_with_capacity(v___x_2215_);
v___x_2217_ = lean_array_push(v___x_2216_, v___x_2210_);
v___x_2218_ = lean_array_push(v___x_2217_, v___x_2212_);
v___x_2219_ = lean_array_push(v___x_2218_, v___x_2214_);
v___x_2220_ = l_Array_append___redArg(v___x_2219_, v_snapshotTasks_2180_);
lean_inc_ref(v___y_2186_);
v___x_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___y_2186_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_box_usize(v___y_2166_);
v___x_2223_ = lean_box(v___x_2114_);
v___x_2224_ = lean_box(v_val_2110_);
v___x_2225_ = lean_box(v___x_2208_);
lean_inc_ref(v___x_2221_);
lean_inc_ref(v___y_2167_);
lean_inc_ref(v_a_2111_);
v___f_2226_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2226_, 0, v_a_2111_);
lean_closure_set(v___f_2226_, 1, v_opts_2205_);
lean_closure_set(v___f_2226_, 2, v___x_2113_);
lean_closure_set(v___f_2226_, 3, v___y_2168_);
lean_closure_set(v___f_2226_, 4, v___y_2170_);
lean_closure_set(v___f_2226_, 5, v___x_2222_);
lean_closure_set(v___f_2226_, 6, v___x_2223_);
lean_closure_set(v___f_2226_, 7, v_env_2175_);
lean_closure_set(v___f_2226_, 8, v___y_2167_);
lean_closure_set(v___f_2226_, 9, v___x_2221_);
lean_closure_set(v___f_2226_, 10, v_pos_2119_);
lean_closure_set(v___f_2226_, 11, v___x_2224_);
lean_closure_set(v___f_2226_, 12, v___y_2164_);
lean_closure_set(v___f_2226_, 13, v___y_2171_);
lean_closure_set(v___f_2226_, 14, v___y_2169_);
lean_closure_set(v___f_2226_, 15, v___x_2202_);
lean_closure_set(v___f_2226_, 16, v___y_2165_);
lean_closure_set(v___f_2226_, 17, v___x_2225_);
v___x_2227_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2221_);
v___x_2228_ = lean_io_bind_task(v___x_2227_, v___f_2226_, v___y_2190_, v_val_2110_);
v___y_2132_ = v___y_2173_;
v___y_2133_ = v___y_2174_;
v_snapshotTasks_2134_ = v_snapshotTasks_2180_;
v___y_2135_ = v___y_2191_;
v___y_2136_ = v___y_2183_;
v___y_2137_ = v___y_2186_;
v___y_2138_ = v___y_2187_;
v___y_2139_ = v___y_2189_;
v_traceTask_2140_ = v___x_2228_;
goto v___jp_2131_;
}
}
}
v___jp_2229_:
{
lean_object* v_env_2255_; lean_object* v_messages_2256_; lean_object* v_scopes_2257_; lean_object* v_infoState_2258_; lean_object* v_traceState_2259_; lean_object* v_snapshotTasks_2260_; lean_object* v_codeQualityEntryTasks_2261_; 
v_env_2255_ = lean_ctor_get(v___y_2240_, 0);
lean_inc_ref(v_env_2255_);
v_messages_2256_ = lean_ctor_get(v___y_2240_, 1);
lean_inc_ref(v_messages_2256_);
v_scopes_2257_ = lean_ctor_get(v___y_2240_, 2);
lean_inc(v_scopes_2257_);
v_infoState_2258_ = lean_ctor_get(v___y_2240_, 8);
lean_inc_ref(v_infoState_2258_);
v_traceState_2259_ = lean_ctor_get(v___y_2240_, 9);
lean_inc_ref(v_traceState_2259_);
v_snapshotTasks_2260_ = lean_ctor_get(v___y_2240_, 10);
lean_inc_ref(v_snapshotTasks_2260_);
v_codeQualityEntryTasks_2261_ = lean_ctor_get(v___y_2240_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2261_);
v___y_2164_ = v___y_2230_;
v___y_2165_ = v___y_2232_;
v___y_2166_ = v___y_2231_;
v___y_2167_ = v___y_2233_;
v___y_2168_ = v___y_2234_;
v___y_2169_ = v___y_2235_;
v___y_2170_ = v___y_2236_;
v___y_2171_ = v___y_2237_;
v___y_2172_ = v___y_2238_;
v___y_2173_ = v___y_2239_;
v___y_2174_ = v___y_2240_;
v_env_2175_ = v_env_2255_;
v_messages_2176_ = v_messages_2256_;
v_scopes_2177_ = v_scopes_2257_;
v_infoState_2178_ = v_infoState_2258_;
v_traceState_2179_ = v_traceState_2259_;
v_snapshotTasks_2180_ = v_snapshotTasks_2260_;
v_codeQualityEntryTasks_2181_ = v_codeQualityEntryTasks_2261_;
v___y_2182_ = v___y_2241_;
v___y_2183_ = v___y_2242_;
v___y_2184_ = v___y_2243_;
v___y_2185_ = v___y_2244_;
v___y_2186_ = v___y_2245_;
v___y_2187_ = v___y_2246_;
v___y_2188_ = v___y_2247_;
v___y_2189_ = v___y_2248_;
v___y_2190_ = v___y_2249_;
v___y_2191_ = v___y_2250_;
v___y_2192_ = v___y_2251_;
v___y_2193_ = v___y_2252_;
v___y_2194_ = v___y_2253_;
v_reportedCmdState_2195_ = v_reportedCmdState_2254_;
goto v___jp_2163_;
}
v___jp_2263_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; uint8_t v___x_2287_; 
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___y_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2127_);
lean_inc_ref(v___y_2272_);
lean_inc_n(v_pos_2119_, 2);
lean_inc(v_revCmds_2108_);
lean_inc(v_fst_2107_);
v___x_2283_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2107_, v_revCmds_2108_, v_cmdState_2120_, v_pos_2119_, v___x_2282_, v___y_2272_, v_a_2111_);
v___x_2284_ = lean_box(v_val_2110_);
v___x_2285_ = lean_box(v___x_2114_);
lean_inc_ref(v_a_2111_);
lean_inc(v___y_2270_);
lean_inc_ref(v___x_2115_);
lean_inc_ref(v___x_2283_);
lean_inc_ref(v___y_2269_);
lean_inc_ref(v___y_2266_);
v___f_2286_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2286_, 0, v___y_2266_);
lean_closure_set(v___f_2286_, 1, v___y_2269_);
lean_closure_set(v___f_2286_, 2, v___x_2284_);
lean_closure_set(v___f_2286_, 3, v___x_2129_);
lean_closure_set(v___f_2286_, 4, v___x_2283_);
lean_closure_set(v___f_2286_, 5, v___x_2115_);
lean_closure_set(v___f_2286_, 6, v___y_2270_);
lean_closure_set(v___f_2286_, 7, v___x_2285_);
lean_closure_set(v___f_2286_, 8, v_a_2111_);
lean_closure_set(v___f_2286_, 9, v_pos_2119_);
lean_closure_set(v___f_2286_, 10, v___x_2121_);
v___x_2287_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2122_, v___x_2262_);
if (v___x_2287_ == 0)
{
lean_inc_ref(v___x_2283_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2266_);
v___y_2230_ = v___y_2266_;
v___y_2231_ = v___y_2267_;
v___y_2232_ = v___y_2268_;
v___y_2233_ = v___y_2269_;
v___y_2234_ = v___y_2270_;
v___y_2235_ = v___y_2271_;
v___y_2236_ = v___y_2273_;
v___y_2237_ = v___y_2274_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2268_;
v___y_2240_ = v___x_2283_;
v___y_2241_ = v___y_2266_;
v___y_2242_ = v___y_2276_;
v___y_2243_ = v___y_2264_;
v___y_2244_ = v___y_2277_;
v___y_2245_ = v___y_2271_;
v___y_2246_ = v___y_2278_;
v___y_2247_ = v___f_2286_;
v___y_2248_ = v___y_2272_;
v___y_2249_ = v___y_2270_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2280_;
v___y_2252_ = v___y_2274_;
v___y_2253_ = v___y_2275_;
v_reportedCmdState_2254_ = v___x_2283_;
goto v___jp_2229_;
}
else
{
uint8_t v___x_2288_; 
lean_inc(v_fst_2107_);
v___x_2288_ = l_Lean_Parser_isTerminalCommand(v_fst_2107_);
if (v___x_2288_ == 0)
{
lean_object* v_env_2289_; lean_object* v_messages_2290_; lean_object* v_scopes_2291_; lean_object* v_infoState_2292_; lean_object* v_traceState_2293_; lean_object* v_snapshotTasks_2294_; lean_object* v_codeQualityEntryTasks_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_env_2289_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref_n(v_env_2289_, 2);
v_messages_2290_ = lean_ctor_get(v___x_2283_, 1);
lean_inc_ref(v_messages_2290_);
v_scopes_2291_ = lean_ctor_get(v___x_2283_, 2);
lean_inc(v_scopes_2291_);
v_infoState_2292_ = lean_ctor_get(v___x_2283_, 8);
lean_inc_ref(v_infoState_2292_);
v_traceState_2293_ = lean_ctor_get(v___x_2283_, 9);
lean_inc_ref(v_traceState_2293_);
v_snapshotTasks_2294_ = lean_ctor_get(v___x_2283_, 10);
lean_inc_ref(v_snapshotTasks_2294_);
v_codeQualityEntryTasks_2295_ = lean_ctor_get(v___x_2283_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2295_);
v___x_2296_ = lean_mk_empty_array_with_capacity(v___y_2273_);
lean_inc_ref(v___x_2296_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_inc_n(v___y_2270_, 4);
v___x_2298_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2296_);
lean_ctor_set(v___x_2298_, 2, v___y_2270_);
lean_ctor_set(v___x_2298_, 3, v___y_2270_);
lean_ctor_set_usize(v___x_2298_, 4, v___y_2267_);
v___x_2299_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2298_, 2);
v___x_2300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2298_);
lean_ctor_set(v___x_2300_, 2, v___x_2299_);
v___x_2301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2302_ = l_Lean_Options_empty;
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_mk_empty_array_with_capacity(v___y_2270_);
lean_inc_ref_n(v___x_2304_, 3);
lean_inc_n(v___x_2113_, 2);
v___x_2305_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2305_, 0, v___x_2301_);
lean_ctor_set(v___x_2305_, 1, v___x_2302_);
lean_ctor_set(v___x_2305_, 2, v___x_2113_);
lean_ctor_set(v___x_2305_, 3, v___x_2303_);
lean_ctor_set(v___x_2305_, 4, v___x_2303_);
lean_ctor_set(v___x_2305_, 5, v___x_2304_);
lean_ctor_set(v___x_2305_, 6, v___x_2304_);
lean_ctor_set(v___x_2305_, 7, v___x_2303_);
lean_ctor_set(v___x_2305_, 8, v___x_2303_);
lean_ctor_set(v___x_2305_, 9, v___x_2303_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*10, v_val_2110_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*10 + 1, v_val_2110_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*10 + 2, v_val_2110_);
v___x_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2303_);
v___x_2307_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2308_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2309_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2113_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
lean_ctor_set(v___x_2311_, 2, v___x_2298_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*3, v___x_2114_);
v___x_2312_ = lean_box(0);
lean_inc_ref(v___y_2269_);
v___x_2313_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2313_, 0, v_env_2289_);
lean_ctor_set(v___x_2313_, 1, v___x_2300_);
lean_ctor_set(v___x_2313_, 2, v___x_2306_);
lean_ctor_set(v___x_2313_, 3, v___x_2299_);
lean_ctor_set(v___x_2313_, 4, v___x_2307_);
lean_ctor_set(v___x_2313_, 5, v___y_2270_);
lean_ctor_set(v___x_2313_, 6, v___x_2308_);
lean_ctor_set(v___x_2313_, 7, v___x_2309_);
lean_ctor_set(v___x_2313_, 8, v___x_2311_);
lean_ctor_set(v___x_2313_, 9, v___y_2269_);
lean_ctor_set(v___x_2313_, 10, v___x_2304_);
lean_ctor_set(v___x_2313_, 11, v___x_2312_);
lean_ctor_set(v___x_2313_, 12, v___x_2304_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2266_);
v___y_2164_ = v___y_2266_;
v___y_2165_ = v___y_2268_;
v___y_2166_ = v___y_2267_;
v___y_2167_ = v___y_2269_;
v___y_2168_ = v___y_2270_;
v___y_2169_ = v___y_2271_;
v___y_2170_ = v___y_2273_;
v___y_2171_ = v___y_2274_;
v___y_2172_ = v___y_2265_;
v___y_2173_ = v___y_2268_;
v___y_2174_ = v___x_2283_;
v_env_2175_ = v_env_2289_;
v_messages_2176_ = v_messages_2290_;
v_scopes_2177_ = v_scopes_2291_;
v_infoState_2178_ = v_infoState_2292_;
v_traceState_2179_ = v_traceState_2293_;
v_snapshotTasks_2180_ = v_snapshotTasks_2294_;
v_codeQualityEntryTasks_2181_ = v_codeQualityEntryTasks_2295_;
v___y_2182_ = v___y_2266_;
v___y_2183_ = v___y_2276_;
v___y_2184_ = v___y_2264_;
v___y_2185_ = v___y_2277_;
v___y_2186_ = v___y_2271_;
v___y_2187_ = v___y_2278_;
v___y_2188_ = v___f_2286_;
v___y_2189_ = v___y_2272_;
v___y_2190_ = v___y_2270_;
v___y_2191_ = v___y_2279_;
v___y_2192_ = v___y_2280_;
v___y_2193_ = v___y_2274_;
v___y_2194_ = v___y_2275_;
v_reportedCmdState_2195_ = v___x_2313_;
goto v___jp_2163_;
}
else
{
lean_inc_ref(v___x_2283_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2266_);
v___y_2230_ = v___y_2266_;
v___y_2231_ = v___y_2267_;
v___y_2232_ = v___y_2268_;
v___y_2233_ = v___y_2269_;
v___y_2234_ = v___y_2270_;
v___y_2235_ = v___y_2271_;
v___y_2236_ = v___y_2273_;
v___y_2237_ = v___y_2274_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2268_;
v___y_2240_ = v___x_2283_;
v___y_2241_ = v___y_2266_;
v___y_2242_ = v___y_2276_;
v___y_2243_ = v___y_2264_;
v___y_2244_ = v___y_2277_;
v___y_2245_ = v___y_2271_;
v___y_2246_ = v___y_2278_;
v___y_2247_ = v___f_2286_;
v___y_2248_ = v___y_2272_;
v___y_2249_ = v___y_2270_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2280_;
v___y_2252_ = v___y_2274_;
v___y_2253_ = v___y_2275_;
v_reportedCmdState_2254_ = v___x_2283_;
goto v___jp_2229_;
}
}
}
v___jp_2314_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2320_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2112_);
v___x_2321_ = l_IO_CancelToken_new();
v___x_2322_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2113_);
v___x_2323_ = l_Lean_Name_str___override(v___x_2113_, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2325_ = l_Lean_Name_str___override(v___x_2323_, v___x_2324_);
v___x_2326_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2327_ = l_Lean_Name_str___override(v___x_2325_, v___x_2326_);
v___x_2328_ = l_Lean_Name_str___override(v___x_2327_, v___x_2324_);
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = l_Lean_Name_num___override(v___x_2328_, v___x_2329_);
v___x_2331_ = l_Lean_Name_str___override(v___x_2330_, v___x_2324_);
v___x_2332_ = l_Lean_Name_str___override(v___x_2331_, v___x_2326_);
v___x_2333_ = l_Lean_Name_str___override(v___x_2332_, v___x_2324_);
v___x_2334_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2335_ = l_Lean_Name_str___override(v___x_2333_, v___x_2334_);
v___x_2336_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2337_ = l_Lean_Name_str___override(v___x_2335_, v___x_2336_);
v___x_2338_ = l_Lean_Name_toString(v___x_2337_, v___x_2114_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_unsigned_to_nat(32u);
v___x_2341_ = lean_mk_empty_array_with_capacity(v___x_2340_);
lean_dec_ref(v___x_2341_);
v___x_2342_ = ((size_t)5ULL);
v___x_2343_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2338_, 2);
v___x_2344_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2344_, 0, v___x_2338_);
lean_ctor_set(v___x_2344_, 1, v___x_2320_);
lean_ctor_set(v___x_2344_, 2, v___x_2339_);
lean_ctor_set(v___x_2344_, 3, v___x_2343_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*4, v_val_2110_);
v___x_2345_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2346_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2338_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
lean_ctor_set(v___x_2346_, 2, v___x_2339_);
lean_ctor_set(v___x_2346_, 3, v___x_2343_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*4, v_val_2110_);
lean_inc(v___y_2317_);
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___y_2317_);
v___x_2348_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2347_);
lean_inc_ref(v___x_2321_);
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2321_);
v___x_2350_ = l_IO_Promise_result_x21___redArg(v___x_2127_);
lean_inc_ref(v___x_2350_);
lean_inc(v___x_2348_);
lean_inc_ref_n(v___x_2347_, 3);
v___x_2351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2347_);
lean_ctor_set(v___x_2351_, 1, v___x_2348_);
lean_ctor_set(v___x_2351_, 2, v___x_2349_);
lean_ctor_set(v___x_2351_, 3, v___x_2350_);
v___x_2352_ = l_IO_Promise_result_x21___redArg(v___x_2128_);
lean_inc_ref(v___x_2352_);
lean_inc_n(v___y_2316_, 3);
v___x_2353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2347_);
lean_ctor_set(v___x_2353_, 1, v___y_2316_);
lean_ctor_set(v___x_2353_, 2, v___x_2339_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
v___x_2354_ = l_IO_Promise_result_x21___redArg(v___x_2129_);
lean_inc_ref(v___x_2354_);
v___x_2355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2347_);
lean_ctor_set(v___x_2355_, 1, v___y_2316_);
lean_ctor_set(v___x_2355_, 2, v___x_2339_);
lean_ctor_set(v___x_2355_, 3, v___x_2354_);
v___x_2356_ = l_IO_Promise_result_x21___redArg(v___x_2130_);
v___x_2357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2339_);
lean_ctor_set(v___x_2357_, 1, v___y_2316_);
lean_ctor_set(v___x_2357_, 2, v___x_2339_);
lean_ctor_set(v___x_2357_, 3, v___x_2356_);
lean_inc_ref(v___x_2346_);
v___x_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2346_);
lean_ctor_set(v___x_2358_, 1, v___x_2351_);
lean_ctor_set(v___x_2358_, 2, v___x_2353_);
lean_ctor_set(v___x_2358_, 3, v___x_2355_);
lean_ctor_set(v___x_2358_, 4, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2344_);
lean_ctor_set(v___x_2359_, 1, v___y_2317_);
lean_ctor_set(v___x_2359_, 2, v___y_2318_);
lean_ctor_set(v___x_2359_, 3, v___x_2358_);
lean_ctor_set(v___x_2359_, 4, v___y_2319_);
v___x_2360_ = lean_io_promise_resolve(v___x_2359_, v_prom_2123_);
if (lean_obj_tag(v_old_x3f_2124_) == 0)
{
v___y_2264_ = v___x_2347_;
v___y_2265_ = v___x_2348_;
v___y_2266_ = v___x_2338_;
v___y_2267_ = v___x_2342_;
v___y_2268_ = v___x_2339_;
v___y_2269_ = v___x_2343_;
v___y_2270_ = v___x_2329_;
v___y_2271_ = v___x_2346_;
v___y_2272_ = v___x_2321_;
v___y_2273_ = v___x_2340_;
v___y_2274_ = v___x_2339_;
v___y_2275_ = v___x_2350_;
v___y_2276_ = v___y_2316_;
v___y_2277_ = v___x_2352_;
v___y_2278_ = v___x_2339_;
v___y_2279_ = v___y_2315_;
v___y_2280_ = v___x_2354_;
v___y_2281_ = v___x_2339_;
goto v___jp_2263_;
}
else
{
lean_object* v_val_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2372_; 
v_val_2361_ = lean_ctor_get(v_old_x3f_2124_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_old_x3f_2124_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2363_ = v_old_x3f_2124_;
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_val_2361_);
lean_dec(v_old_x3f_2124_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_elabSnap_2365_; lean_object* v_stx_2366_; lean_object* v_elabSnap_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v_elabSnap_2365_ = lean_ctor_get(v_val_2361_, 3);
lean_inc_ref(v_elabSnap_2365_);
v_stx_2366_ = lean_ctor_get(v_val_2361_, 1);
lean_inc(v_stx_2366_);
lean_dec(v_val_2361_);
v_elabSnap_2367_ = lean_ctor_get(v_elabSnap_2365_, 1);
lean_inc_ref(v_elabSnap_2367_);
lean_dec_ref(v_elabSnap_2365_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_stx_2366_);
lean_ctor_set(v___x_2368_, 1, v_elabSnap_2367_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2368_);
v___x_2370_ = v___x_2363_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
v___y_2264_ = v___x_2347_;
v___y_2265_ = v___x_2348_;
v___y_2266_ = v___x_2338_;
v___y_2267_ = v___x_2342_;
v___y_2268_ = v___x_2339_;
v___y_2269_ = v___x_2343_;
v___y_2270_ = v___x_2329_;
v___y_2271_ = v___x_2346_;
v___y_2272_ = v___x_2321_;
v___y_2273_ = v___x_2340_;
v___y_2274_ = v___x_2339_;
v___y_2275_ = v___x_2350_;
v___y_2276_ = v___y_2316_;
v___y_2277_ = v___x_2352_;
v___y_2278_ = v___x_2339_;
v___y_2279_ = v___y_2315_;
v___y_2280_ = v___x_2354_;
v___y_2281_ = v___x_2370_;
goto v___jp_2263_;
}
}
}
}
v___jp_2373_:
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2376_);
lean_inc(v_fst_2107_);
v___x_2378_ = l_Lean_Parser_isTerminalCommand(v_fst_2107_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v_toProcessingContext_2380_; lean_object* v_pos_2381_; lean_object* v_endPos_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2379_ = lean_io_promise_new();
v_toProcessingContext_2380_ = lean_ctor_get(v_a_2111_, 0);
v_pos_2381_ = lean_ctor_get(v_fst_2109_, 0);
v_endPos_2382_ = lean_ctor_get(v_toProcessingContext_2380_, 3);
lean_inc(v___x_2379_);
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2379_);
v___x_2384_ = lean_box(0);
lean_inc(v_endPos_2382_);
lean_inc(v_pos_2381_);
v___x_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_pos_2381_);
lean_ctor_set(v___x_2385_, 1, v_endPos_2382_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_parseCancelTk_2125_);
v___x_2388_ = l_IO_Promise_result_x21___redArg(v___x_2379_);
lean_dec(v___x_2379_);
v___x_2389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2384_);
lean_ctor_set(v___x_2389_, 1, v___x_2386_);
lean_ctor_set(v___x_2389_, 2, v___x_2387_);
lean_ctor_set(v___x_2389_, 3, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
v___y_2315_ = v___x_2383_;
v___y_2316_ = v___x_2377_;
v___y_2317_ = v___y_2374_;
v___y_2318_ = v___y_2375_;
v___y_2319_ = v___x_2390_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2391_; 
lean_dec_ref(v_parseCancelTk_2125_);
v___x_2391_ = lean_box(0);
v___y_2315_ = v___x_2391_;
v___y_2316_ = v___x_2377_;
v___y_2317_ = v___y_2374_;
v___y_2318_ = v___y_2375_;
v___y_2319_ = v___x_2391_;
goto v___jp_2314_;
}
}
v___jp_2392_:
{
lean_object* v___x_2395_; 
lean_inc(v_fst_2107_);
v___x_2395_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2107_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_box(0);
v___y_2374_ = v_fst_2393_;
v___y_2375_ = v_snd_2394_;
v___y_2376_ = v___x_2396_;
goto v___jp_2373_;
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2405_; 
v_val_2397_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2399_ = v___x_2395_;
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_val_2397_);
lean_dec(v___x_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
lean_inc(v_val_2397_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_val_2397_);
lean_ctor_set(v___x_2401_, 1, v_val_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2401_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
v___y_2374_ = v_fst_2393_;
v___y_2375_ = v_snd_2394_;
v___y_2376_ = v___x_2403_;
goto v___jp_2373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2410_ = _args[0];
lean_object* v_revCmds_2411_ = _args[1];
lean_object* v_fst_2412_ = _args[2];
lean_object* v_val_2413_ = _args[3];
lean_object* v_a_2414_ = _args[4];
lean_object* v_snd_2415_ = _args[5];
lean_object* v___x_2416_ = _args[6];
lean_object* v___x_2417_ = _args[7];
lean_object* v___x_2418_ = _args[8];
lean_object* v___f_2419_ = _args[9];
lean_object* v___f_2420_ = _args[10];
lean_object* v___f_2421_ = _args[11];
lean_object* v_pos_2422_ = _args[12];
lean_object* v_cmdState_2423_ = _args[13];
lean_object* v___x_2424_ = _args[14];
lean_object* v_opts_2425_ = _args[15];
lean_object* v_prom_2426_ = _args[16];
lean_object* v_old_x3f_2427_ = _args[17];
lean_object* v_parseCancelTk_2428_ = _args[18];
lean_object* v___y_2429_ = _args[19];
_start:
{
uint8_t v_val_38120__boxed_2430_; uint8_t v___x_38123__boxed_2431_; lean_object* v_res_2432_; 
v_val_38120__boxed_2430_ = lean_unbox(v_val_2413_);
v___x_38123__boxed_2431_ = lean_unbox(v___x_2417_);
v_res_2432_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2410_, v_revCmds_2411_, v_fst_2412_, v_val_38120__boxed_2430_, v_a_2414_, v_snd_2415_, v___x_2416_, v___x_38123__boxed_2431_, v___x_2418_, v___f_2419_, v___f_2420_, v___f_2421_, v_pos_2422_, v_cmdState_2423_, v___x_2424_, v_opts_2425_, v_prom_2426_, v_old_x3f_2427_, v_parseCancelTk_2428_);
lean_dec(v_prom_2426_);
lean_dec_ref(v_opts_2425_);
lean_dec_ref(v_a_2414_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2435_, lean_object* v_parserState_2436_, lean_object* v_cmdState_2437_, lean_object* v_prom_2438_, uint8_t v_sync_2439_, lean_object* v_parseCancelTk_2440_, lean_object* v_revCmds_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_toSnapshot_2445_; lean_object* v_stx_2446_; lean_object* v_parserState_2447_; lean_object* v_elabSnap_2448_; lean_object* v_val_2449_; lean_object* v_newParserState_2450_; lean_object* v___y_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v_fst_2530_; lean_object* v_snd_2531_; uint8_t v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___x_2617_; 
v___f_2485_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2486_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2487_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2488_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2489_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2617_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2435_) == 1)
{
lean_object* v_val_2650_; lean_object* v_nextCmdSnap_x3f_2651_; 
v_val_2650_ = lean_ctor_get(v_old_x3f_2435_, 0);
v_nextCmdSnap_x3f_2651_ = lean_ctor_get(v_val_2650_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2651_) == 0)
{
goto v___jp_2618_;
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
lean_dec_ref_known(v___x_2657_, 1);
v_nextCmdSnap_x3f_2659_ = lean_ctor_get(v_val_2658_, 4);
lean_inc(v_nextCmdSnap_x3f_2659_);
lean_dec(v_val_2658_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2659_) == 0)
{
goto v___jp_2618_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
v_val_2660_ = lean_ctor_get(v_nextCmdSnap_x3f_2659_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2659_, 1);
v___x_2661_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2660_);
if (lean_obj_tag(v___x_2661_) == 1)
{
lean_object* v_val_2662_; lean_object* v_parserState_2663_; lean_object* v_pos_2664_; uint8_t v___x_2665_; 
v_val_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v_parserState_2663_ = lean_ctor_get(v_val_2662_, 2);
lean_inc_ref(v_parserState_2663_);
lean_dec(v_val_2662_);
v_pos_2664_ = lean_ctor_get(v_parserState_2663_, 0);
lean_inc(v_pos_2664_);
lean_dec_ref(v_parserState_2663_);
v___x_2665_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2664_, v_a_2442_);
lean_dec(v_pos_2664_);
if (v___x_2665_ == 0)
{
goto v___jp_2618_;
}
else
{
lean_inc(v_val_2656_);
lean_inc_ref(v_elabSnap_2655_);
lean_inc_ref_n(v_parserState_2654_, 2);
lean_inc(v_stx_2653_);
lean_inc_ref(v_toSnapshot_2652_);
lean_dec_ref_known(v_old_x3f_2435_, 1);
lean_dec_ref(v_parseCancelTk_2440_);
lean_dec_ref(v_cmdState_2437_);
lean_dec_ref(v_parserState_2436_);
v_toSnapshot_2445_ = v_toSnapshot_2652_;
v_stx_2446_ = v_stx_2653_;
v_parserState_2447_ = v_parserState_2654_;
v_elabSnap_2448_ = v_elabSnap_2655_;
v_val_2449_ = v_val_2656_;
v_newParserState_2450_ = v_parserState_2654_;
goto v___jp_2444_;
}
}
else
{
lean_dec(v___x_2661_);
goto v___jp_2618_;
}
}
}
else
{
lean_dec(v___x_2657_);
goto v___jp_2618_;
}
}
}
else
{
goto v___jp_2618_;
}
v___jp_2444_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_resultSnap_2453_; lean_object* v_task_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2477_; 
v___x_2451_ = lean_io_promise_new();
v___x_2452_ = l_IO_CancelToken_new();
v_resultSnap_2453_ = lean_ctor_get(v_elabSnap_2448_, 2);
lean_inc_ref(v_resultSnap_2453_);
v_task_2454_ = lean_ctor_get(v_resultSnap_2453_, 3);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_resultSnap_2453_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; lean_object* v_unused_2479_; lean_object* v_unused_2480_; 
v_unused_2478_ = lean_ctor_get(v_resultSnap_2453_, 2);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_resultSnap_2453_, 1);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_resultSnap_2453_, 0);
lean_dec(v_unused_2480_);
v___x_2456_ = v_resultSnap_2453_;
v_isShared_2457_ = v_isSharedCheck_2477_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_task_2454_);
lean_dec(v_resultSnap_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2477_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v_toProcessingContext_2463_; lean_object* v_pos_2464_; lean_object* v_endPos_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2458_ = lean_box(v_sync_2439_);
lean_inc_ref(v_a_2442_);
lean_inc_ref(v___x_2452_);
lean_inc(v___x_2451_);
lean_inc_ref(v_newParserState_2450_);
lean_inc(v_stx_2446_);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2459_, 0, v_val_2449_);
lean_closure_set(v___f_2459_, 1, v_stx_2446_);
lean_closure_set(v___f_2459_, 2, v_revCmds_2441_);
lean_closure_set(v___f_2459_, 3, v_newParserState_2450_);
lean_closure_set(v___f_2459_, 4, v___x_2451_);
lean_closure_set(v___f_2459_, 5, v___x_2458_);
lean_closure_set(v___f_2459_, 6, v___x_2452_);
lean_closure_set(v___f_2459_, 7, v_a_2442_);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = 1;
v___x_2462_ = l_BaseIO_chainTask___redArg(v_task_2454_, v___f_2459_, v___x_2460_, v___x_2461_);
v_toProcessingContext_2463_ = lean_ctor_get(v_a_2442_, 0);
v_pos_2464_ = lean_ctor_get(v_newParserState_2450_, 0);
lean_inc(v_pos_2464_);
lean_dec_ref(v_newParserState_2450_);
v_endPos_2465_ = lean_ctor_get(v_toProcessingContext_2463_, 3);
v___x_2466_ = lean_box(0);
lean_inc(v_endPos_2465_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_pos_2464_);
lean_ctor_set(v___x_2467_, 1, v_endPos_2465_);
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2452_);
v___x_2470_ = l_IO_Promise_result_x21___redArg(v___x_2451_);
lean_dec(v___x_2451_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 3, v___x_2470_);
lean_ctor_set(v___x_2456_, 2, v___x_2469_);
lean_ctor_set(v___x_2456_, 1, v___x_2468_);
lean_ctor_set(v___x_2456_, 0, v___x_2466_);
v___x_2472_ = v___x_2456_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2474_, 0, v_toSnapshot_2445_);
lean_ctor_set(v___x_2474_, 1, v_stx_2446_);
lean_ctor_set(v___x_2474_, 2, v_parserState_2447_);
lean_ctor_set(v___x_2474_, 3, v_elabSnap_2448_);
lean_ctor_set(v___x_2474_, 4, v___x_2473_);
v___x_2475_ = lean_io_promise_resolve(v___x_2474_, v_prom_2438_);
lean_dec(v_prom_2438_);
return v___x_2475_;
}
}
}
v___jp_2481_:
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_box(0);
return v___x_2482_;
}
v___jp_2483_:
{
goto v___jp_2481_;
}
v___jp_2490_:
{
lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2507_);
v___x_2509_ = l_Lean_Parser_isTerminalCommand(v___y_2494_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_io_promise_new();
v___x_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
v___x_2512_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2508_, v___y_2504_, v___y_2495_, v_revCmds_2441_, v___y_2492_, v___y_2493_, v_a_2442_, v___y_2496_, v___y_2499_, v___y_2497_, v___y_2502_, v___y_2505_, v___y_2506_, v___x_2488_, v___f_2487_, v___f_2486_, v___f_2485_, v___y_2491_, v_cmdState_2437_, v___y_2498_, v___x_2489_, v___y_2500_, v___y_2503_, v___y_2501_, v_prom_2438_, v_old_x3f_2435_, v_parseCancelTk_2440_, v___x_2511_);
lean_dec(v_prom_2438_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2506_);
lean_dec(v___y_2504_);
v___y_2484_ = v___x_2512_;
goto v___jp_2483_;
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_box(0);
v___x_2514_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2508_, v___y_2504_, v___y_2495_, v_revCmds_2441_, v___y_2492_, v___y_2493_, v_a_2442_, v___y_2496_, v___y_2499_, v___y_2497_, v___y_2502_, v___y_2505_, v___y_2506_, v___x_2488_, v___f_2487_, v___f_2486_, v___f_2485_, v___y_2491_, v_cmdState_2437_, v___y_2498_, v___x_2489_, v___y_2500_, v___y_2503_, v___y_2501_, v_prom_2438_, v_old_x3f_2435_, v_parseCancelTk_2440_, v___x_2513_);
lean_dec(v_prom_2438_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2506_);
lean_dec(v___y_2504_);
v___y_2484_ = v___x_2514_;
goto v___jp_2483_;
}
}
v___jp_2515_:
{
lean_object* v___x_2532_; 
lean_inc(v___y_2529_);
v___x_2532_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2529_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; 
v___x_2533_ = lean_box(0);
v___y_2491_ = v___y_2516_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2518_;
v___y_2494_ = v___y_2529_;
v___y_2495_ = v___y_2519_;
v___y_2496_ = v___y_2520_;
v___y_2497_ = v___y_2521_;
v___y_2498_ = v___y_2522_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2524_;
v___y_2501_ = v_snd_2531_;
v___y_2502_ = v_fst_2530_;
v___y_2503_ = v___y_2525_;
v___y_2504_ = v___y_2526_;
v___y_2505_ = v___y_2527_;
v___y_2506_ = v___y_2528_;
v___y_2507_ = v___x_2533_;
goto v___jp_2490_;
}
else
{
lean_object* v_val_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
v_val_2534_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2536_ = v___x_2532_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_val_2534_);
lean_dec(v___x_2532_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_inc(v_val_2534_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v_val_2534_);
lean_ctor_set(v___x_2538_, 1, v_val_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
v___y_2491_ = v___y_2516_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2518_;
v___y_2494_ = v___y_2529_;
v___y_2495_ = v___y_2519_;
v___y_2496_ = v___y_2520_;
v___y_2497_ = v___y_2521_;
v___y_2498_ = v___y_2522_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2524_;
v___y_2501_ = v_snd_2531_;
v___y_2502_ = v_fst_2530_;
v___y_2503_ = v___y_2525_;
v___y_2504_ = v___y_2526_;
v___y_2505_ = v___y_2527_;
v___y_2506_ = v___y_2528_;
v___y_2507_ = v___x_2540_;
goto v___jp_2490_;
}
}
}
}
v___jp_2543_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2548_ = l_Lean_Name_str___override(v___y_2545_, v___x_2547_);
v___x_2549_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2550_ = l_Lean_Name_str___override(v___x_2548_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2552_ = l_Lean_Name_str___override(v___x_2550_, v___x_2551_);
v___x_2553_ = l_Lean_Name_str___override(v___x_2552_, v___x_2549_);
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = l_Lean_Name_num___override(v___x_2553_, v___x_2554_);
v___x_2556_ = l_Lean_Name_str___override(v___x_2555_, v___x_2549_);
v___x_2557_ = l_Lean_Name_str___override(v___x_2556_, v___x_2551_);
v___x_2558_ = l_Lean_Name_str___override(v___x_2557_, v___x_2549_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2560_ = l_Lean_Name_str___override(v___x_2558_, v___x_2559_);
v___x_2561_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2562_ = l_Lean_Name_str___override(v___x_2560_, v___x_2561_);
v___x_2563_ = l_Lean_Name_toString(v___x_2562_, v___y_2544_);
v___x_2564_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2567_ = 0;
v___x_2568_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2568_, 0, v___x_2563_);
lean_ctor_set(v___x_2568_, 1, v___x_2564_);
lean_ctor_set(v___x_2568_, 2, v___x_2565_);
lean_ctor_set(v___x_2568_, 3, v___x_2566_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*4, v___x_2567_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2571_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2568_, 3);
v___x_2572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2568_);
lean_ctor_set(v___x_2572_, 1, v_cmdState_2437_);
lean_ctor_set(v___x_2572_, 2, v___x_2571_);
v___x_2573_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2565_, v___x_2572_);
v___x_2574_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2565_, v___x_2568_);
v___x_2575_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2568_);
lean_ctor_set(v___x_2576_, 1, v___x_2570_);
lean_ctor_set(v___x_2576_, 2, v___x_2573_);
lean_ctor_set(v___x_2576_, 3, v___x_2574_);
lean_ctor_set(v___x_2576_, 4, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2568_);
lean_ctor_set(v___x_2577_, 1, v___x_2569_);
lean_ctor_set(v___x_2577_, 2, v___y_2546_);
lean_ctor_set(v___x_2577_, 3, v___x_2576_);
lean_ctor_set(v___x_2577_, 4, v___x_2565_);
v___x_2578_ = lean_io_promise_resolve(v___x_2577_, v_prom_2438_);
lean_dec(v_prom_2438_);
v___x_2579_ = lean_box(0);
return v___x_2579_;
}
v___jp_2580_:
{
uint8_t v___x_2591_; uint8_t v___x_2592_; 
v___x_2591_ = l_IO_CancelToken_isSet(v_parseCancelTk_2440_);
v___x_2592_ = 1;
if (v___x_2591_ == 0)
{
lean_dec(v___y_2587_);
if (v_sync_2439_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2593_ = lean_io_promise_new();
v___x_2594_ = lean_io_promise_new();
v___x_2595_ = lean_io_promise_new();
v___x_2596_ = lean_io_promise_new();
v___x_2597_ = l_Lean_internal_cmdlineSnapshots;
v___x_2598_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2588_, v___x_2597_);
lean_dec_ref(v___y_2588_);
if (v___x_2598_ == 0)
{
lean_inc(v___y_2590_);
v___y_2516_ = v___y_2581_;
v___y_2517_ = v___y_2584_;
v___y_2518_ = v___x_2591_;
v___y_2519_ = v___y_2586_;
v___y_2520_ = v___y_2585_;
v___y_2521_ = v___x_2592_;
v___y_2522_ = v___x_2595_;
v___y_2523_ = v___y_2582_;
v___y_2524_ = v___y_2583_;
v___y_2525_ = v___x_2597_;
v___y_2526_ = v___x_2596_;
v___y_2527_ = v___x_2593_;
v___y_2528_ = v___x_2594_;
v___y_2529_ = v___y_2590_;
v_fst_2530_ = v___y_2590_;
v_snd_2531_ = v___y_2589_;
goto v___jp_2515_;
}
else
{
uint8_t v___x_2599_; 
lean_inc(v___y_2590_);
v___x_2599_ = l_Lean_Parser_isTerminalCommand(v___y_2590_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v___y_2589_);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2516_ = v___y_2581_;
v___y_2517_ = v___y_2584_;
v___y_2518_ = v___x_2591_;
v___y_2519_ = v___y_2586_;
v___y_2520_ = v___y_2585_;
v___y_2521_ = v___x_2592_;
v___y_2522_ = v___x_2595_;
v___y_2523_ = v___y_2582_;
v___y_2524_ = v___y_2583_;
v___y_2525_ = v___x_2597_;
v___y_2526_ = v___x_2596_;
v___y_2527_ = v___x_2593_;
v___y_2528_ = v___x_2594_;
v___y_2529_ = v___y_2590_;
v_fst_2530_ = v___x_2600_;
v_snd_2531_ = v___x_2601_;
goto v___jp_2515_;
}
else
{
lean_inc(v___y_2590_);
v___y_2516_ = v___y_2581_;
v___y_2517_ = v___y_2584_;
v___y_2518_ = v___x_2591_;
v___y_2519_ = v___y_2586_;
v___y_2520_ = v___y_2585_;
v___y_2521_ = v___x_2592_;
v___y_2522_ = v___x_2595_;
v___y_2523_ = v___y_2582_;
v___y_2524_ = v___y_2583_;
v___y_2525_ = v___x_2597_;
v___y_2526_ = v___x_2596_;
v___y_2527_ = v___x_2593_;
v___y_2528_ = v___x_2594_;
v___y_2529_ = v___y_2590_;
v_fst_2530_ = v___y_2590_;
v_snd_2531_ = v___y_2589_;
goto v___jp_2515_;
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec_ref(v___y_2588_);
v___x_2602_ = lean_box(v___x_2591_);
v___x_2603_ = lean_box(v___x_2592_);
lean_inc_ref(v_a_2442_);
v___f_2604_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2604_, 0, v___y_2586_);
lean_closure_set(v___f_2604_, 1, v_revCmds_2441_);
lean_closure_set(v___f_2604_, 2, v___y_2584_);
lean_closure_set(v___f_2604_, 3, v___x_2602_);
lean_closure_set(v___f_2604_, 4, v_a_2442_);
lean_closure_set(v___f_2604_, 5, v___y_2585_);
lean_closure_set(v___f_2604_, 6, v___y_2582_);
lean_closure_set(v___f_2604_, 7, v___x_2603_);
lean_closure_set(v___f_2604_, 8, v___x_2488_);
lean_closure_set(v___f_2604_, 9, v___f_2487_);
lean_closure_set(v___f_2604_, 10, v___f_2486_);
lean_closure_set(v___f_2604_, 11, v___f_2485_);
lean_closure_set(v___f_2604_, 12, v___y_2581_);
lean_closure_set(v___f_2604_, 13, v_cmdState_2437_);
lean_closure_set(v___f_2604_, 14, v___x_2489_);
lean_closure_set(v___f_2604_, 15, v___y_2583_);
lean_closure_set(v___f_2604_, 16, v_prom_2438_);
lean_closure_set(v___f_2604_, 17, v_old_x3f_2435_);
lean_closure_set(v___f_2604_, 18, v_parseCancelTk_2440_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_io_as_task(v___f_2604_, v___x_2605_);
lean_dec_ref(v___x_2606_);
goto v___jp_2481_;
}
}
else
{
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec(v_revCmds_2441_);
lean_dec_ref(v_parseCancelTk_2440_);
if (lean_obj_tag(v_old_x3f_2435_) == 1)
{
lean_object* v_val_2607_; lean_object* v___x_2608_; lean_object* v_children_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_val_2607_ = lean_ctor_get(v_old_x3f_2435_, 0);
lean_inc(v_val_2607_);
lean_dec_ref_known(v_old_x3f_2435_, 1);
v___x_2608_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2607_);
v_children_2609_ = lean_ctor_get(v___x_2608_, 1);
lean_inc_ref(v_children_2609_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_array_get_size(v_children_2609_);
v___x_2612_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_dec_ref(v_children_2609_);
v___y_2544_ = v___x_2592_;
v___y_2545_ = v___y_2587_;
v___y_2546_ = v___y_2589_;
goto v___jp_2543_;
}
else
{
lean_object* v___x_2613_; size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2611_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2609_, v___x_2614_, v___x_2615_, v___x_2613_);
lean_dec_ref(v_children_2609_);
v___y_2544_ = v___x_2592_;
v___y_2545_ = v___y_2587_;
v___y_2546_ = v___y_2589_;
goto v___jp_2543_;
}
}
else
{
lean_dec(v_old_x3f_2435_);
v___y_2544_ = v___x_2592_;
v___y_2545_ = v___y_2587_;
v___y_2546_ = v___y_2589_;
goto v___jp_2543_;
}
}
}
v___jp_2618_:
{
lean_object* v_env_2619_; lean_object* v_scopes_2620_; lean_object* v___x_2621_; lean_object* v_opts_2622_; lean_object* v_currNamespace_2623_; lean_object* v_openDecls_2624_; lean_object* v___x_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_snd_2630_; 
v_env_2619_ = lean_ctor_get(v_cmdState_2437_, 0);
v_scopes_2620_ = lean_ctor_get(v_cmdState_2437_, 2);
v___x_2621_ = l_List_head_x21___redArg(v___x_2488_, v_scopes_2620_);
v_opts_2622_ = lean_ctor_get(v___x_2621_, 1);
lean_inc_ref_n(v_opts_2622_, 2);
v_currNamespace_2623_ = lean_ctor_get(v___x_2621_, 2);
lean_inc(v_currNamespace_2623_);
v_openDecls_2624_ = lean_ctor_get(v___x_2621_, 3);
lean_inc(v_openDecls_2624_);
lean_dec(v___x_2621_);
lean_inc_ref(v_env_2619_);
v___x_2625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2625_, 0, v_env_2619_);
lean_ctor_set(v___x_2625_, 1, v_opts_2622_);
lean_ctor_set(v___x_2625_, 2, v_currNamespace_2623_);
lean_ctor_set(v___x_2625_, 3, v_openDecls_2624_);
lean_inc_ref(v_parserState_2436_);
lean_inc_ref(v_a_2442_);
v___f_2626_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2626_, 0, v_a_2442_);
lean_closure_set(v___f_2626_, 1, v___x_2625_);
lean_closure_set(v___f_2626_, 2, v_parserState_2436_);
v___x_2627_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_profileit(v___x_2627_, v_opts_2622_, v___f_2626_, v___x_2628_);
v_snd_2630_ = lean_ctor_get(v___x_2629_, 1);
lean_inc(v_snd_2630_);
if (lean_obj_tag(v_old_x3f_2435_) == 1)
{
lean_object* v_val_2631_; lean_object* v_fst_2632_; lean_object* v_fst_2633_; lean_object* v_snd_2634_; lean_object* v_pos_2635_; lean_object* v_toSnapshot_2636_; lean_object* v_stx_2637_; lean_object* v_parserState_2638_; lean_object* v_elabSnap_2639_; lean_object* v_nextCmdSnap_x3f_2640_; uint8_t v___x_2641_; 
v_val_2631_ = lean_ctor_get(v_old_x3f_2435_, 0);
v_fst_2632_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_n(v_fst_2632_, 2);
lean_dec(v___x_2629_);
v_fst_2633_ = lean_ctor_get(v_snd_2630_, 0);
lean_inc(v_fst_2633_);
v_snd_2634_ = lean_ctor_get(v_snd_2630_, 1);
lean_inc(v_snd_2634_);
lean_dec(v_snd_2630_);
v_pos_2635_ = lean_ctor_get(v_parserState_2436_, 0);
lean_inc(v_pos_2635_);
lean_dec_ref(v_parserState_2436_);
v_toSnapshot_2636_ = lean_ctor_get(v_val_2631_, 0);
v_stx_2637_ = lean_ctor_get(v_val_2631_, 1);
v_parserState_2638_ = lean_ctor_get(v_val_2631_, 2);
v_elabSnap_2639_ = lean_ctor_get(v_val_2631_, 3);
v_nextCmdSnap_x3f_2640_ = lean_ctor_get(v_val_2631_, 4);
lean_inc(v_stx_2637_);
v___x_2641_ = l_Lean_Syntax_eqWithInfo(v_fst_2632_, v_stx_2637_);
if (v___x_2641_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2640_) == 0)
{
lean_inc(v_fst_2632_);
lean_inc(v_fst_2633_);
lean_inc_ref(v_opts_2622_);
v___y_2581_ = v_pos_2635_;
v___y_2582_ = v___x_2628_;
v___y_2583_ = v_opts_2622_;
v___y_2584_ = v_fst_2633_;
v___y_2585_ = v_snd_2634_;
v___y_2586_ = v_fst_2632_;
v___y_2587_ = v___x_2628_;
v___y_2588_ = v_opts_2622_;
v___y_2589_ = v_fst_2633_;
v___y_2590_ = v_fst_2632_;
goto v___jp_2580_;
}
else
{
lean_object* v_val_2642_; lean_object* v___x_2643_; 
v_val_2642_ = lean_ctor_get(v_nextCmdSnap_x3f_2640_, 0);
lean_inc(v_val_2642_);
v___x_2643_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2617_, v_val_2642_);
lean_inc(v_fst_2632_);
lean_inc(v_fst_2633_);
lean_inc_ref(v_opts_2622_);
v___y_2581_ = v_pos_2635_;
v___y_2582_ = v___x_2628_;
v___y_2583_ = v_opts_2622_;
v___y_2584_ = v_fst_2633_;
v___y_2585_ = v_snd_2634_;
v___y_2586_ = v_fst_2632_;
v___y_2587_ = v___x_2628_;
v___y_2588_ = v_opts_2622_;
v___y_2589_ = v_fst_2633_;
v___y_2590_ = v_fst_2632_;
goto v___jp_2580_;
}
}
else
{
lean_inc(v_val_2631_);
lean_dec(v_pos_2635_);
lean_dec(v_snd_2634_);
lean_dec(v_fst_2632_);
lean_dec_ref_known(v_old_x3f_2435_, 1);
lean_dec_ref(v_opts_2622_);
lean_dec_ref(v_parseCancelTk_2440_);
lean_dec_ref(v_cmdState_2437_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2640_) == 1)
{
lean_object* v_val_2644_; 
lean_inc_ref(v_nextCmdSnap_x3f_2640_);
lean_inc_ref(v_elabSnap_2639_);
lean_inc_ref(v_parserState_2638_);
lean_inc(v_stx_2637_);
lean_inc_ref(v_toSnapshot_2636_);
lean_dec(v_val_2631_);
v_val_2644_ = lean_ctor_get(v_nextCmdSnap_x3f_2640_, 0);
lean_inc(v_val_2644_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2640_, 1);
v_toSnapshot_2445_ = v_toSnapshot_2636_;
v_stx_2446_ = v_stx_2637_;
v_parserState_2447_ = v_parserState_2638_;
v_elabSnap_2448_ = v_elabSnap_2639_;
v_val_2449_ = v_val_2644_;
v_newParserState_2450_ = v_fst_2633_;
goto v___jp_2444_;
}
else
{
lean_object* v___x_2645_; 
lean_dec(v_fst_2633_);
lean_dec(v_revCmds_2441_);
v___x_2645_ = lean_io_promise_resolve(v_val_2631_, v_prom_2438_);
lean_dec(v_prom_2438_);
return v___x_2645_;
}
}
}
else
{
lean_object* v_fst_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v_pos_2649_; 
v_fst_2646_ = lean_ctor_get(v___x_2629_, 0);
lean_inc_n(v_fst_2646_, 2);
lean_dec(v___x_2629_);
v_fst_2647_ = lean_ctor_get(v_snd_2630_, 0);
lean_inc_n(v_fst_2647_, 2);
v_snd_2648_ = lean_ctor_get(v_snd_2630_, 1);
lean_inc(v_snd_2648_);
lean_dec(v_snd_2630_);
v_pos_2649_ = lean_ctor_get(v_parserState_2436_, 0);
lean_inc(v_pos_2649_);
lean_dec_ref(v_parserState_2436_);
lean_inc_ref(v_opts_2622_);
v___y_2581_ = v_pos_2649_;
v___y_2582_ = v___x_2628_;
v___y_2583_ = v_opts_2622_;
v___y_2584_ = v_fst_2647_;
v___y_2585_ = v_snd_2648_;
v___y_2586_ = v_fst_2646_;
v___y_2587_ = v___x_2628_;
v___y_2588_ = v_opts_2622_;
v___y_2589_ = v_fst_2647_;
v___y_2590_ = v_fst_2646_;
goto v___jp_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2666_, lean_object* v_stx_2667_, lean_object* v_revCmds_2668_, lean_object* v_newParserState_2669_, lean_object* v_val_2670_, uint8_t v_sync_2671_, lean_object* v_val_2672_, lean_object* v_a_2673_, lean_object* v_oldNext_2674_){
_start:
{
lean_object* v_cmdState_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_cmdState_2676_ = lean_ctor_get(v_oldResult_2666_, 1);
lean_inc_ref(v_cmdState_2676_);
lean_dec_ref(v_oldResult_2666_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_oldNext_2674_);
v___x_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_stx_2667_);
lean_ctor_set(v___x_2678_, 1, v_revCmds_2668_);
v___x_2679_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2677_, v_newParserState_2669_, v_cmdState_2676_, v_val_2670_, v_sync_2671_, v_val_2672_, v___x_2678_, v_a_2673_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2680_ = _args[0];
lean_object* v_val_2681_ = _args[1];
lean_object* v_fst_2682_ = _args[2];
lean_object* v_revCmds_2683_ = _args[3];
lean_object* v_fst_2684_ = _args[4];
lean_object* v_val_2685_ = _args[5];
lean_object* v_a_2686_ = _args[6];
lean_object* v_snd_2687_ = _args[7];
lean_object* v___x_2688_ = _args[8];
lean_object* v___x_2689_ = _args[9];
lean_object* v_fst_2690_ = _args[10];
lean_object* v_val_2691_ = _args[11];
lean_object* v_val_2692_ = _args[12];
lean_object* v___x_2693_ = _args[13];
lean_object* v___f_2694_ = _args[14];
lean_object* v___f_2695_ = _args[15];
lean_object* v___f_2696_ = _args[16];
lean_object* v_pos_2697_ = _args[17];
lean_object* v_cmdState_2698_ = _args[18];
lean_object* v_val_2699_ = _args[19];
lean_object* v___x_2700_ = _args[20];
lean_object* v_opts_2701_ = _args[21];
lean_object* v___x_2702_ = _args[22];
lean_object* v_snd_2703_ = _args[23];
lean_object* v_prom_2704_ = _args[24];
lean_object* v_old_x3f_2705_ = _args[25];
lean_object* v_parseCancelTk_2706_ = _args[26];
lean_object* v_next_x3f_2707_ = _args[27];
lean_object* v___y_2708_ = _args[28];
_start:
{
uint8_t v_val_37725__boxed_2709_; uint8_t v___x_37728__boxed_2710_; lean_object* v_res_2711_; 
v_val_37725__boxed_2709_ = lean_unbox(v_val_2685_);
v___x_37728__boxed_2710_ = lean_unbox(v___x_2689_);
v_res_2711_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2680_, v_val_2681_, v_fst_2682_, v_revCmds_2683_, v_fst_2684_, v_val_37725__boxed_2709_, v_a_2686_, v_snd_2687_, v___x_2688_, v___x_37728__boxed_2710_, v_fst_2690_, v_val_2691_, v_val_2692_, v___x_2693_, v___f_2694_, v___f_2695_, v___f_2696_, v_pos_2697_, v_cmdState_2698_, v_val_2699_, v___x_2700_, v_opts_2701_, v___x_2702_, v_snd_2703_, v_prom_2704_, v_old_x3f_2705_, v_parseCancelTk_2706_, v_next_x3f_2707_);
lean_dec(v_prom_2704_);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v_opts_2701_);
lean_dec(v_val_2692_);
lean_dec_ref(v_a_2686_);
lean_dec(v_val_2681_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2712_, lean_object* v_parserState_2713_, lean_object* v_cmdState_2714_, lean_object* v_prom_2715_, lean_object* v_sync_2716_, lean_object* v_parseCancelTk_2717_, lean_object* v_revCmds_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
uint8_t v_sync_boxed_2721_; lean_object* v_res_2722_; 
v_sync_boxed_2721_ = lean_unbox(v_sync_2716_);
v_res_2722_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2712_, v_parserState_2713_, v_cmdState_2714_, v_prom_2715_, v_sync_boxed_2721_, v_parseCancelTk_2717_, v_revCmds_2718_, v_a_2719_);
lean_dec_ref(v_a_2719_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2723_, size_t v_i_2724_, size_t v_stop_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2723_, v_i_2724_, v_stop_2725_, v_b_2726_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_stop_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_i_boxed_2736_; size_t v_stop_boxed_2737_; lean_object* v_res_2738_; 
v_i_boxed_2736_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_stop_boxed_2737_ = lean_unbox_usize(v_stop_2732_);
lean_dec(v_stop_2732_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2730_, v_i_boxed_2736_, v_stop_boxed_2737_, v_b_2733_, v___y_2734_);
lean_dec_ref(v___y_2734_);
lean_dec_ref(v_as_2730_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2739_, lean_object* v_opt_2740_){
_start:
{
lean_object* v_name_2741_; lean_object* v_map_2742_; lean_object* v___x_2743_; 
v_name_2741_ = lean_ctor_get(v_opt_2740_, 0);
v_map_2742_ = lean_ctor_get(v_opts_2739_, 0);
v___x_2743_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2742_, v_name_2741_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; 
v___x_2744_ = lean_box(0);
return v___x_2744_;
}
else
{
lean_object* v_val_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2754_; 
v_val_2745_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2747_ = v___x_2743_;
v_isShared_2748_ = v_isSharedCheck_2754_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_val_2745_);
lean_dec(v___x_2743_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2754_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
if (lean_obj_tag(v_val_2745_) == 0)
{
lean_object* v_v_2749_; lean_object* v___x_2751_; 
v_v_2749_ = lean_ctor_get(v_val_2745_, 0);
lean_inc_ref(v_v_2749_);
lean_dec_ref_known(v_val_2745_, 1);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v_v_2749_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_v_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
lean_object* v___x_2753_; 
lean_del_object(v___x_2747_);
lean_dec(v_val_2745_);
v___x_2753_ = lean_box(0);
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2755_, lean_object* v_opt_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2755_, v_opt_2756_);
lean_dec_ref(v_opt_2756_);
lean_dec_ref(v_opts_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2758_);
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2762_, 0, v_x_2759_);
lean_ctor_set(v___x_2762_, 1, v___x_2760_);
lean_ctor_set(v___x_2762_, 2, v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2769_ = l_Lean_Array_toPArray_x27___redArg(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
if (lean_obj_tag(v_a_2770_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = l_List_reverse___redArg(v_a_2771_);
return v___x_2772_;
}
else
{
lean_object* v_head_2773_; lean_object* v_tail_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2787_; 
v_head_2773_ = lean_ctor_get(v_a_2770_, 0);
v_tail_2774_ = lean_ctor_get(v_a_2770_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_a_2770_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2776_ = v_a_2770_;
v_isShared_2777_ = v_isSharedCheck_2787_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_tail_2774_);
lean_inc(v_head_2773_);
lean_dec(v_a_2770_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2787_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2778_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v_head_2773_);
v___x_2780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
v___x_2781_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v_a_2771_);
lean_ctor_set(v___x_2776_, 0, v___x_2782_);
v___x_2784_ = v___x_2776_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_a_2771_);
v___x_2784_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
v_a_2770_ = v_tail_2774_;
v_a_2771_ = v___x_2784_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2788_; double v___x_2789_; 
v___x_2788_ = lean_unsigned_to_nat(1000000000u);
v___x_2789_ = lean_float_of_nat(v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2807_ = l_Lean_MessageData_ofFormat(v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2808_, lean_object* v_stx_2809_, lean_object* v_origStx_2810_, lean_object* v_toProcessingContext_2811_, lean_object* v___x_2812_, lean_object* v_fileMap_2813_, lean_object* v_parserState_2814_, lean_object* v_a_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_toProcessingContext_2821_; lean_object* v___x_2822_; 
v_toProcessingContext_2821_ = lean_ctor_get(v___y_2819_, 0);
lean_inc_ref(v_toProcessingContext_2821_);
lean_inc(v_stx_2809_);
v___x_2822_ = lean_apply_3(v_setupImports_2808_, v_stx_2809_, v_toProcessingContext_2821_, lean_box(0));
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_3035_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_3035_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_3035_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
if (lean_obj_tag(v_a_2823_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; 
lean_dec_ref(v___x_2818_);
lean_dec(v___x_2816_);
lean_dec_ref(v_parserState_2814_);
lean_dec_ref(v_fileMap_2813_);
lean_dec(v___x_2812_);
lean_dec_ref(v_toProcessingContext_2811_);
lean_dec(v_origStx_2810_);
lean_dec(v_stx_2809_);
v_a_2827_ = lean_ctor_get(v_a_2823_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v_a_2823_, 1);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_a_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_3034_; 
v_a_2831_ = lean_ctor_get(v_a_2823_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_2833_ = v_a_2823_;
v_isShared_2834_ = v_isSharedCheck_3034_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v_a_2823_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_3034_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v_mainModuleName_2836_; lean_object* v_package_x3f_2837_; uint8_t v_isModule_2838_; lean_object* v_imports_2839_; lean_object* v_opts_2840_; uint32_t v_trustLevel_2841_; lean_object* v_importArts_2842_; lean_object* v_plugins_2843_; double v___x_2844_; double v___x_2845_; double v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2851_; 
v___x_2835_ = lean_io_mono_nanos_now();
v_mainModuleName_2836_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_mainModuleName_2836_);
v_package_x3f_2837_ = lean_ctor_get(v_a_2831_, 1);
lean_inc(v_package_x3f_2837_);
v_isModule_2838_ = lean_ctor_get_uint8(v_a_2831_, sizeof(void*)*6 + 4);
v_imports_2839_ = lean_ctor_get(v_a_2831_, 2);
lean_inc_ref(v_imports_2839_);
v_opts_2840_ = lean_ctor_get(v_a_2831_, 3);
lean_inc_ref(v_opts_2840_);
v_trustLevel_2841_ = lean_ctor_get_uint32(v_a_2831_, sizeof(void*)*6);
v_importArts_2842_ = lean_ctor_get(v_a_2831_, 4);
lean_inc(v_importArts_2842_);
v_plugins_2843_ = lean_ctor_get(v_a_2831_, 5);
lean_inc_ref(v_plugins_2843_);
lean_dec(v_a_2831_);
v___x_2844_ = lean_float_of_nat(v___x_2835_);
v___x_2845_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2846_ = lean_float_div(v___x_2844_, v___x_2845_);
v___x_2847_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2809_);
v___x_2848_ = l_Lean_MessageLog_empty;
v___x_2849_ = 1;
lean_inc(v_stx_2809_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v_stx_2809_);
v___x_2851_ = v___x_2833_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_stx_2809_);
v___x_2851_ = v_reuseFailAlloc_3033_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_origStx_2810_);
lean_inc_ref(v___x_2851_);
lean_inc_ref(v_opts_2840_);
v___x_2853_ = l_Lean_Elab_processHeaderCore(v___x_2847_, v_imports_2839_, v_isModule_2838_, v_opts_2840_, v___x_2848_, v_toProcessingContext_2811_, v_trustLevel_2841_, v_plugins_2843_, v___x_2849_, v_mainModuleName_2836_, v_package_x3f_2837_, v_importArts_2842_, v___x_2851_, v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_3024_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_3024_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_3024_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_fst_2858_; lean_object* v_snd_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_3023_; 
v_fst_2858_ = lean_ctor_get(v_a_2854_, 0);
v_snd_2859_ = lean_ctor_get(v_a_2854_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_a_2854_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2861_ = v_a_2854_;
v_isShared_2862_ = v_isSharedCheck_3023_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_snd_2859_);
lean_inc(v_fst_2858_);
lean_dec(v_a_2854_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_3023_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; double v___x_2864_; double v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v_traceState_2883_; 
v___x_2863_ = lean_io_mono_nanos_now();
v___x_2864_ = lean_float_of_nat(v___x_2863_);
v___x_2865_ = lean_float_div(v___x_2864_, v___x_2845_);
lean_inc(v_snd_2859_);
v___x_2866_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2859_);
v___x_2867_ = l_Lean_MessageLog_hasErrors(v_snd_2859_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_del_object(v___x_2825_);
lean_dec_ref(v___x_2818_);
v___x_2992_ = l_Lean_trace_profiler_output;
v___x_2993_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2840_, v___x_2992_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = l_Lean_trace_profiler_serve;
v___x_2995_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2840_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2883_ = v___x_2996_;
goto v___jp_2882_;
}
else
{
goto v___jp_2976_;
}
}
else
{
lean_dec_ref_known(v___x_2993_, 1);
goto v___jp_2976_;
}
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint64_t v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
lean_del_object(v___x_2861_);
lean_dec(v_snd_2859_);
lean_dec(v_fst_2858_);
lean_del_object(v___x_2856_);
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_opts_2840_);
lean_dec(v___x_2816_);
lean_dec_ref(v_parserState_2814_);
lean_dec_ref(v_fileMap_2813_);
lean_dec(v_stx_2809_);
v___x_2997_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2998_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2999_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2812_, 2);
v___x_3000_ = l_Lean_Name_num___override(v___x_2999_, v___x_2812_);
v___x_3001_ = l_Lean_Name_str___override(v___x_3000_, v___x_2997_);
v___x_3002_ = l_Lean_Name_str___override(v___x_3001_, v___x_2998_);
v___x_3003_ = l_Lean_Name_str___override(v___x_3002_, v___x_2997_);
v___x_3004_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3005_ = l_Lean_Name_str___override(v___x_3003_, v___x_3004_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3007_ = l_Lean_Name_str___override(v___x_3005_, v___x_3006_);
v___x_3008_ = l_Lean_Name_toString(v___x_3007_, v___x_2849_);
v___x_3009_ = lean_box(0);
v___x_3010_ = 0ULL;
v___x_3011_ = lean_unsigned_to_nat(32u);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_3011_);
v___x_3013_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3014_ = ((size_t)5ULL);
v___x_3015_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3012_);
lean_ctor_set(v___x_3015_, 2, v___x_2812_);
lean_ctor_set(v___x_3015_, 3, v___x_2812_);
lean_ctor_set_usize(v___x_3015_, 4, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set_uint64(v___x_3016_, sizeof(void*)*1, v___x_3010_);
v___x_3017_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3017_, 0, v___x_3008_);
lean_ctor_set(v___x_3017_, 1, v___x_2866_);
lean_ctor_set(v___x_3017_, 2, v___x_3009_);
lean_ctor_set(v___x_3017_, 3, v___x_3016_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*4, v___x_2867_);
v___x_3018_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2818_);
v___x_3019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
lean_ctor_set(v___x_3019_, 2, v___x_3009_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_3019_);
v___x_3021_ = v___x_2825_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
v___jp_2868_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___y_2874_);
v___x_2876_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2876_, 0, v___y_2869_);
lean_ctor_set(v___x_2876_, 1, v___x_2866_);
lean_ctor_set(v___x_2876_, 2, v___x_2875_);
lean_ctor_set(v___x_2876_, 3, v___y_2872_);
lean_ctor_set_uint8(v___x_2876_, sizeof(void*)*4, v___x_2867_);
v___x_2877_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2873_, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2878_, 0, v___y_2871_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
lean_ctor_set(v___x_2878_, 2, v___y_2870_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2878_);
v___x_2880_ = v___x_2856_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
v___jp_2882_:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Language_Lean_reparseOptions(v_opts_2840_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v_env_2887_; lean_object* v_messages_2888_; lean_object* v_scopes_2889_; lean_object* v_usedQuotCtxts_2890_; lean_object* v_nextMacroScope_2891_; lean_object* v_maxRecDepth_2892_; lean_object* v_ngen_2893_; lean_object* v_auxDeclNGen_2894_; lean_object* v_snapshotTasks_2895_; lean_object* v_prevLinterStates_2896_; lean_object* v_codeQualityEntryTasks_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2965_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
lean_inc(v_fst_2858_);
v___x_2886_ = l_Lean_Elab_Command_mkState(v_fst_2858_, v_snd_2859_, v_a_2885_);
v_env_2887_ = lean_ctor_get(v___x_2886_, 0);
v_messages_2888_ = lean_ctor_get(v___x_2886_, 1);
v_scopes_2889_ = lean_ctor_get(v___x_2886_, 2);
v_usedQuotCtxts_2890_ = lean_ctor_get(v___x_2886_, 3);
v_nextMacroScope_2891_ = lean_ctor_get(v___x_2886_, 4);
v_maxRecDepth_2892_ = lean_ctor_get(v___x_2886_, 5);
v_ngen_2893_ = lean_ctor_get(v___x_2886_, 6);
v_auxDeclNGen_2894_ = lean_ctor_get(v___x_2886_, 7);
v_snapshotTasks_2895_ = lean_ctor_get(v___x_2886_, 10);
v_prevLinterStates_2896_ = lean_ctor_get(v___x_2886_, 11);
v_codeQualityEntryTasks_2897_ = lean_ctor_get(v___x_2886_, 12);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; 
v_unused_2966_ = lean_ctor_get(v___x_2886_, 9);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v___x_2886_, 8);
lean_dec(v_unused_2967_);
v___x_2899_ = v___x_2886_;
v_isShared_2900_ = v_isSharedCheck_2965_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2897_);
lean_inc(v_prevLinterStates_2896_);
lean_inc(v_snapshotTasks_2895_);
lean_inc(v_auxDeclNGen_2894_);
lean_inc(v_ngen_2893_);
lean_inc(v_maxRecDepth_2892_);
lean_inc(v_nextMacroScope_2891_);
lean_inc(v_usedQuotCtxts_2890_);
lean_inc(v_scopes_2889_);
lean_inc(v_messages_2888_);
lean_inc(v_env_2887_);
lean_dec(v___x_2886_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2965_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2901_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2902_ = lean_box(0);
lean_inc_n(v___x_2812_, 4);
v___x_2903_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2812_);
lean_ctor_set(v___x_2903_, 1, v___x_2812_);
lean_ctor_set(v___x_2903_, 2, v___x_2812_);
lean_ctor_set(v___x_2903_, 3, v___x_2812_);
lean_ctor_set(v___x_2903_, 4, v___x_2901_);
lean_ctor_set(v___x_2903_, 5, v___x_2901_);
lean_ctor_set(v___x_2903_, 6, v___x_2901_);
lean_ctor_set(v___x_2903_, 7, v___x_2901_);
lean_ctor_set(v___x_2903_, 8, v___x_2901_);
lean_ctor_set(v___x_2903_, 9, v___x_2901_);
lean_ctor_set(v___x_2903_, 10, v___x_2901_);
v___x_2904_ = l_Lean_Options_empty;
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2909_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2909_, 0, v_fst_2858_);
lean_ctor_set(v___x_2909_, 1, v___x_2902_);
lean_ctor_set(v___x_2909_, 2, v_fileMap_2813_);
lean_ctor_set(v___x_2909_, 3, v___x_2903_);
lean_ctor_set(v___x_2909_, 4, v___x_2904_);
lean_ctor_set(v___x_2909_, 5, v___x_2905_);
lean_ctor_set(v___x_2909_, 6, v___x_2906_);
lean_ctor_set(v___x_2909_, 7, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
v___x_2911_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2809_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v_stx_2809_);
lean_ctor_set(v___x_2861_, 0, v___x_2911_);
v___x_2913_ = v___x_2861_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_stx_2809_);
v___x_2913_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
v___x_2915_ = lean_unsigned_to_nat(2u);
v___x_2916_ = l_Lean_Syntax_getArg(v_stx_2809_, v___x_2915_);
lean_dec(v_stx_2809_);
v___x_2917_ = l_Lean_Syntax_getArgs(v___x_2916_);
lean_dec(v___x_2916_);
v___x_2918_ = lean_array_to_list(v___x_2917_);
v___x_2919_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2918_, v___x_2906_);
v___x_2920_ = l_Lean_List_toPArray_x27___redArg(v___x_2919_);
v___x_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2914_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2910_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = lean_mk_empty_array_with_capacity(v___x_2907_);
v___x_2924_ = lean_array_push(v___x_2923_, v___x_2922_);
v___x_2925_ = l_Lean_Array_toPArray_x27___redArg(v___x_2924_);
lean_dec_ref(v___x_2924_);
lean_inc_ref(v___x_2925_);
v___x_2926_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2926_, 0, v___x_2901_);
lean_ctor_set(v___x_2926_, 1, v___x_2901_);
lean_ctor_set(v___x_2926_, 2, v___x_2925_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*3, v___x_2849_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 9, v_traceState_2883_);
lean_ctor_set(v___x_2899_, 8, v___x_2926_);
v___x_2928_ = v___x_2899_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_env_2887_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_messages_2888_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_scopes_2889_);
lean_ctor_set(v_reuseFailAlloc_2963_, 3, v_usedQuotCtxts_2890_);
lean_ctor_set(v_reuseFailAlloc_2963_, 4, v_nextMacroScope_2891_);
lean_ctor_set(v_reuseFailAlloc_2963_, 5, v_maxRecDepth_2892_);
lean_ctor_set(v_reuseFailAlloc_2963_, 6, v_ngen_2893_);
lean_ctor_set(v_reuseFailAlloc_2963_, 7, v_auxDeclNGen_2894_);
lean_ctor_set(v_reuseFailAlloc_2963_, 8, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2963_, 9, v_traceState_2883_);
lean_ctor_set(v_reuseFailAlloc_2963_, 10, v_snapshotTasks_2895_);
lean_ctor_set(v_reuseFailAlloc_2963_, 11, v_prevLinterStates_2896_);
lean_ctor_set(v_reuseFailAlloc_2963_, 12, v_codeQualityEntryTasks_2897_);
v___x_2928_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; lean_object* v_size_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; uint64_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2929_ = lean_io_promise_new();
v___x_2930_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_2930_);
lean_inc(v___x_2929_);
lean_inc_ref(v___x_2928_);
v___x_2931_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2902_, v_parserState_2814_, v___x_2928_, v___x_2929_, v___x_2849_, v___x_2930_, v___x_2906_, v_a_2815_);
v___x_2932_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2933_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2934_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2812_, 3);
v___x_2935_ = l_Lean_Name_num___override(v___x_2934_, v___x_2812_);
v___x_2936_ = lean_unsigned_to_nat(32u);
v___x_2937_ = lean_mk_empty_array_with_capacity(v___x_2936_);
v___x_2938_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2939_ = ((size_t)5ULL);
v___x_2940_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2937_);
lean_ctor_set(v___x_2940_, 2, v___x_2812_);
lean_ctor_set(v___x_2940_, 3, v___x_2812_);
lean_ctor_set_usize(v___x_2940_, 4, v___x_2939_);
v_size_2941_ = lean_ctor_get(v___x_2925_, 2);
v___x_2942_ = l_Lean_Name_str___override(v___x_2935_, v___x_2932_);
v___x_2943_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2816_);
v___x_2944_ = l_Lean_Name_str___override(v___x_2942_, v___x_2933_);
v___x_2945_ = l_Lean_Name_str___override(v___x_2944_, v___x_2932_);
v___x_2946_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2947_ = l_Lean_Name_str___override(v___x_2945_, v___x_2946_);
v___x_2948_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2949_ = l_Lean_Name_str___override(v___x_2947_, v___x_2948_);
v___x_2950_ = l_Lean_Name_toString(v___x_2949_, v___x_2849_);
v___x_2951_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2952_ = 0ULL;
v___x_2953_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2953_, 0, v___x_2940_);
lean_ctor_set_uint64(v___x_2953_, sizeof(void*)*1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2930_);
v___x_2955_ = l_IO_Promise_result_x21___redArg(v___x_2929_);
lean_dec(v___x_2929_);
v___x_2956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2816_);
lean_ctor_set(v___x_2956_, 1, v___x_2943_);
lean_ctor_set(v___x_2956_, 2, v___x_2954_);
lean_ctor_set(v___x_2956_, 3, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2928_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_inc_ref(v___x_2953_);
lean_inc_ref(v___x_2950_);
v___x_2959_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2959_, 0, v___x_2950_);
lean_ctor_set(v___x_2959_, 1, v___x_2951_);
lean_ctor_set(v___x_2959_, 2, v___x_2902_);
lean_ctor_set(v___x_2959_, 3, v___x_2953_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*4, v___x_2867_);
v___x_2960_ = lean_nat_dec_lt(v___x_2812_, v_size_2941_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_dec_ref(v___x_2925_);
lean_dec(v___x_2812_);
v___x_2961_ = l_outOfBounds___redArg(v___x_2817_);
v___y_2869_ = v___x_2950_;
v___y_2870_ = v___x_2958_;
v___y_2871_ = v___x_2959_;
v___y_2872_ = v___x_2953_;
v___y_2873_ = v___x_2851_;
v___y_2874_ = v___x_2961_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2817_, v___x_2925_, v___x_2812_);
lean_dec(v___x_2812_);
lean_dec_ref(v___x_2925_);
v___y_2869_ = v___x_2950_;
v___y_2870_ = v___x_2958_;
v___y_2871_ = v___x_2959_;
v___y_2872_ = v___x_2953_;
v___y_2873_ = v___x_2851_;
v___y_2874_ = v___x_2962_;
goto v___jp_2868_;
}
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v_traceState_2883_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2861_);
lean_dec(v_snd_2859_);
lean_dec(v_fst_2858_);
lean_del_object(v___x_2856_);
lean_dec_ref(v___x_2851_);
lean_dec(v___x_2816_);
lean_dec_ref(v_parserState_2814_);
lean_dec_ref(v_fileMap_2813_);
lean_dec(v___x_2812_);
lean_dec(v_stx_2809_);
v_a_2968_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2884_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2884_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
v___jp_2976_:
{
uint64_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2977_ = 0ULL;
v___x_2978_ = lean_box(0);
v___x_2979_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2980_ = lean_box(0);
v___x_2981_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2982_, 0, v___x_2979_);
lean_ctor_set(v___x_2982_, 1, v___x_2980_);
lean_ctor_set(v___x_2982_, 2, v___x_2981_);
lean_ctor_set_float(v___x_2982_, sizeof(void*)*3, v___x_2846_);
lean_ctor_set_float(v___x_2982_, sizeof(void*)*3 + 8, v___x_2865_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*3 + 16, v___x_2849_);
v___x_2983_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2984_ = lean_mk_empty_array_with_capacity(v___x_2812_);
v___x_2985_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2982_);
lean_ctor_set(v___x_2985_, 1, v___x_2983_);
lean_ctor_set(v___x_2985_, 2, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2978_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_mk_empty_array_with_capacity(v___x_2987_);
v___x_2989_ = lean_array_push(v___x_2988_, v___x_2986_);
v___x_2990_ = l_Lean_Array_toPArray_x27___redArg(v___x_2989_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set_uint64(v___x_2991_, sizeof(void*)*1, v___x_2977_);
v_traceState_2883_ = v___x_2991_;
goto v___jp_2882_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_opts_2840_);
lean_del_object(v___x_2825_);
lean_dec_ref(v___x_2818_);
lean_dec(v___x_2816_);
lean_dec_ref(v_parserState_2814_);
lean_dec_ref(v_fileMap_2813_);
lean_dec(v___x_2812_);
lean_dec(v_stx_2809_);
v_a_3025_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2853_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2853_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
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
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v___x_2818_);
lean_dec(v___x_2816_);
lean_dec_ref(v_parserState_2814_);
lean_dec_ref(v_fileMap_2813_);
lean_dec(v___x_2812_);
lean_dec_ref(v_toProcessingContext_2811_);
lean_dec(v_origStx_2810_);
lean_dec(v_stx_2809_);
v_a_3036_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2822_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2822_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3044_, lean_object* v_stx_3045_, lean_object* v_origStx_3046_, lean_object* v_toProcessingContext_3047_, lean_object* v___x_3048_, lean_object* v_fileMap_3049_, lean_object* v_parserState_3050_, lean_object* v_a_3051_, lean_object* v___x_3052_, lean_object* v___x_3053_, lean_object* v___x_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3044_, v_stx_3045_, v_origStx_3046_, v_toProcessingContext_3047_, v___x_3048_, v_fileMap_3049_, v_parserState_3050_, v_a_3051_, v___x_3052_, v___x_3053_, v___x_3054_, v___y_3055_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_a_3051_);
return v_res_3057_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___f_3059_; 
v___x_3058_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3059_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3059_, 0, v___x_3058_);
return v___f_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3060_, lean_object* v_stx_3061_, lean_object* v_origStx_3062_, lean_object* v_parserState_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_toProcessingContext_3066_; lean_object* v_fileMap_3067_; lean_object* v_endPos_3068_; lean_object* v___x_3069_; lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_toProcessingContext_3066_ = lean_ctor_get(v_a_3064_, 0);
v_fileMap_3067_ = lean_ctor_get(v_toProcessingContext_3066_, 2);
v_endPos_3068_ = lean_ctor_get(v_toProcessingContext_3066_, 3);
v___x_3069_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3070_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3071_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3072_ = lean_box(0);
v___x_3073_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3064_, 2);
lean_inc_ref(v_fileMap_3067_);
lean_inc_ref(v_toProcessingContext_3066_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3074_, 0, v_setupImports_3060_);
lean_closure_set(v___f_3074_, 1, v_stx_3061_);
lean_closure_set(v___f_3074_, 2, v_origStx_3062_);
lean_closure_set(v___f_3074_, 3, v_toProcessingContext_3066_);
lean_closure_set(v___f_3074_, 4, v___x_3073_);
lean_closure_set(v___f_3074_, 5, v_fileMap_3067_);
lean_closure_set(v___f_3074_, 6, v_parserState_3063_);
lean_closure_set(v___f_3074_, 7, v_a_3064_);
lean_closure_set(v___f_3074_, 8, v___x_3072_);
lean_closure_set(v___f_3074_, 9, v___x_3071_);
lean_closure_set(v___f_3074_, 10, v___x_3069_);
lean_inc(v_endPos_3068_);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v_endPos_3068_);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
v___x_3077_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3077_, 0, lean_box(0));
lean_closure_set(v___x_3077_, 1, v___f_3070_);
lean_closure_set(v___x_3077_, 2, v___f_3074_);
lean_closure_set(v___x_3077_, 3, v_a_3064_);
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
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_box(0);
v___x_3087_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3086_);
return v___x_3087_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = 1;
v___x_3093_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3094_ = l_Lean_Name_toString(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3095_ = 0;
v___x_3096_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3097_ = lean_box(0);
v___x_3098_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3099_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3100_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v___x_3098_);
lean_ctor_set(v___x_3100_, 2, v___x_3097_);
lean_ctor_set(v___x_3100_, 3, v___x_3096_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*4, v___x_3095_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3101_, lean_object* v_cmdState_3102_, lean_object* v_a_3103_, lean_object* v_toSnapshot_3104_, lean_object* v_newStx_3105_, lean_object* v_oldCmd_3106_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_diagnostics_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3136_; 
v___x_3108_ = lean_io_promise_new();
v___x_3109_ = l_IO_CancelToken_new();
v___x_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3110_, 0, v_oldCmd_3106_);
v___x_3111_ = 1;
v___x_3112_ = lean_box(0);
lean_inc_ref(v___x_3109_);
lean_inc(v___x_3108_);
lean_inc_ref(v_cmdState_3102_);
v___x_3113_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3110_, v_newParserState_3101_, v_cmdState_3102_, v___x_3108_, v___x_3111_, v___x_3109_, v___x_3112_, v_a_3103_);
v_diagnostics_3114_ = lean_ctor_get(v_toSnapshot_3104_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_toSnapshot_3104_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; lean_object* v_unused_3138_; lean_object* v_unused_3139_; 
v_unused_3137_ = lean_ctor_get(v_toSnapshot_3104_, 3);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_toSnapshot_3104_, 2);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_toSnapshot_3104_, 0);
lean_dec(v_unused_3139_);
v___x_3116_ = v_toSnapshot_3104_;
v_isShared_3117_ = v_isSharedCheck_3136_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_diagnostics_3114_);
lean_dec(v_toSnapshot_3104_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3136_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3120_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3121_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3109_);
v___x_3123_ = l_IO_Promise_result_x21___redArg(v___x_3108_);
lean_dec(v___x_3108_);
v___x_3124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3118_);
lean_ctor_set(v___x_3124_, 1, v___x_3119_);
lean_ctor_set(v___x_3124_, 2, v___x_3122_);
lean_ctor_set(v___x_3124_, 3, v___x_3123_);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_cmdState_3102_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
v___x_3127_ = 0;
v___x_3128_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_newStx_3105_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 3, v___x_3121_);
lean_ctor_set(v___x_3116_, 2, v___x_3118_);
lean_ctor_set(v___x_3116_, 0, v___x_3120_);
v___x_3131_ = v___x_3116_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_diagnostics_3114_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3135_, 3, v___x_3121_);
v___x_3131_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_ctor_set_uint8(v___x_3131_, sizeof(void*)*4, v___x_3127_);
v___x_3132_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3129_, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3128_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
lean_ctor_set(v___x_3133_, 2, v___x_3126_);
v___x_3134_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3118_, v___x_3133_);
return v___x_3134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3140_, lean_object* v_cmdState_3141_, lean_object* v_a_3142_, lean_object* v_toSnapshot_3143_, lean_object* v_newStx_3144_, lean_object* v_oldCmd_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3140_, v_cmdState_3141_, v_a_3142_, v_toSnapshot_3143_, v_newStx_3144_, v_oldCmd_3145_);
lean_dec_ref(v_a_3142_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3148_, lean_object* v_a_3149_, lean_object* v_newStx_3150_, lean_object* v___x_3151_, lean_object* v_oldProcessed_3152_){
_start:
{
lean_object* v_result_x3f_3154_; 
v_result_x3f_3154_ = lean_ctor_get(v_oldProcessed_3152_, 2);
if (lean_obj_tag(v_result_x3f_3154_) == 1)
{
lean_object* v_val_3155_; lean_object* v_firstCmdSnap_3156_; lean_object* v_toSnapshot_3157_; lean_object* v_cmdState_3158_; lean_object* v_stx_x3f_3159_; lean_object* v___f_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; lean_object* v___x_3163_; 
v_val_3155_ = lean_ctor_get(v_result_x3f_3154_, 0);
lean_inc(v_val_3155_);
v_firstCmdSnap_3156_ = lean_ctor_get(v_val_3155_, 1);
lean_inc_ref(v_firstCmdSnap_3156_);
v_toSnapshot_3157_ = lean_ctor_get(v_oldProcessed_3152_, 0);
lean_inc_ref(v_toSnapshot_3157_);
lean_dec_ref(v_oldProcessed_3152_);
v_cmdState_3158_ = lean_ctor_get(v_val_3155_, 0);
lean_inc_ref(v_cmdState_3158_);
lean_dec(v_val_3155_);
v_stx_x3f_3159_ = lean_ctor_get(v_firstCmdSnap_3156_, 0);
lean_inc(v_stx_x3f_3159_);
lean_inc_ref(v_a_3149_);
v___f_3160_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3160_, 0, v_newParserState_3148_);
lean_closure_set(v___f_3160_, 1, v_cmdState_3158_);
lean_closure_set(v___f_3160_, 2, v_a_3149_);
lean_closure_set(v___f_3160_, 3, v_toSnapshot_3157_);
lean_closure_set(v___f_3160_, 4, v_newStx_3150_);
v___x_3161_ = lean_box(0);
v___x_3162_ = 1;
v___x_3163_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3156_, v___f_3160_, v_stx_x3f_3159_, v___x_3151_, v___x_3161_, v___x_3162_);
return v___x_3163_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v___x_3151_);
lean_dec_ref(v_newParserState_3148_);
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_newStx_3150_);
v___x_3165_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3164_, v_oldProcessed_3152_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3166_, lean_object* v_a_3167_, lean_object* v_newStx_3168_, lean_object* v___x_3169_, lean_object* v_oldProcessed_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3166_, v_a_3167_, v_newStx_3168_, v___x_3169_, v_oldProcessed_3170_);
lean_dec_ref(v_a_3167_);
return v_res_3172_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3173_ = 0;
v___x_3174_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3175_ = lean_box(0);
v___x_3176_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3177_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3178_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___x_3176_);
lean_ctor_set(v___x_3178_, 2, v___x_3175_);
lean_ctor_set(v___x_3178_, 3, v___x_3174_);
lean_ctor_set_uint8(v___x_3178_, sizeof(void*)*4, v___x_3173_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3179_, lean_object* v_a_3180_, lean_object* v_old_3181_, lean_object* v_newStx_3182_, lean_object* v_newParserState_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_result_x3f_3186_; 
v_result_x3f_3186_ = lean_ctor_get(v_old_3181_, 4);
lean_inc(v_result_x3f_3186_);
if (lean_obj_tag(v_result_x3f_3186_) == 1)
{
lean_object* v_val_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3241_; 
v_val_3187_ = lean_ctor_get(v_result_x3f_3186_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_result_x3f_3186_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3189_ = v_result_x3f_3186_;
v_isShared_3190_ = v_isSharedCheck_3241_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_val_3187_);
lean_dec(v_result_x3f_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3241_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_processedSnap_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3239_; 
v_processedSnap_3191_ = lean_ctor_get(v_val_3187_, 1);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_val_3187_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_val_3187_, 0);
lean_dec(v_unused_3240_);
v___x_3193_ = v_val_3187_;
v_isShared_3194_ = v_isSharedCheck_3239_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_processedSnap_3191_);
lean_dec(v_val_3187_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3239_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v_toSnapshot_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3234_; 
v_toSnapshot_3195_ = lean_ctor_get(v_old_3181_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_old_3181_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; lean_object* v_unused_3236_; lean_object* v_unused_3237_; lean_object* v_unused_3238_; 
v_unused_3235_ = lean_ctor_get(v_old_3181_, 4);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_old_3181_, 3);
lean_dec(v_unused_3236_);
v_unused_3237_ = lean_ctor_get(v_old_3181_, 2);
lean_dec(v_unused_3237_);
v_unused_3238_ = lean_ctor_get(v_old_3181_, 1);
lean_dec(v_unused_3238_);
v___x_3197_ = v_old_3181_;
v_isShared_3198_ = v_isSharedCheck_3234_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_toSnapshot_3195_);
lean_dec(v_old_3181_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3234_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_pos_3199_; lean_object* v_endPos_3200_; lean_object* v_stx_x3f_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; lean_object* v___x_3207_; lean_object* v_diagnostics_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3230_; 
v_pos_3199_ = lean_ctor_get(v_newParserState_3183_, 0);
v_endPos_3200_ = lean_ctor_get(v_toProcessingContext_3179_, 3);
v_stx_x3f_3201_ = lean_ctor_get(v_processedSnap_3191_, 0);
lean_inc(v_stx_x3f_3201_);
lean_inc(v_endPos_3200_);
lean_inc(v_pos_3199_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_pos_3199_);
lean_ctor_set(v___x_3202_, 1, v_endPos_3200_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_inc_ref(v___x_3203_);
lean_inc(v_newStx_3182_);
lean_inc_ref(v_a_3180_);
lean_inc_ref(v_newParserState_3183_);
v___f_3204_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3204_, 0, v_newParserState_3183_);
lean_closure_set(v___f_3204_, 1, v_a_3180_);
lean_closure_set(v___f_3204_, 2, v_newStx_3182_);
lean_closure_set(v___f_3204_, 3, v___x_3203_);
v___x_3205_ = lean_box(0);
v___x_3206_ = 1;
v___x_3207_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3191_, v___f_3204_, v_stx_x3f_3201_, v___x_3203_, v___x_3205_, v___x_3206_);
v_diagnostics_3208_ = lean_ctor_get(v_toSnapshot_3195_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_toSnapshot_3195_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; lean_object* v_unused_3232_; lean_object* v_unused_3233_; 
v_unused_3231_ = lean_ctor_get(v_toSnapshot_3195_, 3);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v_toSnapshot_3195_, 2);
lean_dec(v_unused_3232_);
v_unused_3233_ = lean_ctor_get(v_toSnapshot_3195_, 0);
lean_dec(v_unused_3233_);
v___x_3210_ = v_toSnapshot_3195_;
v_isShared_3211_ = v_isSharedCheck_3230_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_diagnostics_3208_);
lean_dec(v_toSnapshot_3195_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3230_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3212_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3213_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 1, v___x_3207_);
lean_ctor_set(v___x_3193_, 0, v_newParserState_3183_);
v___x_3215_ = v___x_3193_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_newParserState_3183_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3207_);
v___x_3215_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3217_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3215_);
v___x_3217_ = v___x_3189_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3218_ = 0;
v___x_3219_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3182_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_newStx_3182_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 3, v___x_3213_);
lean_ctor_set(v___x_3210_, 2, v___x_3205_);
lean_ctor_set(v___x_3210_, 0, v___x_3212_);
v___x_3222_ = v___x_3210_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_diagnostics_3208_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v___x_3213_);
v___x_3222_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_ctor_set_uint8(v___x_3222_, sizeof(void*)*4, v___x_3218_);
v___x_3223_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3220_, v___x_3222_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 4, v___x_3217_);
lean_ctor_set(v___x_3197_, 3, v_newStx_3182_);
lean_ctor_set(v___x_3197_, 2, v_toProcessingContext_3179_);
lean_ctor_set(v___x_3197_, 1, v___x_3223_);
lean_ctor_set(v___x_3197_, 0, v___x_3219_);
v___x_3225_ = v___x_3197_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_toProcessingContext_3179_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_newStx_3182_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v___x_3217_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
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
lean_dec(v_result_x3f_3186_);
lean_dec_ref(v_newParserState_3183_);
lean_dec(v_newStx_3182_);
lean_dec_ref(v_toProcessingContext_3179_);
return v_old_3181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3242_, lean_object* v_a_3243_, lean_object* v_old_3244_, lean_object* v_newStx_3245_, lean_object* v_newParserState_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3242_, v_a_3243_, v_old_3244_, v_newStx_3245_, v_newParserState_3246_, v___y_3247_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v_a_3243_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3250_, lean_object* v_setupImports_3251_, lean_object* v_old_x3f_3252_, lean_object* v___x_3253_, lean_object* v___f_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; 
lean_inc_ref(v_toProcessingContext_3250_);
v___x_3257_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3250_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3326_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3326_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3326_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_snd_3262_; lean_object* v_fst_3263_; lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3325_; 
v_snd_3262_ = lean_ctor_get(v_a_3258_, 1);
lean_inc(v_snd_3262_);
v_fst_3263_ = lean_ctor_get(v_a_3258_, 0);
lean_inc(v_fst_3263_);
lean_dec(v_a_3258_);
v_fst_3264_ = lean_ctor_get(v_snd_3262_, 0);
v_snd_3265_ = lean_ctor_get(v_snd_3262_, 1);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_snd_3262_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3267_ = v_snd_3262_;
v_isShared_3268_ = v_isSharedCheck_3325_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snd_3265_);
lean_inc(v_fst_3264_);
lean_dec(v_snd_3262_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3325_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
uint8_t v___x_3269_; 
v___x_3269_ = l_Lean_MessageLog_hasErrors(v_snd_3265_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___y_3272_; 
lean_inc(v_fst_3263_);
v___x_3270_ = l_Lean_Syntax_unsetTrailing(v_fst_3263_);
if (lean_obj_tag(v_old_x3f_3252_) == 1)
{
lean_object* v_val_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3308_; 
v_val_3293_ = lean_ctor_get(v_old_x3f_3252_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_old_x3f_3252_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3295_ = v_old_x3f_3252_;
v_isShared_3296_ = v_isSharedCheck_3308_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_val_3293_);
lean_dec(v_old_x3f_3252_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3308_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v_stx_3297_; lean_object* v_result_x3f_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v_stx_3297_ = lean_ctor_get(v_val_3293_, 3);
v_result_x3f_3298_ = lean_ctor_get(v_val_3293_, 4);
lean_inc(v_stx_3297_);
v___x_3299_ = l_Lean_Syntax_unsetTrailing(v_stx_3297_);
lean_inc(v___x_3270_);
v___x_3300_ = l_Lean_Syntax_eqWithInfo(v___x_3270_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_inc(v_result_x3f_3298_);
lean_del_object(v___x_3295_);
lean_dec(v_val_3293_);
lean_dec_ref(v___f_3254_);
if (lean_obj_tag(v_result_x3f_3298_) == 0)
{
lean_dec_ref(v___x_3253_);
v___y_3272_ = v___y_3255_;
goto v___jp_3271_;
}
else
{
lean_object* v_val_3301_; lean_object* v_processedSnap_3302_; lean_object* v___x_3303_; 
v_val_3301_ = lean_ctor_get(v_result_x3f_3298_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v_result_x3f_3298_, 1);
v_processedSnap_3302_ = lean_ctor_get(v_val_3301_, 1);
lean_inc_ref(v_processedSnap_3302_);
lean_dec(v_val_3301_);
v___x_3303_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3253_, v_processedSnap_3302_);
v___y_3272_ = v___y_3255_;
goto v___jp_3271_;
}
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3306_; 
lean_dec(v___x_3270_);
lean_del_object(v___x_3267_);
lean_dec(v_snd_3265_);
lean_del_object(v___x_3260_);
lean_dec_ref(v___x_3253_);
lean_dec_ref(v_setupImports_3251_);
lean_dec_ref(v_toProcessingContext_3250_);
lean_inc_ref(v___y_3255_);
v___x_3304_ = lean_apply_5(v___f_3254_, v_val_3293_, v_fst_3263_, v_fst_3264_, v___y_3255_, lean_box(0));
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3304_);
v___x_3306_ = v___x_3295_;
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
else
{
lean_dec_ref(v___f_3254_);
lean_dec_ref(v___x_3253_);
lean_dec(v_old_x3f_3252_);
v___y_3272_ = v___y_3255_;
goto v___jp_3271_;
}
v___jp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3273_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3265_);
lean_inc(v_fst_3264_);
lean_inc(v_fst_3263_);
v___x_3274_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3251_, v___x_3270_, v_fst_3263_, v_fst_3264_, v___y_3272_);
v___x_3275_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3276_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_unsigned_to_nat(32u);
v___x_3279_ = lean_mk_empty_array_with_capacity(v___x_3278_);
lean_dec_ref(v___x_3279_);
v___x_3280_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 1, v___x_3274_);
v___x_3282_ = v___x_3267_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_fst_3264_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v___x_3274_);
v___x_3282_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3284_, 0, v___x_3275_);
lean_ctor_set(v___x_3284_, 1, v___x_3276_);
lean_ctor_set(v___x_3284_, 2, v___x_3277_);
lean_ctor_set(v___x_3284_, 3, v___x_3280_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*4, v___x_3269_);
lean_inc(v_fst_3263_);
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v_fst_3263_);
v___x_3286_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3286_, 0, v___x_3275_);
lean_ctor_set(v___x_3286_, 1, v___x_3273_);
lean_ctor_set(v___x_3286_, 2, v___x_3277_);
lean_ctor_set(v___x_3286_, 3, v___x_3280_);
lean_ctor_set_uint8(v___x_3286_, sizeof(void*)*4, v___x_3269_);
v___x_3287_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3285_, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3284_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
lean_ctor_set(v___x_3288_, 2, v_toProcessingContext_3250_);
lean_ctor_set(v___x_3288_, 3, v_fst_3263_);
lean_ctor_set(v___x_3288_, 4, v___x_3283_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3288_);
v___x_3290_ = v___x_3260_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_del_object(v___x_3267_);
lean_dec(v_fst_3264_);
lean_dec_ref(v___f_3254_);
lean_dec_ref(v___x_3253_);
lean_dec(v_old_x3f_3252_);
lean_dec_ref(v_setupImports_3251_);
v___x_3309_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3265_);
v___x_3310_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3311_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_unsigned_to_nat(32u);
v___x_3314_ = lean_mk_empty_array_with_capacity(v___x_3313_);
lean_dec_ref(v___x_3314_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3316_, 0, v___x_3310_);
lean_ctor_set(v___x_3316_, 1, v___x_3311_);
lean_ctor_set(v___x_3316_, 2, v___x_3312_);
lean_ctor_set(v___x_3316_, 3, v___x_3315_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*4, v___x_3269_);
lean_inc(v_fst_3263_);
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v_fst_3263_);
v___x_3318_ = 0;
v___x_3319_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3319_, 0, v___x_3310_);
lean_ctor_set(v___x_3319_, 1, v___x_3309_);
lean_ctor_set(v___x_3319_, 2, v___x_3312_);
lean_ctor_set(v___x_3319_, 3, v___x_3315_);
lean_ctor_set_uint8(v___x_3319_, sizeof(void*)*4, v___x_3318_);
v___x_3320_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3317_, v___x_3319_);
v___x_3321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3316_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
lean_ctor_set(v___x_3321_, 2, v_toProcessingContext_3250_);
lean_ctor_set(v___x_3321_, 3, v_fst_3263_);
lean_ctor_set(v___x_3321_, 4, v___x_3312_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3321_);
v___x_3323_ = v___x_3260_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec_ref(v___f_3254_);
lean_dec_ref(v___x_3253_);
lean_dec(v_old_x3f_3252_);
lean_dec_ref(v_setupImports_3251_);
lean_dec_ref(v_toProcessingContext_3250_);
v_a_3327_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3257_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3257_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3335_, lean_object* v_setupImports_3336_, lean_object* v_old_x3f_3337_, lean_object* v___x_3338_, lean_object* v___f_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3335_, v_setupImports_3336_, v_old_x3f_3337_, v___x_3338_, v___f_3339_, v___y_3340_);
lean_dec_ref(v___y_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3343_, lean_object* v_toProcessingContext_3344_, lean_object* v_x_3345_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3346_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3343_);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3349_, 0, v_x_3345_);
lean_ctor_set(v___x_3349_, 1, v___x_3346_);
lean_ctor_set(v___x_3349_, 2, v_toProcessingContext_3344_);
lean_ctor_set(v___x_3349_, 3, v___x_3347_);
lean_ctor_set(v___x_3349_, 4, v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3350_, lean_object* v_old_x3f_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v_toProcessingContext_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___f_3357_; lean_object* v___f_3358_; lean_object* v___f_3359_; 
v_toProcessingContext_3354_ = lean_ctor_get(v_a_3352_, 0);
v___x_3355_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3356_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3352_);
lean_inc_ref_n(v_toProcessingContext_3354_, 3);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3357_, 0, v_toProcessingContext_3354_);
lean_closure_set(v___f_3357_, 1, v_a_3352_);
lean_inc(v_old_x3f_3351_);
v___f_3358_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3358_, 0, v_toProcessingContext_3354_);
lean_closure_set(v___f_3358_, 1, v_setupImports_3350_);
lean_closure_set(v___f_3358_, 2, v_old_x3f_3351_);
lean_closure_set(v___f_3358_, 3, v___x_3356_);
lean_closure_set(v___f_3358_, 4, v___f_3357_);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3359_, 0, v___x_3355_);
lean_closure_set(v___f_3359_, 1, v_toProcessingContext_3354_);
if (lean_obj_tag(v_old_x3f_3351_) == 1)
{
lean_object* v_val_3360_; lean_object* v_result_x3f_3361_; 
v_val_3360_ = lean_ctor_get(v_old_x3f_3351_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v_old_x3f_3351_, 1);
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
v___x_3372_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
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
v___x_3378_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3377_, v_a_3352_);
lean_dec(v_pos_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3379_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
return v___x_3379_;
}
else
{
lean_object* v_parserState_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v___f_3359_);
lean_dec_ref(v___f_3358_);
v_parserState_3380_ = lean_ctor_get(v_val_3363_, 0);
lean_inc_ref(v_parserState_3380_);
lean_inc_ref(v_toProcessingContext_3354_);
v___x_3381_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3354_, v_a_3352_, v_val_3360_, v_stx_3362_, v_parserState_3380_, v_a_3352_);
return v___x_3381_;
}
}
else
{
lean_object* v___x_3382_; 
lean_dec(v___x_3374_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3382_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
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
v___x_3383_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
return v___x_3383_;
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v_val_3366_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3384_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
return v___x_3384_;
}
}
else
{
lean_object* v___x_3385_; 
lean_dec(v___x_3365_);
lean_dec(v_stx_3362_);
lean_dec(v_val_3360_);
v___x_3385_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
return v___x_3385_;
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v_val_3360_);
v___x_3386_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
return v___x_3386_;
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v_old_x3f_3351_);
v___x_3387_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3359_, v___f_3358_, v_a_3352_);
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
v___x_3430_ = lean_box(0);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3475_, lean_object* v_snap_3476_, lean_object* v_acc_3477_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3478_; lean_object* v_acc_3479_; 
v_nextCmdSnap_x3f_3478_ = lean_ctor_get(v_snap_3476_, 4);
lean_inc(v_nextCmdSnap_x3f_3478_);
lean_inc(v_f_3475_);
v_acc_3479_ = lean_apply_2(v_f_3475_, v_acc_3477_, v_snap_3476_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3478_) == 1)
{
lean_object* v_val_3480_; lean_object* v___x_3481_; 
v_val_3480_ = lean_ctor_get(v_nextCmdSnap_x3f_3478_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3478_, 1);
v___x_3481_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3480_);
v_snap_3476_ = v___x_3481_;
v_acc_3477_ = v_acc_3479_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3478_);
lean_dec(v_f_3475_);
return v_acc_3479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3483_, lean_object* v_f_3484_, lean_object* v_snap_3485_, lean_object* v_acc_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3484_, v_snap_3485_, v_acc_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3488_, lean_object* v_init_3489_, lean_object* v_f_3490_){
_start:
{
lean_object* v_result_x3f_3491_; 
v_result_x3f_3491_ = lean_ctor_get(v_snap_3488_, 4);
lean_inc(v_result_x3f_3491_);
lean_dec_ref(v_snap_3488_);
if (lean_obj_tag(v_result_x3f_3491_) == 0)
{
lean_object* v___x_3492_; 
lean_dec(v_f_3490_);
lean_dec(v_init_3489_);
v___x_3492_ = lean_box(0);
return v___x_3492_;
}
else
{
lean_object* v_val_3493_; lean_object* v_processedSnap_3494_; lean_object* v___x_3495_; lean_object* v_result_x3f_3496_; 
v_val_3493_ = lean_ctor_get(v_result_x3f_3491_, 0);
lean_inc(v_val_3493_);
lean_dec_ref_known(v_result_x3f_3491_, 1);
v_processedSnap_3494_ = lean_ctor_get(v_val_3493_, 1);
lean_inc_ref(v_processedSnap_3494_);
lean_dec(v_val_3493_);
v___x_3495_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3494_);
v_result_x3f_3496_ = lean_ctor_get(v___x_3495_, 2);
lean_inc(v_result_x3f_3496_);
lean_dec(v___x_3495_);
if (lean_obj_tag(v_result_x3f_3496_) == 0)
{
lean_object* v___x_3497_; 
lean_dec(v_f_3490_);
lean_dec(v_init_3489_);
v___x_3497_ = lean_box(0);
return v___x_3497_;
}
else
{
lean_object* v_val_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3508_; 
v_val_3498_ = lean_ctor_get(v_result_x3f_3496_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_result_x3f_3496_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3500_ = v_result_x3f_3496_;
v_isShared_3501_ = v_isSharedCheck_3508_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_val_3498_);
lean_dec(v_result_x3f_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3508_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v_firstCmdSnap_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3506_; 
v_firstCmdSnap_3502_ = lean_ctor_get(v_val_3498_, 1);
lean_inc_ref(v_firstCmdSnap_3502_);
lean_dec(v_val_3498_);
v___x_3503_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3502_);
v___x_3504_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3490_, v___x_3503_, v_init_3489_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3504_);
v___x_3506_ = v___x_3500_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3509_, lean_object* v_snap_3510_, lean_object* v_init_3511_, lean_object* v_f_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3510_, v_init_3511_, v_f_3512_);
return v___x_3513_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = 1;
v___x_3520_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3521_ = l_Lean_Name_toString(v___x_3520_, v___x_3519_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3522_ = 0;
v___x_3523_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3524_ = lean_box(0);
v___x_3525_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3526_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3527_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___x_3525_);
lean_ctor_set(v___x_3527_, 2, v___x_3524_);
lean_ctor_set(v___x_3527_, 3, v___x_3523_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*4, v___x_3522_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3529_ = lean_box(0);
v___x_3530_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3529_, v___x_3528_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3531_){
_start:
{
lean_object* v_result_x3f_3532_; 
v_result_x3f_3532_ = lean_ctor_get(v_snap_3531_, 4);
lean_inc(v_result_x3f_3532_);
if (lean_obj_tag(v_result_x3f_3532_) == 1)
{
lean_object* v_val_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3608_; 
v_val_3533_ = lean_ctor_get(v_result_x3f_3532_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_result_x3f_3532_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3535_ = v_result_x3f_3532_;
v_isShared_3536_ = v_isSharedCheck_3608_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_val_3533_);
lean_dec(v_result_x3f_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3608_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_toSnapshot_3537_; lean_object* v_metaSnap_3538_; lean_object* v_ictx_3539_; lean_object* v_stx_3540_; lean_object* v_parserState_3541_; lean_object* v_processedSnap_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3607_; 
v_toSnapshot_3537_ = lean_ctor_get(v_snap_3531_, 0);
v_metaSnap_3538_ = lean_ctor_get(v_snap_3531_, 1);
v_ictx_3539_ = lean_ctor_get(v_snap_3531_, 2);
v_stx_3540_ = lean_ctor_get(v_snap_3531_, 3);
v_parserState_3541_ = lean_ctor_get(v_val_3533_, 0);
v_processedSnap_3542_ = lean_ctor_get(v_val_3533_, 1);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_val_3533_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3544_ = v_val_3533_;
v_isShared_3545_ = v_isSharedCheck_3607_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_processedSnap_3542_);
lean_inc(v_parserState_3541_);
lean_dec(v_val_3533_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3607_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v_processed_3546_; lean_object* v_result_x3f_3547_; 
v_processed_3546_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3542_);
v_result_x3f_3547_ = lean_ctor_get(v_processed_3546_, 2);
lean_inc(v_result_x3f_3547_);
if (lean_obj_tag(v_result_x3f_3547_) == 1)
{
lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3601_; 
lean_inc(v_stx_3540_);
lean_inc_ref(v_ictx_3539_);
lean_inc_ref(v_metaSnap_3538_);
lean_inc_ref(v_toSnapshot_3537_);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_snap_3531_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; 
v_unused_3602_ = lean_ctor_get(v_snap_3531_, 4);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v_snap_3531_, 3);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_snap_3531_, 2);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_snap_3531_, 1);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_snap_3531_, 0);
lean_dec(v_unused_3606_);
v___x_3549_ = v_snap_3531_;
v_isShared_3550_ = v_isSharedCheck_3601_;
goto v_resetjp_3548_;
}
else
{
lean_dec(v_snap_3531_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3601_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v_val_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3600_; 
v_val_3551_ = lean_ctor_get(v_result_x3f_3547_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_result_x3f_3547_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3553_ = v_result_x3f_3547_;
v_isShared_3554_ = v_isSharedCheck_3600_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_val_3551_);
lean_dec(v_result_x3f_3547_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3600_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_toSnapshot_3555_; lean_object* v_metaSnap_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3598_; 
v_toSnapshot_3555_ = lean_ctor_get(v_processed_3546_, 0);
v_metaSnap_3556_ = lean_ctor_get(v_processed_3546_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_processed_3546_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v_processed_3546_, 2);
lean_dec(v_unused_3599_);
v___x_3558_ = v_processed_3546_;
v_isShared_3559_ = v_isSharedCheck_3598_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_metaSnap_3556_);
lean_inc(v_toSnapshot_3555_);
lean_dec(v_processed_3546_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3598_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_cmdState_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3596_; 
v_cmdState_3560_ = lean_ctor_get(v_val_3551_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_val_3551_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v_val_3551_, 1);
lean_dec(v_unused_3597_);
v___x_3562_ = v_val_3551_;
v_isShared_3563_ = v_isSharedCheck_3596_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_cmdState_3560_);
lean_dec(v_val_3551_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3596_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_resultSnap_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_elabSnap_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v_termCmd_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3564_ = lean_box(0);
v___x_3565_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3566_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3560_);
v_resultSnap_3567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3567_, 0, v___x_3565_);
lean_ctor_set(v_resultSnap_3567_, 1, v_cmdState_3560_);
lean_ctor_set(v_resultSnap_3567_, 2, v___x_3566_);
v___x_3568_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3569_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3564_, v_resultSnap_3567_);
v___x_3570_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3571_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3572_, 0, v___x_3565_);
lean_ctor_set(v_elabSnap_3572_, 1, v___x_3568_);
lean_ctor_set(v_elabSnap_3572_, 2, v___x_3569_);
lean_ctor_set(v_elabSnap_3572_, 3, v___x_3570_);
lean_ctor_set(v_elabSnap_3572_, 4, v___x_3571_);
v___x_3573_ = lean_box(0);
v___x_3574_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3575_, 0, v___x_3565_);
lean_ctor_set(v_termCmd_3575_, 1, v___x_3573_);
lean_ctor_set(v_termCmd_3575_, 2, v___x_3574_);
lean_ctor_set(v_termCmd_3575_, 3, v_elabSnap_3572_);
lean_ctor_set(v_termCmd_3575_, 4, v___x_3564_);
v___x_3576_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3564_, v_termCmd_3575_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v___x_3576_);
v___x_3578_ = v___x_3562_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_cmdState_3560_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3580_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3578_);
v___x_3580_ = v___x_3553_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v_newProcessed_3582_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 2, v___x_3580_);
v_newProcessed_3582_ = v___x_3558_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_toSnapshot_3555_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_metaSnap_3556_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v___x_3580_);
v_newProcessed_3582_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3564_, v_newProcessed_3582_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v___x_3583_);
v___x_3585_ = v___x_3544_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_parserState_3541_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3585_);
v___x_3587_ = v___x_3535_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 4, v___x_3587_);
v___x_3589_ = v___x_3549_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_toSnapshot_3537_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_metaSnap_3538_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_ictx_3539_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_stx_3540_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
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
lean_dec(v_result_x3f_3547_);
lean_dec(v_processed_3546_);
lean_del_object(v___x_3544_);
lean_dec_ref(v_parserState_3541_);
lean_del_object(v___x_3535_);
return v_snap_3531_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3532_);
return v_snap_3531_;
}
}
}
lean_object* runtime_initialize_Lean_Language_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Language_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Util(builtin);
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
lean_object* initialize_Lean_Language_Lean_Util(uint8_t builtin);
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
res = initialize_Lean_Language_Lean_Util(builtin);
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

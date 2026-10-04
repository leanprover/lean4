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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_d_326_; 
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_k_329_; lean_object* v_v_330_; lean_object* v_l_331_; lean_object* v_r_332_; lean_object* v___x_333_; 
v_k_329_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_k_329_);
v_v_330_ = lean_ctor_get(v_x_323_, 2);
lean_inc(v_v_330_);
v_l_331_ = lean_ctor_get(v_x_323_, 3);
lean_inc(v_l_331_);
v_r_332_ = lean_ctor_get(v_x_323_, 4);
lean_inc(v_r_332_);
lean_dec_ref_known(v_x_323_, 5);
v___x_333_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_321_, v_init_322_, v_l_331_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
if (lean_obj_tag(v_a_334_) == 0)
{
lean_object* v_a_335_; 
lean_dec_ref_known(v___x_333_, 1);
lean_dec(v_r_332_);
lean_dec(v_v_330_);
lean_dec(v_k_329_);
v_a_335_ = lean_ctor_get(v_a_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v_a_334_, 1);
v_d_326_ = v_a_335_;
goto v___jp_325_;
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_387_; 
v_a_336_ = lean_ctor_get(v_a_334_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_387_ == 0)
{
v___x_338_ = v_a_334_;
v_isShared_339_ = v_isSharedCheck_387_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v_a_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_387_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_340_ = l_Lean_Name_getRoot(v_k_329_);
v___x_341_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1));
v___x_342_ = lean_box(0);
v___x_343_ = l_Lean_Name_replacePrefix(v_k_329_, v___x_341_, v___x_342_);
v___x_344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_321_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_dec(v___x_340_);
lean_del_object(v___x_338_);
lean_dec_ref_known(v___x_333_, 1);
if (lean_obj_tag(v_v_330_) == 0)
{
lean_object* v_val_345_; lean_object* v_v_346_; lean_object* v___x_347_; 
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_344_, 1);
v_v_346_ = lean_ctor_get(v_v_330_, 0);
lean_inc_ref(v_v_346_);
lean_dec_ref_known(v_v_330_, 1);
v___x_347_ = l_Lean_Language_Lean_setOption(v_a_336_, v_val_345_, v___x_343_, v_v_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v_init_322_ = v_a_348_;
v_x_323_ = v_r_332_;
goto _start;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_r_332_);
v_a_350_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_347_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_347_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec_ref_known(v___x_344_, 1);
v___x_358_ = l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(v_a_336_, v___x_343_, v_v_330_);
v_init_322_ = v___x_358_;
v_x_323_ = v_r_332_;
goto _start;
}
}
else
{
uint8_t v___x_360_; 
lean_dec(v___x_344_);
lean_dec(v_a_336_);
lean_dec(v_v_330_);
v___x_360_ = lean_name_eq(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
if (v___x_360_ == 0)
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_r_332_);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v___x_333_, 0);
lean_dec(v_unused_382_);
v___x_362_ = v___x_333_;
v_isShared_363_ = v_isSharedCheck_381_;
goto v_resetjp_361_;
}
else
{
lean_dec(v___x_333_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_381_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_364_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2));
v___x_365_ = 1;
lean_inc(v___x_343_);
v___x_366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_343_, v___x_365_);
v___x_367_ = lean_string_append(v___x_364_, v___x_366_);
lean_dec_ref(v___x_366_);
v___x_368_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3));
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
v___x_370_ = l_Lean_Name_append(v___x_341_, v___x_343_);
v___x_371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_370_, v___x_365_);
v___x_372_ = lean_string_append(v___x_369_, v___x_371_);
lean_dec_ref(v___x_371_);
v___x_373_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4));
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 18);
lean_ctor_set(v___x_338_, 0, v___x_374_);
v___x_376_ = v___x_338_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 1);
lean_ctor_set(v___x_362_, 0, v___x_376_);
v___x_378_ = v___x_362_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_dec(v___x_343_);
lean_del_object(v___x_338_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_333_, 1);
if (lean_obj_tag(v_a_383_) == 0)
{
lean_object* v_a_384_; 
lean_dec(v_r_332_);
v_a_384_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v_a_383_, 1);
v_d_326_ = v_a_384_;
goto v___jp_325_;
}
else
{
lean_object* v_a_385_; 
v_a_385_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v_a_383_, 1);
v_init_322_ = v_a_385_;
v_x_323_ = v_r_332_;
goto _start;
}
}
else
{
lean_dec(v_r_332_);
return v___x_333_;
}
}
}
}
}
}
else
{
lean_dec(v_r_332_);
lean_dec(v_v_330_);
lean_dec(v_k_329_);
return v___x_333_;
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v_init_322_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_d_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object* v_a_390_, lean_object* v_init_391_, lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_390_, v_init_391_, v_x_392_);
lean_dec(v_a_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object* v_opts_395_){
_start:
{
lean_object* v_opts_x27_397_; lean_object* v___x_398_; 
v_opts_x27_397_ = l_Lean_Options_empty;
v___x_398_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v_map_400_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v_map_400_ = lean_ctor_get(v_opts_395_, 0);
lean_inc(v_map_400_);
lean_dec_ref(v_opts_395_);
v___x_401_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_399_, v_opts_x27_397_, v_map_400_);
lean_dec(v_a_399_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_a_406_; lean_object* v___x_408_; 
v_a_406_ = lean_ctor_get(v_a_402_, 0);
lean_inc(v_a_406_);
lean_dec(v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_a_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_a_411_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_401_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_401_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_opts_395_);
v_a_419_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_398_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_398_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object* v_opts_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Language_Lean_reparseOptions(v_opts_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object* v_stx_438_){
_start:
{
lean_object* v_stx_440_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = l_Lean_Syntax_getArg(v_stx_438_, v___x_443_);
v___x_445_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3));
v___x_446_ = l_Lean_Syntax_isOfKind(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
v_stx_440_ = v_stx_438_;
goto v___jp_439_;
}
else
{
lean_object* v___x_447_; lean_object* v_stx_448_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v_stx_448_ = l_Lean_Syntax_getArg(v_stx_438_, v___x_447_);
lean_dec(v_stx_438_);
v_stx_440_ = v_stx_448_;
goto v___jp_439_;
}
v___jp_439_:
{
uint8_t v___x_441_; lean_object* v___x_442_; 
v___x_441_ = 0;
v___x_442_ = l_Lean_Syntax_getPos_x3f(v_stx_440_, v___x_441_);
lean_dec(v_stx_440_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_449_, lean_object* v_decl_450_, lean_object* v_ref_451_){
_start:
{
lean_object* v_defValue_453_; lean_object* v_descr_454_; lean_object* v_deprecation_x3f_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_defValue_453_ = lean_ctor_get(v_decl_450_, 0);
v_descr_454_ = lean_ctor_get(v_decl_450_, 1);
v_deprecation_x3f_455_ = lean_ctor_get(v_decl_450_, 2);
v___x_456_ = lean_alloc_ctor(1, 0, 1);
v___x_457_ = lean_unbox(v_defValue_453_);
lean_ctor_set_uint8(v___x_456_, 0, v___x_457_);
lean_inc(v_deprecation_x3f_455_);
lean_inc_ref(v_descr_454_);
lean_inc_n(v_name_449_, 2);
v___x_458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_458_, 0, v_name_449_);
lean_ctor_set(v___x_458_, 1, v_ref_451_);
lean_ctor_set(v___x_458_, 2, v___x_456_);
lean_ctor_set(v___x_458_, 3, v_descr_454_);
lean_ctor_set(v___x_458_, 4, v_deprecation_x3f_455_);
v___x_459_ = lean_register_option(v_name_449_, v___x_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_459_, 0);
lean_dec(v_unused_468_);
v___x_461_ = v___x_459_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_dec(v___x_459_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_inc(v_defValue_453_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_name_449_);
lean_ctor_set(v___x_463_, 1, v_defValue_453_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_name_449_);
v_a_469_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_459_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_459_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_477_, lean_object* v_decl_478_, lean_object* v_ref_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_477_, v_decl_478_, v_ref_479_);
lean_dec_ref(v_decl_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_500_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_501_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_502_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_499_, v___x_500_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_504_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(32u);
v___x_506_ = lean_mk_empty_array_with_capacity(v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_508_ = ((size_t)5ULL);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_unsigned_to_nat(32u);
v___x_511_ = lean_mk_empty_array_with_capacity(v___x_510_);
v___x_512_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_513_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
lean_ctor_set(v___x_513_, 2, v___x_509_);
lean_ctor_set(v___x_513_, 3, v___x_509_);
lean_ctor_set_usize(v___x_513_, 4, v___x_508_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; lean_object* v_infoState_517_; lean_object* v_trees_518_; lean_object* v___x_519_; lean_object* v_infoState_520_; lean_object* v_env_521_; lean_object* v_messages_522_; lean_object* v_scopes_523_; lean_object* v_usedQuotCtxts_524_; lean_object* v_nextMacroScope_525_; lean_object* v_maxRecDepth_526_; lean_object* v_ngen_527_; lean_object* v_auxDeclNGen_528_; lean_object* v_traceState_529_; lean_object* v_snapshotTasks_530_; lean_object* v_prevLinterStates_531_; lean_object* v_codeQualityEntryTasks_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_553_; 
v___x_516_ = lean_st_ref_get(v___y_514_);
v_infoState_517_ = lean_ctor_get(v___x_516_, 8);
lean_inc_ref(v_infoState_517_);
lean_dec(v___x_516_);
v_trees_518_ = lean_ctor_get(v_infoState_517_, 2);
lean_inc_ref(v_trees_518_);
lean_dec_ref(v_infoState_517_);
v___x_519_ = lean_st_ref_take(v___y_514_);
v_infoState_520_ = lean_ctor_get(v___x_519_, 8);
v_env_521_ = lean_ctor_get(v___x_519_, 0);
v_messages_522_ = lean_ctor_get(v___x_519_, 1);
v_scopes_523_ = lean_ctor_get(v___x_519_, 2);
v_usedQuotCtxts_524_ = lean_ctor_get(v___x_519_, 3);
v_nextMacroScope_525_ = lean_ctor_get(v___x_519_, 4);
v_maxRecDepth_526_ = lean_ctor_get(v___x_519_, 5);
v_ngen_527_ = lean_ctor_get(v___x_519_, 6);
v_auxDeclNGen_528_ = lean_ctor_get(v___x_519_, 7);
v_traceState_529_ = lean_ctor_get(v___x_519_, 9);
v_snapshotTasks_530_ = lean_ctor_get(v___x_519_, 10);
v_prevLinterStates_531_ = lean_ctor_get(v___x_519_, 11);
v_codeQualityEntryTasks_532_ = lean_ctor_get(v___x_519_, 12);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_553_ == 0)
{
v___x_534_ = v___x_519_;
v_isShared_535_ = v_isSharedCheck_553_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_codeQualityEntryTasks_532_);
lean_inc(v_prevLinterStates_531_);
lean_inc(v_snapshotTasks_530_);
lean_inc(v_traceState_529_);
lean_inc(v_infoState_520_);
lean_inc(v_auxDeclNGen_528_);
lean_inc(v_ngen_527_);
lean_inc(v_maxRecDepth_526_);
lean_inc(v_nextMacroScope_525_);
lean_inc(v_usedQuotCtxts_524_);
lean_inc(v_scopes_523_);
lean_inc(v_messages_522_);
lean_inc(v_env_521_);
lean_dec(v___x_519_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_553_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v_enabled_536_; lean_object* v_assignment_537_; lean_object* v_lazyAssignment_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_551_; 
v_enabled_536_ = lean_ctor_get_uint8(v_infoState_520_, sizeof(void*)*3);
v_assignment_537_ = lean_ctor_get(v_infoState_520_, 0);
v_lazyAssignment_538_ = lean_ctor_get(v_infoState_520_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_infoState_520_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_infoState_520_, 2);
lean_dec(v_unused_552_);
v___x_540_ = v_infoState_520_;
v_isShared_541_ = v_isSharedCheck_551_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_lazyAssignment_538_);
lean_inc(v_assignment_537_);
lean_dec(v_infoState_520_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_551_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 2, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_assignment_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_lazyAssignment_538_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___x_542_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*3, v_enabled_536_);
v___x_544_ = v_reuseFailAlloc_550_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 8, v___x_544_);
v___x_546_ = v___x_534_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_env_521_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_messages_522_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_scopes_523_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_usedQuotCtxts_524_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_nextMacroScope_525_);
lean_ctor_set(v_reuseFailAlloc_549_, 5, v_maxRecDepth_526_);
lean_ctor_set(v_reuseFailAlloc_549_, 6, v_ngen_527_);
lean_ctor_set(v_reuseFailAlloc_549_, 7, v_auxDeclNGen_528_);
lean_ctor_set(v_reuseFailAlloc_549_, 8, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_549_, 9, v_traceState_529_);
lean_ctor_set(v_reuseFailAlloc_549_, 10, v_snapshotTasks_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 11, v_prevLinterStates_531_);
lean_ctor_set(v_reuseFailAlloc_549_, 12, v_codeQualityEntryTasks_532_);
v___x_546_ = v_reuseFailAlloc_549_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_st_ref_put(v___y_514_, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_trees_518_);
return v___x_548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_554_);
lean_dec(v___y_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_564_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_565_, lean_object* v_opt_566_){
_start:
{
lean_object* v_name_567_; lean_object* v_defValue_568_; lean_object* v_map_569_; lean_object* v___x_570_; 
v_name_567_ = lean_ctor_get(v_opt_566_, 0);
v_defValue_568_ = lean_ctor_get(v_opt_566_, 1);
v_map_569_ = lean_ctor_get(v_opts_565_, 0);
v___x_570_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_569_, v_name_567_);
if (lean_obj_tag(v___x_570_) == 0)
{
uint8_t v___x_571_; 
v___x_571_ = lean_unbox(v_defValue_568_);
return v___x_571_;
}
else
{
lean_object* v_val_572_; 
v_val_572_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v___x_570_, 1);
if (lean_obj_tag(v_val_572_) == 1)
{
uint8_t v_v_573_; 
v_v_573_ = lean_ctor_get_uint8(v_val_572_, 0);
lean_dec_ref_known(v_val_572_, 0);
return v_v_573_;
}
else
{
uint8_t v___x_574_; 
lean_dec(v_val_572_);
v___x_574_ = lean_unbox(v_defValue_568_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_575_, lean_object* v_opt_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_575_, v_opt_576_);
lean_dec_ref(v_opt_576_);
lean_dec_ref(v_opts_575_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = l_Lean_Language_Snapshot_transform(v_val_581_, v___y_582_);
v___x_584_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_586_, v___y_587_);
lean_dec_ref(v___y_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_589_, lean_object* v_val_590_){
_start:
{
lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_inc_ref(v_val_590_);
v___f_591_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_591_, 0, v_val_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_inst_589_);
lean_ctor_set(v___x_592_, 1, v_val_590_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___f_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_594_, lean_object* v_revCmds_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_597_);
lean_dec_ref(v___x_599_);
lean_inc(v_stx_594_);
v___x_600_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_594_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_612_; 
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_613_);
v___x_602_ = v___x_600_;
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
else
{
lean_dec(v___x_600_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
uint8_t v___x_604_; 
v___x_604_ = l_Lean_Parser_isTerminalCommand(v_stx_594_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_revCmds_595_);
v___x_605_ = lean_box(0);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_602_);
v___x_609_ = l_List_reverse___redArg(v_revCmds_595_);
v___x_610_ = lean_array_mk(v___x_609_);
v___x_611_ = l_Lean_Elab_Command_runModuleLintersAsync(v___x_610_, v___y_596_, v___y_597_);
return v___x_611_;
}
}
}
else
{
lean_dec(v_revCmds_595_);
lean_dec(v_stx_594_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_614_, lean_object* v_revCmds_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_614_, v_revCmds_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_619_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_620_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_ctor_set(v___x_625_, 3, v___x_624_);
lean_ctor_set(v___x_625_, 4, v___x_623_);
lean_ctor_set(v___x_625_, 5, v___x_623_);
lean_ctor_set(v___x_625_, 6, v___x_623_);
lean_ctor_set(v___x_625_, 7, v___x_623_);
lean_ctor_set(v___x_625_, 8, v___x_623_);
lean_ctor_set(v___x_625_, 9, v___x_623_);
lean_ctor_set(v___x_625_, 10, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(32u);
v___x_627_ = lean_mk_empty_array_with_capacity(v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = ((size_t)5ULL);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_unsigned_to_nat(32u);
v___x_632_ = lean_mk_empty_array_with_capacity(v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_634_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_630_);
lean_ctor_set(v___x_634_, 3, v___x_630_);
lean_ctor_set_usize(v___x_634_, 4, v___x_629_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_box(1);
v___x_636_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
lean_ctor_set(v___x_638_, 2, v___x_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; lean_object* v_env_643_; uint8_t v___x_644_; lean_object* v_env_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_scopes_648_; lean_object* v___x_649_; lean_object* v_opts_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_642_ = lean_st_ref_get(v___y_640_);
v_env_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_env_643_);
lean_dec(v___x_642_);
v___x_644_ = 0;
v_env_645_ = l_Lean_Environment_setRecordingDeps(v_env_643_, v___x_644_);
v___x_646_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_647_ = lean_st_ref_get(v___y_640_);
v_scopes_648_ = lean_ctor_get(v___x_647_, 2);
lean_inc(v_scopes_648_);
lean_dec(v___x_647_);
v___x_649_ = l_List_head_x21___redArg(v___x_646_, v_scopes_648_);
lean_dec(v_scopes_648_);
v_opts_650_ = lean_ctor_get(v___x_649_, 1);
lean_inc_ref(v_opts_650_);
lean_dec(v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_653_, 0, v_env_645_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_652_);
lean_ctor_set(v___x_653_, 3, v_opts_650_);
v___x_654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_msgData_639_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_656_, v___y_657_);
lean_dec(v___y_657_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_660_, uint8_t v___y_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 1)
{
lean_object* v_pre_663_; 
v_pre_663_ = lean_ctor_get(v_x_662_, 0);
if (lean_obj_tag(v_pre_663_) == 0)
{
lean_object* v_str_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_str_664_ = lean_ctor_get(v_x_662_, 1);
v___x_665_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_666_ = lean_string_dec_eq(v_str_664_, v___x_665_);
if (v___x_666_ == 0)
{
return v___x_666_;
}
else
{
return v_suppressElabErrors_660_;
}
}
else
{
return v___y_661_;
}
}
else
{
return v___y_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_667_, lean_object* v___y_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_suppressElabErrors_boxed_670_; uint8_t v___y_9369__boxed_671_; uint8_t v_res_672_; lean_object* v_r_673_; 
v_suppressElabErrors_boxed_670_ = lean_unbox(v_suppressElabErrors_667_);
v___y_9369__boxed_671_ = lean_unbox(v___y_668_);
v_res_672_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_670_, v___y_9369__boxed_671_, v_x_669_);
lean_dec(v_x_669_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_675_, lean_object* v_msgData_676_, uint8_t v_severity_677_, uint8_t v_isSilent_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; uint8_t v___y_751_; lean_object* v___y_752_; uint8_t v___y_776_; lean_object* v___y_777_; uint8_t v___y_778_; uint8_t v___y_779_; lean_object* v___y_780_; uint8_t v___y_784_; uint8_t v___y_785_; uint8_t v___y_786_; uint8_t v___x_801_; uint8_t v___y_803_; uint8_t v___y_804_; uint8_t v___y_805_; uint8_t v___y_807_; uint8_t v___x_819_; 
v___x_801_ = 2;
v___x_819_ = l_Lean_instBEqMessageSeverity_beq(v_severity_677_, v___x_801_);
if (v___x_819_ == 0)
{
v___y_807_ = v___x_819_;
goto v___jp_806_;
}
else
{
uint8_t v___x_820_; 
lean_inc_ref(v_msgData_676_);
v___x_820_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_676_);
v___y_807_ = v___x_820_;
goto v___jp_806_;
}
v___jp_682_:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Elab_Command_getScope___redArg(v___y_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v_currNamespace_693_; lean_object* v___x_694_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v_currNamespace_693_ = lean_ctor_get(v_a_692_, 2);
lean_inc(v_currNamespace_693_);
lean_dec(v_a_692_);
v___x_694_ = l_Lean_Elab_Command_getScope___redArg(v___y_690_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_730_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_730_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_730_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_730_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_openDecls_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_env_704_; lean_object* v_messages_705_; lean_object* v_scopes_706_; lean_object* v_usedQuotCtxts_707_; lean_object* v_nextMacroScope_708_; lean_object* v_maxRecDepth_709_; lean_object* v_ngen_710_; lean_object* v_auxDeclNGen_711_; lean_object* v_infoState_712_; lean_object* v_traceState_713_; lean_object* v_snapshotTasks_714_; lean_object* v_prevLinterStates_715_; lean_object* v_codeQualityEntryTasks_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_729_; 
v_openDecls_699_ = lean_ctor_get(v_a_695_, 3);
lean_inc(v_openDecls_699_);
lean_dec(v_a_695_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_currNamespace_693_);
lean_ctor_set(v___x_700_, 1, v_openDecls_699_);
v___x_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___y_689_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_685_);
v___x_702_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_702_, 0, v___y_685_);
lean_ctor_set(v___x_702_, 1, v___y_683_);
lean_ctor_set(v___x_702_, 2, v___y_687_);
lean_ctor_set(v___x_702_, 3, v___y_684_);
lean_ctor_set(v___x_702_, 4, v___x_701_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*5, v___y_688_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*5 + 1, v___y_686_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*5 + 2, v_isSilent_678_);
v___x_703_ = lean_st_ref_take(v___y_690_);
v_env_704_ = lean_ctor_get(v___x_703_, 0);
v_messages_705_ = lean_ctor_get(v___x_703_, 1);
v_scopes_706_ = lean_ctor_get(v___x_703_, 2);
v_usedQuotCtxts_707_ = lean_ctor_get(v___x_703_, 3);
v_nextMacroScope_708_ = lean_ctor_get(v___x_703_, 4);
v_maxRecDepth_709_ = lean_ctor_get(v___x_703_, 5);
v_ngen_710_ = lean_ctor_get(v___x_703_, 6);
v_auxDeclNGen_711_ = lean_ctor_get(v___x_703_, 7);
v_infoState_712_ = lean_ctor_get(v___x_703_, 8);
v_traceState_713_ = lean_ctor_get(v___x_703_, 9);
v_snapshotTasks_714_ = lean_ctor_get(v___x_703_, 10);
v_prevLinterStates_715_ = lean_ctor_get(v___x_703_, 11);
v_codeQualityEntryTasks_716_ = lean_ctor_get(v___x_703_, 12);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_729_ == 0)
{
v___x_718_ = v___x_703_;
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_codeQualityEntryTasks_716_);
lean_inc(v_prevLinterStates_715_);
lean_inc(v_snapshotTasks_714_);
lean_inc(v_traceState_713_);
lean_inc(v_infoState_712_);
lean_inc(v_auxDeclNGen_711_);
lean_inc(v_ngen_710_);
lean_inc(v_maxRecDepth_709_);
lean_inc(v_nextMacroScope_708_);
lean_inc(v_usedQuotCtxts_707_);
lean_inc(v_scopes_706_);
lean_inc(v_messages_705_);
lean_inc(v_env_704_);
lean_dec(v___x_703_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_box(0);
v___x_721_ = l_Lean_MessageLog_add(v___x_702_, v_messages_705_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_env_704_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_scopes_706_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_usedQuotCtxts_707_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_nextMacroScope_708_);
lean_ctor_set(v_reuseFailAlloc_728_, 5, v_maxRecDepth_709_);
lean_ctor_set(v_reuseFailAlloc_728_, 6, v_ngen_710_);
lean_ctor_set(v_reuseFailAlloc_728_, 7, v_auxDeclNGen_711_);
lean_ctor_set(v_reuseFailAlloc_728_, 8, v_infoState_712_);
lean_ctor_set(v_reuseFailAlloc_728_, 9, v_traceState_713_);
lean_ctor_set(v_reuseFailAlloc_728_, 10, v_snapshotTasks_714_);
lean_ctor_set(v_reuseFailAlloc_728_, 11, v_prevLinterStates_715_);
lean_ctor_set(v_reuseFailAlloc_728_, 12, v_codeQualityEntryTasks_716_);
v___x_723_ = v_reuseFailAlloc_728_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_st_ref_put(v___y_690_, v___x_723_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_720_);
v___x_726_ = v___x_697_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_720_);
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
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_currNamespace_693_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_683_);
v_a_731_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_694_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_694_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___y_689_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_683_);
v_a_739_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_691_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_691_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
v___jp_747_:
{
lean_object* v_fileName_753_; lean_object* v_fileMap_754_; uint8_t v_suppressElabErrors_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_774_; 
v_fileName_753_ = lean_ctor_get(v___y_679_, 0);
v_fileMap_754_ = lean_ctor_get(v___y_679_, 1);
v_suppressElabErrors_755_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*10);
v___x_756_ = lean_box(v_suppressElabErrors_755_);
v___x_757_ = lean_box(v___y_748_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_758_, 0, v___x_756_);
lean_closure_set(v___f_758_, 1, v___x_757_);
v___x_759_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_676_);
v___x_760_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_759_, v___y_680_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_774_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_774_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_774_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc_ref_n(v_fileMap_754_, 2);
v___x_765_ = l_Lean_FileMap_toPosition(v_fileMap_754_, v___y_749_);
lean_dec(v___y_749_);
v___x_766_ = l_Lean_FileMap_toPosition(v_fileMap_754_, v___y_752_);
lean_dec(v___y_752_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_755_ == 0)
{
lean_del_object(v___x_763_);
lean_dec_ref(v___f_758_);
v___y_683_ = v___x_765_;
v___y_684_ = v___x_768_;
v___y_685_ = v_fileName_753_;
v___y_686_ = v___y_750_;
v___y_687_ = v___x_767_;
v___y_688_ = v___y_751_;
v___y_689_ = v_a_761_;
v___y_690_ = v___y_680_;
goto v___jp_682_;
}
else
{
uint8_t v___x_769_; 
lean_inc(v_a_761_);
v___x_769_ = l_Lean_MessageData_hasTag(v___f_758_, v_a_761_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec_ref_known(v___x_767_, 1);
lean_dec_ref(v___x_765_);
lean_dec(v_a_761_);
v___x_770_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_770_);
v___x_772_ = v___x_763_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_del_object(v___x_763_);
v___y_683_ = v___x_765_;
v___y_684_ = v___x_768_;
v___y_685_ = v_fileName_753_;
v___y_686_ = v___y_750_;
v___y_687_ = v___x_767_;
v___y_688_ = v___y_751_;
v___y_689_ = v_a_761_;
v___y_690_ = v___y_680_;
goto v___jp_682_;
}
}
}
}
v___jp_775_:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Syntax_getTailPos_x3f(v___y_777_, v___y_779_);
lean_dec(v___y_777_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_inc(v___y_780_);
v___y_748_ = v___y_776_;
v___y_749_ = v___y_780_;
v___y_750_ = v___y_778_;
v___y_751_ = v___y_779_;
v___y_752_ = v___y_780_;
goto v___jp_747_;
}
else
{
lean_object* v_val_782_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_781_, 1);
v___y_748_ = v___y_776_;
v___y_749_ = v___y_780_;
v___y_750_ = v___y_778_;
v___y_751_ = v___y_779_;
v___y_752_ = v_val_782_;
goto v___jp_747_;
}
}
v___jp_783_:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Elab_Command_getRef___redArg(v___y_679_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v_ref_789_; lean_object* v___x_790_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v_ref_789_ = l_Lean_replaceRef(v_ref_675_, v_a_788_);
lean_dec(v_a_788_);
v___x_790_ = l_Lean_Syntax_getPos_x3f(v_ref_789_, v___y_785_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___y_776_ = v___y_784_;
v___y_777_ = v_ref_789_;
v___y_778_ = v___y_786_;
v___y_779_ = v___y_785_;
v___y_780_ = v___x_791_;
goto v___jp_775_;
}
else
{
lean_object* v_val_792_; 
v_val_792_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_val_792_);
lean_dec_ref_known(v___x_790_, 1);
v___y_776_ = v___y_784_;
v___y_777_ = v_ref_789_;
v___y_778_ = v___y_786_;
v___y_779_ = v___y_785_;
v___y_780_ = v_val_792_;
goto v___jp_775_;
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_msgData_676_);
v_a_793_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_787_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_787_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
v___jp_802_:
{
if (v___y_805_ == 0)
{
v___y_784_ = v___y_803_;
v___y_785_ = v___y_804_;
v___y_786_ = v_severity_677_;
goto v___jp_783_;
}
else
{
v___y_784_ = v___y_803_;
v___y_785_ = v___y_804_;
v___y_786_ = v___x_801_;
goto v___jp_783_;
}
}
v___jp_806_:
{
if (v___y_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_scopes_810_; lean_object* v___x_811_; lean_object* v_opts_812_; uint8_t v___x_813_; uint8_t v___x_814_; 
v___x_808_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_809_ = lean_st_ref_get(v___y_680_);
v_scopes_810_ = lean_ctor_get(v___x_809_, 2);
lean_inc(v_scopes_810_);
lean_dec(v___x_809_);
v___x_811_ = l_List_head_x21___redArg(v___x_808_, v_scopes_810_);
lean_dec(v_scopes_810_);
v_opts_812_ = lean_ctor_get(v___x_811_, 1);
lean_inc_ref(v_opts_812_);
lean_dec(v___x_811_);
v___x_813_ = 1;
v___x_814_ = l_Lean_instBEqMessageSeverity_beq(v_severity_677_, v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v_opts_812_);
v___y_803_ = v___y_807_;
v___y_804_ = v___y_807_;
v___y_805_ = v___x_814_;
goto v___jp_802_;
}
else
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = l_Lean_warningAsError;
v___x_816_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_812_, v___x_815_);
lean_dec_ref(v_opts_812_);
v___y_803_ = v___y_807_;
v___y_804_ = v___y_807_;
v___y_805_ = v___x_816_;
goto v___jp_802_;
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec_ref(v_msgData_676_);
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_821_, lean_object* v_msgData_822_, lean_object* v_severity_823_, lean_object* v_isSilent_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v_severity_boxed_828_; uint8_t v_isSilent_boxed_829_; lean_object* v_res_830_; 
v_severity_boxed_828_ = lean_unbox(v_severity_823_);
v_isSilent_boxed_829_ = lean_unbox(v_isSilent_824_);
v_res_830_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_821_, v_msgData_822_, v_severity_boxed_828_, v_isSilent_boxed_829_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_ref_821_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_831_, uint8_t v_severity_832_, uint8_t v_isSilent_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Elab_Command_getRef___redArg(v___y_834_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_838_, v_msgData_831_, v_severity_832_, v_isSilent_833_, v___y_834_, v___y_835_);
lean_dec(v_a_838_);
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_msgData_831_);
v_a_840_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_837_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_848_, lean_object* v_severity_849_, lean_object* v_isSilent_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v_severity_boxed_854_; uint8_t v_isSilent_boxed_855_; lean_object* v_res_856_; 
v_severity_boxed_854_ = lean_unbox(v_severity_849_);
v_isSilent_boxed_855_ = lean_unbox(v_isSilent_850_);
v_res_856_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_848_, v_severity_boxed_854_, v_isSilent_boxed_855_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = 2;
v___x_862_ = 0;
v___x_863_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_857_, v___x_861_, v___x_862_, v___y_858_, v___y_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_869_, lean_object* v_msgData_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = 2;
v___x_875_ = 0;
v___x_876_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_869_, v_msgData_870_, v___x_874_, v___x_875_, v___y_871_, v___y_872_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_877_, lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_877_, v_msgData_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_ref_877_);
return v_res_882_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
if (lean_obj_tag(v_ex_886_) == 0)
{
lean_object* v_ref_890_; lean_object* v_msg_891_; lean_object* v___x_892_; 
v_ref_890_ = lean_ctor_get(v_ex_886_, 0);
lean_inc(v_ref_890_);
v_msg_891_ = lean_ctor_get(v_ex_886_, 1);
lean_inc_ref(v_msg_891_);
lean_dec_ref_known(v_ex_886_, 2);
v___x_892_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_890_, v_msg_891_, v___y_887_, v___y_888_);
lean_dec(v_ref_890_);
return v___x_892_;
}
else
{
lean_object* v_id_893_; uint8_t v___y_895_; uint8_t v___x_917_; 
v_id_893_ = lean_ctor_get(v_ex_886_, 0);
lean_inc(v_id_893_);
v___x_917_ = l_Lean_Elab_isAbortExceptionId(v_id_893_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_Exception_isInterrupt(v_ex_886_);
lean_dec_ref_known(v_ex_886_, 2);
v___y_895_ = v___x_918_;
goto v___jp_894_;
}
else
{
lean_dec_ref_known(v_ex_886_, 2);
v___y_895_ = v___x_917_;
goto v___jp_894_;
}
v___jp_894_:
{
if (v___y_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_InternalExceptionId_getName(v_id_893_);
lean_dec(v_id_893_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_899_ = l_Lean_MessageData_ofName(v_a_897_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_900_, v___y_887_, v___y_888_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_914_; 
v_a_902_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_914_ == 0)
{
v___x_904_ = v___x_896_;
v_isShared_905_ = v_isSharedCheck_914_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_896_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_914_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v_ref_906_ = lean_ctor_get(v___y_887_, 7);
v___x_907_ = lean_io_error_to_string(v_a_902_);
v___x_908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___x_909_ = l_Lean_MessageData_ofFormat(v___x_908_);
lean_inc(v_ref_906_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_ref_906_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_910_);
v___x_912_ = v___x_904_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec(v_id_893_);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
v___x_928_ = lean_apply_3(v_x_924_, v___y_925_, v___y_926_, lean_box(0));
if (lean_obj_tag(v___x_928_) == 0)
{
return v___x_928_;
}
else
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
v___x_930_ = l_Lean_Exception_isInterrupt(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec_ref_known(v___x_928_, 1);
v___x_931_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_929_, v___y_925_, v___y_926_);
return v___x_931_;
}
else
{
lean_dec(v_a_929_);
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_937_, lean_object* v___x_938_, lean_object* v_val_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_a_943_; lean_object* v___x_945_; 
v___x_945_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_937_, v___x_938_, v_val_939_);
if (lean_obj_tag(v___x_945_) == 0)
{
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_945_, 1);
v_a_943_ = v_a_946_;
goto v___jp_942_;
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_945_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_object* v___x_955_; 
lean_dec_ref_known(v___x_945_, 1);
v___x_955_ = lean_box(0);
v_a_943_ = v___x_955_;
goto v___jp_942_;
}
v___jp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_a_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_956_, lean_object* v___x_957_, lean_object* v_val_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_956_, v___x_957_, v_val_958_, v___y_959_);
lean_dec_ref(v___y_959_);
lean_dec(v_val_958_);
lean_dec_ref(v___x_957_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_962_, lean_object* v_x_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_get_set_stderr(v_h_962_);
lean_inc_ref(v___y_964_);
v___x_967_ = lean_apply_2(v_x_963_, v___y_964_, lean_box(0));
v___x_968_ = lean_get_set_stderr(v___x_966_);
lean_dec_ref(v___x_968_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_969_, lean_object* v_x_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_969_, v_x_970_, v___y_971_);
lean_dec_ref(v___y_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_974_, lean_object* v_h_975_, lean_object* v_x_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_975_, v_x_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_980_, lean_object* v_h_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_980_, v_h_981_, v_x_982_, v___y_983_);
lean_dec_ref(v___y_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_986_, lean_object* v_x_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_get_set_stdin(v_h_986_);
lean_inc_ref(v___y_988_);
v___x_991_ = lean_apply_2(v_x_987_, v___y_988_, lean_box(0));
v___x_992_ = lean_get_set_stdin(v___x_990_);
lean_dec_ref(v___x_992_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_993_, v_x_994_, v___y_995_);
lean_dec_ref(v___y_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1000_ = lean_panic_fn_borrowed(v___x_999_, v_msg_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_get_set_stdout(v_h_1001_);
lean_inc_ref(v___y_1003_);
v___x_1006_ = lean_apply_2(v_x_1002_, v___y_1003_, lean_box(0));
v___x_1007_ = lean_get_set_stdout(v___x_1005_);
lean_dec_ref(v___x_1007_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1008_, v_x_1009_, v___y_1010_);
lean_dec_ref(v___y_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_1013_, lean_object* v_h_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1014_, v_x_1015_, v___y_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1019_, lean_object* v_h_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1019_, v_h_1020_, v_x_1021_, v___y_1022_);
lean_dec_ref(v___y_1022_);
return v_res_1024_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_ByteArray_empty;
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1031_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1032_ = lean_unsigned_to_nat(46u);
v___x_1033_ = lean_unsigned_to_nat(193u);
v___x_1034_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1035_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1036_ = l_mkPanicMessageWithDecl(v___x_1035_, v___x_1034_, v___x_1033_, v___x_1032_, v___x_1031_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1037_, uint8_t v_isolateStderr_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___y_1051_; 
v___x_1045_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1046_ = lean_st_mk_ref(v___x_1045_);
v___x_1047_ = lean_st_mk_ref(v___x_1045_);
v___x_1048_ = l_IO_FS_Stream_ofBuffer(v___x_1046_);
lean_inc(v___x_1047_);
v___x_1049_ = l_IO_FS_Stream_ofBuffer(v___x_1047_);
if (v_isolateStderr_1038_ == 0)
{
v___y_1051_ = v_x_1037_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1060_; 
lean_inc_ref(v___x_1049_);
v___x_1060_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1060_, 0, lean_box(0));
lean_closure_set(v___x_1060_, 1, v___x_1049_);
lean_closure_set(v___x_1060_, 2, v_x_1037_);
v___y_1051_ = v___x_1060_;
goto v___jp_1050_;
}
v___jp_1041_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___y_1043_);
lean_ctor_set(v___x_1044_, 1, v___y_1042_);
return v___x_1044_;
}
v___jp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_data_1055_; uint8_t v___x_1056_; 
v___x_1052_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1052_, 0, lean_box(0));
lean_closure_set(v___x_1052_, 1, v___x_1049_);
lean_closure_set(v___x_1052_, 2, v___y_1051_);
v___x_1053_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1048_, v___x_1052_, v___y_1039_);
v___x_1054_ = lean_st_ref_get(v___x_1047_);
lean_dec(v___x_1047_);
v_data_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_ref(v_data_1055_);
lean_dec(v___x_1054_);
v___x_1056_ = lean_string_validate_utf8(v_data_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v_data_1055_);
v___x_1057_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1058_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1057_);
v___y_1042_ = v___x_1053_;
v___y_1043_ = v___x_1058_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_string_from_utf8_unchecked(v_data_1055_);
v___y_1042_ = v___x_1053_;
v___y_1043_ = v___x_1059_;
goto v___jp_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1061_, lean_object* v_isolateStderr_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v_isolateStderr_boxed_1065_; lean_object* v_res_1066_; 
v_isolateStderr_boxed_1065_ = lean_unbox(v_isolateStderr_1062_);
v_res_1066_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1061_, v_isolateStderr_boxed_1065_, v___y_1063_);
lean_dec_ref(v___y_1063_);
return v_res_1066_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = 1;
v___x_1076_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1077_ = l_Lean_Name_toString(v___x_1076_, v___x_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1078_, lean_object* v_revCmds_1079_, lean_object* v_cmdState_1080_, lean_object* v_beginPos_1081_, lean_object* v_snap_1082_, lean_object* v_cancelTk_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_env_1086_; lean_object* v_scopes_1087_; lean_object* v_usedQuotCtxts_1088_; lean_object* v_nextMacroScope_1089_; lean_object* v_maxRecDepth_1090_; lean_object* v_ngen_1091_; lean_object* v_auxDeclNGen_1092_; lean_object* v_infoState_1093_; lean_object* v_prevLinterStates_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1176_; 
v_env_1086_ = lean_ctor_get(v_cmdState_1080_, 0);
v_scopes_1087_ = lean_ctor_get(v_cmdState_1080_, 2);
v_usedQuotCtxts_1088_ = lean_ctor_get(v_cmdState_1080_, 3);
v_nextMacroScope_1089_ = lean_ctor_get(v_cmdState_1080_, 4);
v_maxRecDepth_1090_ = lean_ctor_get(v_cmdState_1080_, 5);
v_ngen_1091_ = lean_ctor_get(v_cmdState_1080_, 6);
v_auxDeclNGen_1092_ = lean_ctor_get(v_cmdState_1080_, 7);
v_infoState_1093_ = lean_ctor_get(v_cmdState_1080_, 8);
v_prevLinterStates_1094_ = lean_ctor_get(v_cmdState_1080_, 11);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_cmdState_1080_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1177_ = lean_ctor_get(v_cmdState_1080_, 12);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_cmdState_1080_, 10);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_cmdState_1080_, 9);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_cmdState_1080_, 1);
lean_dec(v_unused_1180_);
v___x_1096_ = v_cmdState_1080_;
v_isShared_1097_ = v_isSharedCheck_1176_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_prevLinterStates_1094_);
lean_inc(v_infoState_1093_);
lean_inc(v_auxDeclNGen_1092_);
lean_inc(v_ngen_1091_);
lean_inc(v_maxRecDepth_1090_);
lean_inc(v_nextMacroScope_1089_);
lean_inc(v_usedQuotCtxts_1088_);
lean_inc(v_scopes_1087_);
lean_inc(v_env_1086_);
lean_dec(v_cmdState_1080_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1176_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___f_1098_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1098_, 0, v_stx_1078_);
lean_closure_set(v___f_1098_, 1, v_revCmds_1079_);
v___x_1099_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1100_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1101_ = l_List_head_x21___redArg(v___x_1099_, v_scopes_1087_);
v___x_1102_ = l_Lean_MessageLog_empty;
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1105_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 12, v___x_1105_);
lean_ctor_set(v___x_1096_, 10, v___x_1105_);
lean_ctor_set(v___x_1096_, 9, v___x_1104_);
lean_ctor_set(v___x_1096_, 1, v___x_1102_);
v___x_1107_ = v___x_1096_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_env_1086_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_scopes_1087_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_usedQuotCtxts_1088_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_nextMacroScope_1089_);
lean_ctor_set(v_reuseFailAlloc_1175_, 5, v_maxRecDepth_1090_);
lean_ctor_set(v_reuseFailAlloc_1175_, 6, v_ngen_1091_);
lean_ctor_set(v_reuseFailAlloc_1175_, 7, v_auxDeclNGen_1092_);
lean_ctor_set(v_reuseFailAlloc_1175_, 8, v_infoState_1093_);
lean_ctor_set(v_reuseFailAlloc_1175_, 9, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1175_, 10, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1175_, 11, v_prevLinterStates_1094_);
lean_ctor_set(v_reuseFailAlloc_1175_, 12, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v_toProcessingContext_1109_; lean_object* v_fileName_1110_; lean_object* v_fileMap_1111_; lean_object* v_opts_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; uint8_t v___y_1120_; lean_object* v_env_1121_; lean_object* v_scopes_1122_; lean_object* v_usedQuotCtxts_1123_; lean_object* v_nextMacroScope_1124_; lean_object* v_maxRecDepth_1125_; lean_object* v_ngen_1126_; lean_object* v_auxDeclNGen_1127_; lean_object* v_infoState_1128_; lean_object* v_traceState_1129_; lean_object* v_snapshotTasks_1130_; lean_object* v_prevLinterStates_1131_; lean_object* v_codeQualityEntryTasks_1132_; lean_object* v_messages_1133_; lean_object* v___y_1142_; 
v___x_1108_ = lean_st_mk_ref(v___x_1107_);
v_toProcessingContext_1109_ = lean_ctor_get(v_a_1084_, 0);
v_fileName_1110_ = lean_ctor_get(v_toProcessingContext_1109_, 1);
v_fileMap_1111_ = lean_ctor_get(v_toProcessingContext_1109_, 2);
v_opts_1112_ = lean_ctor_get(v___x_1101_, 1);
lean_inc_ref(v_opts_1112_);
lean_dec(v___x_1101_);
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Lean_firstFrontendMacroScope;
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Lean_internal_cmdlineSnapshots;
v___x_1118_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1112_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1174_; 
lean_inc_ref(v_snap_1082_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_snap_1082_);
v___y_1142_ = v___x_1174_;
goto v___jp_1141_;
}
else
{
v___y_1142_ = v___x_1114_;
goto v___jp_1141_;
}
v___jp_1119_:
{
lean_object* v_new_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_new_1134_ = lean_ctor_get(v_snap_1082_, 1);
lean_inc(v_new_1134_);
lean_dec_ref(v_snap_1082_);
v___x_1135_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1135_, 0, v_env_1121_);
lean_ctor_set(v___x_1135_, 1, v_messages_1133_);
lean_ctor_set(v___x_1135_, 2, v_scopes_1122_);
lean_ctor_set(v___x_1135_, 3, v_usedQuotCtxts_1123_);
lean_ctor_set(v___x_1135_, 4, v_nextMacroScope_1124_);
lean_ctor_set(v___x_1135_, 5, v_maxRecDepth_1125_);
lean_ctor_set(v___x_1135_, 6, v_ngen_1126_);
lean_ctor_set(v___x_1135_, 7, v_auxDeclNGen_1127_);
lean_ctor_set(v___x_1135_, 8, v_infoState_1128_);
lean_ctor_set(v___x_1135_, 9, v_traceState_1129_);
lean_ctor_set(v___x_1135_, 10, v_snapshotTasks_1130_);
lean_ctor_set(v___x_1135_, 11, v_prevLinterStates_1131_);
lean_ctor_set(v___x_1135_, 12, v_codeQualityEntryTasks_1132_);
v___x_1136_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1137_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1138_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
lean_ctor_set(v___x_1138_, 2, v___x_1114_);
lean_ctor_set(v___x_1138_, 3, v___x_1104_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*4, v___y_1120_);
v___x_1139_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1100_, v___x_1138_);
v___x_1140_ = lean_io_promise_resolve(v___x_1139_, v_new_1134_);
lean_dec(v_new_1134_);
return v___x_1135_;
}
v___jp_1141_:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v___x_1151_; lean_object* v_env_1152_; lean_object* v_messages_1153_; lean_object* v_scopes_1154_; lean_object* v_usedQuotCtxts_1155_; lean_object* v_nextMacroScope_1156_; lean_object* v_maxRecDepth_1157_; lean_object* v_ngen_1158_; lean_object* v_auxDeclNGen_1159_; lean_object* v_infoState_1160_; lean_object* v_traceState_1161_; lean_object* v_snapshotTasks_1162_; lean_object* v_prevLinterStates_1163_; lean_object* v_codeQualityEntryTasks_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_cancelTk_1083_);
v___x_1144_ = 0;
lean_inc(v_beginPos_1081_);
lean_inc_ref(v_fileMap_1111_);
lean_inc_ref(v_fileName_1110_);
v___x_1145_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1145_, 0, v_fileName_1110_);
lean_ctor_set(v___x_1145_, 1, v_fileMap_1111_);
lean_ctor_set(v___x_1145_, 2, v___x_1103_);
lean_ctor_set(v___x_1145_, 3, v_beginPos_1081_);
lean_ctor_set(v___x_1145_, 4, v___x_1113_);
lean_ctor_set(v___x_1145_, 5, v___x_1114_);
lean_ctor_set(v___x_1145_, 6, v___x_1115_);
lean_ctor_set(v___x_1145_, 7, v___x_1116_);
lean_ctor_set(v___x_1145_, 8, v___y_1142_);
lean_ctor_set(v___x_1145_, 9, v___x_1143_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*10, v___x_1144_);
lean_inc(v___x_1108_);
v___f_1146_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1146_, 0, v___f_1098_);
lean_closure_set(v___f_1146_, 1, v___x_1145_);
lean_closure_set(v___f_1146_, 2, v___x_1108_);
v___x_1147_ = l_Lean_Core_stderrAsMessages;
v___x_1148_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1112_, v___x_1147_);
lean_dec_ref(v_opts_1112_);
v___x_1149_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1146_, v___x_1148_, v_a_1084_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_fst_1150_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = lean_st_ref_get(v___x_1108_);
lean_dec(v___x_1108_);
v_env_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_ref(v_env_1152_);
v_messages_1153_ = lean_ctor_get(v___x_1151_, 1);
lean_inc_ref(v_messages_1153_);
v_scopes_1154_ = lean_ctor_get(v___x_1151_, 2);
lean_inc(v_scopes_1154_);
v_usedQuotCtxts_1155_ = lean_ctor_get(v___x_1151_, 3);
lean_inc(v_usedQuotCtxts_1155_);
v_nextMacroScope_1156_ = lean_ctor_get(v___x_1151_, 4);
lean_inc(v_nextMacroScope_1156_);
v_maxRecDepth_1157_ = lean_ctor_get(v___x_1151_, 5);
lean_inc(v_maxRecDepth_1157_);
v_ngen_1158_ = lean_ctor_get(v___x_1151_, 6);
lean_inc_ref(v_ngen_1158_);
v_auxDeclNGen_1159_ = lean_ctor_get(v___x_1151_, 7);
lean_inc_ref(v_auxDeclNGen_1159_);
v_infoState_1160_ = lean_ctor_get(v___x_1151_, 8);
lean_inc_ref(v_infoState_1160_);
v_traceState_1161_ = lean_ctor_get(v___x_1151_, 9);
lean_inc_ref(v_traceState_1161_);
v_snapshotTasks_1162_ = lean_ctor_get(v___x_1151_, 10);
lean_inc_ref(v_snapshotTasks_1162_);
v_prevLinterStates_1163_ = lean_ctor_get(v___x_1151_, 11);
lean_inc(v_prevLinterStates_1163_);
v_codeQualityEntryTasks_1164_ = lean_ctor_get(v___x_1151_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1164_);
lean_dec(v___x_1151_);
v___x_1165_ = lean_string_utf8_byte_size(v_fst_1150_);
v___x_1166_ = lean_nat_dec_eq(v___x_1165_, v___x_1103_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_fileMap_1111_);
v___x_1167_ = l_Lean_FileMap_toPosition(v_fileMap_1111_, v_beginPos_1081_);
lean_dec(v_beginPos_1081_);
v___x_1168_ = 0;
v___x_1169_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_fst_1150_);
v___x_1171_ = l_Lean_MessageData_ofFormat(v___x_1170_);
lean_inc_ref(v_fileName_1110_);
v___x_1172_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1172_, 0, v_fileName_1110_);
lean_ctor_set(v___x_1172_, 1, v___x_1167_);
lean_ctor_set(v___x_1172_, 2, v___x_1114_);
lean_ctor_set(v___x_1172_, 3, v___x_1169_);
lean_ctor_set(v___x_1172_, 4, v___x_1171_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*5, v___x_1144_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*5 + 1, v___x_1168_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*5 + 2, v___x_1144_);
v___x_1173_ = l_Lean_MessageLog_add(v___x_1172_, v_messages_1153_);
v___y_1120_ = v___x_1144_;
v_env_1121_ = v_env_1152_;
v_scopes_1122_ = v_scopes_1154_;
v_usedQuotCtxts_1123_ = v_usedQuotCtxts_1155_;
v_nextMacroScope_1124_ = v_nextMacroScope_1156_;
v_maxRecDepth_1125_ = v_maxRecDepth_1157_;
v_ngen_1126_ = v_ngen_1158_;
v_auxDeclNGen_1127_ = v_auxDeclNGen_1159_;
v_infoState_1128_ = v_infoState_1160_;
v_traceState_1129_ = v_traceState_1161_;
v_snapshotTasks_1130_ = v_snapshotTasks_1162_;
v_prevLinterStates_1131_ = v_prevLinterStates_1163_;
v_codeQualityEntryTasks_1132_ = v_codeQualityEntryTasks_1164_;
v_messages_1133_ = v___x_1173_;
goto v___jp_1119_;
}
else
{
lean_dec(v_fst_1150_);
lean_dec(v_beginPos_1081_);
v___y_1120_ = v___x_1144_;
v_env_1121_ = v_env_1152_;
v_scopes_1122_ = v_scopes_1154_;
v_usedQuotCtxts_1123_ = v_usedQuotCtxts_1155_;
v_nextMacroScope_1124_ = v_nextMacroScope_1156_;
v_maxRecDepth_1125_ = v_maxRecDepth_1157_;
v_ngen_1126_ = v_ngen_1158_;
v_auxDeclNGen_1127_ = v_auxDeclNGen_1159_;
v_infoState_1128_ = v_infoState_1160_;
v_traceState_1129_ = v_traceState_1161_;
v_snapshotTasks_1130_ = v_snapshotTasks_1162_;
v_prevLinterStates_1131_ = v_prevLinterStates_1163_;
v_codeQualityEntryTasks_1132_ = v_codeQualityEntryTasks_1164_;
v_messages_1133_ = v_messages_1153_;
goto v___jp_1119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1181_, lean_object* v_revCmds_1182_, lean_object* v_cmdState_1183_, lean_object* v_beginPos_1184_, lean_object* v_snap_1185_, lean_object* v_cancelTk_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1181_, v_revCmds_1182_, v_cmdState_1183_, v_beginPos_1184_, v_snap_1185_, v_cancelTk_1186_, v_a_1187_);
lean_dec_ref(v_a_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1190_, lean_object* v_h_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1191_, v_x_1192_, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1196_, lean_object* v_h_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1196_, v_h_1197_, v_x_1198_, v___y_1199_);
lean_dec_ref(v___y_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1202_, lean_object* v_x_1203_, uint8_t v_isolateStderr_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1203_, v_isolateStderr_1204_, v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_x_1209_, lean_object* v_isolateStderr_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v_isolateStderr_boxed_1213_; lean_object* v_res_1214_; 
v_isolateStderr_boxed_1213_ = lean_unbox(v_isolateStderr_1210_);
v_res_1214_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1208_, v_x_1209_, v_isolateStderr_boxed_1213_, v___y_1211_);
lean_dec_ref(v___y_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1215_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1225_){
_start:
{
lean_object* v_toSnapshotTreeM_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_toSnapshotTreeM_1226_ = lean_ctor_get(v_a_1225_, 1);
lean_inc_ref(v_toSnapshotTreeM_1226_);
lean_dec_ref(v_a_1225_);
v___x_1227_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1228_ = lean_apply_1(v_toSnapshotTreeM_1226_, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1229_){
_start:
{
lean_object* v_toSnapshot_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_toSnapshot_1230_ = lean_ctor_get(v_a_1229_, 0);
lean_inc_ref(v_toSnapshot_1230_);
lean_dec_ref(v_a_1229_);
v___x_1231_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1232_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1230_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1237_ = l_Lean_Language_Snapshot_transform(v_a_1235_, v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1240_, lean_object* v_opt_1241_){
_start:
{
lean_object* v_name_1242_; lean_object* v_defValue_1243_; lean_object* v_map_1244_; lean_object* v___x_1245_; 
v_name_1242_ = lean_ctor_get(v_opt_1241_, 0);
v_defValue_1243_ = lean_ctor_get(v_opt_1241_, 1);
v_map_1244_ = lean_ctor_get(v_opts_1240_, 0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1244_, v_name_1242_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_inc(v_defValue_1243_);
return v_defValue_1243_;
}
else
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1245_, 1);
if (lean_obj_tag(v_val_1246_) == 3)
{
lean_object* v_v_1247_; 
v_v_1247_ = lean_ctor_get(v_val_1246_, 0);
lean_inc(v_v_1247_);
lean_dec_ref_known(v_val_1246_, 1);
return v_v_1247_;
}
else
{
lean_dec(v_val_1246_);
lean_inc(v_defValue_1243_);
return v_defValue_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1248_, lean_object* v_opt_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1248_, v_opt_1249_);
lean_dec_ref(v_opt_1249_);
lean_dec_ref(v_opts_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1253_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1251_, v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1260_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1261_ = l_Lean_Name_append(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1262_, lean_object* v___x_1263_, uint8_t v_val_1264_, lean_object* v_val_1265_, lean_object* v_val_1266_, lean_object* v___x_1267_, lean_object* v___x_1268_, uint8_t v___x_1269_, lean_object* v_a_1270_, lean_object* v_pos_1271_, lean_object* v___x_1272_, lean_object* v_infoSt_1273_){
_start:
{
lean_object* v___y_1276_; lean_object* v_msgLog_1277_; lean_object* v___y_1283_; lean_object* v_trees_1315_; lean_object* v_size_1316_; uint8_t v___x_1317_; 
v_trees_1315_ = lean_ctor_get(v_infoSt_1273_, 2);
v_size_1316_ = lean_ctor_get(v_trees_1315_, 2);
v___x_1317_ = lean_nat_dec_lt(v___x_1268_, v_size_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = l_outOfBounds___redArg(v___x_1272_);
v___y_1283_ = v___x_1318_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1272_, v_trees_1315_, v___x_1268_);
v___y_1283_ = v___x_1319_;
goto v___jp_1282_;
}
v___jp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1277_);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1276_);
v___x_1280_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1280_, 0, v___x_1262_);
lean_ctor_set(v___x_1280_, 1, v___x_1278_);
lean_ctor_set(v___x_1280_, 2, v___x_1279_);
lean_ctor_set(v___x_1280_, 3, v___x_1263_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*4, v_val_1264_);
v___x_1281_ = lean_io_promise_resolve(v___x_1280_, v_val_1265_);
return v___x_1281_;
}
v___jp_1282_:
{
lean_object* v_scopes_1284_; lean_object* v___x_1285_; lean_object* v_opts_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v_hasTrace_1290_; 
v_scopes_1284_ = lean_ctor_get(v_val_1266_, 2);
v___x_1285_ = l_List_head_x21___redArg(v___x_1267_, v_scopes_1284_);
v_opts_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc_ref(v_opts_1286_);
lean_dec(v___x_1285_);
v___x_1287_ = l_Lean_MessageLog_empty;
v___x_1288_ = l_Lean_inheritedTraceOptions;
v___x_1289_ = lean_st_ref_get(v___x_1288_);
v_hasTrace_1290_ = lean_ctor_get_uint8(v_opts_1286_, sizeof(void*)*1);
if (v_hasTrace_1290_ == 0)
{
lean_dec(v___x_1289_);
lean_dec_ref(v_opts_1286_);
lean_dec(v___x_1268_);
v___y_1276_ = v___y_1283_;
v_msgLog_1277_ = v___x_1287_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1292_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1293_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1294_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1289_, v_opts_1286_, v___x_1293_);
lean_dec_ref(v_opts_1286_);
lean_dec(v___x_1289_);
if (v___x_1294_ == 0)
{
lean_dec(v___x_1268_);
v___y_1276_ = v___y_1283_;
v_msgLog_1277_ = v___x_1287_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_box(0);
lean_inc_ref(v___y_1283_);
v___x_1296_ = l_Lean_Elab_InfoTree_format(v___y_1283_, v___x_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; double v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_toProcessingContext_1301_; lean_object* v_fileName_1302_; lean_object* v_fileMap_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = lean_float_of_nat(v___x_1268_);
v___x_1299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1300_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1300_, 0, v___x_1291_);
lean_ctor_set(v___x_1300_, 1, v___x_1295_);
lean_ctor_set(v___x_1300_, 2, v___x_1299_);
lean_ctor_set_float(v___x_1300_, sizeof(void*)*3, v___x_1298_);
lean_ctor_set_float(v___x_1300_, sizeof(void*)*3 + 8, v___x_1298_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*3 + 16, v___x_1269_);
v_toProcessingContext_1301_ = lean_ctor_get(v_a_1270_, 0);
v_fileName_1302_ = lean_ctor_get(v_toProcessingContext_1301_, 1);
v_fileMap_1303_ = lean_ctor_get(v_toProcessingContext_1301_, 2);
v___x_1304_ = l_Lean_MessageData_nil;
v___x_1305_ = l_Lean_MessageData_ofFormat(v_a_1297_);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_mk_empty_array_with_capacity(v___x_1306_);
v___x_1308_ = lean_array_push(v___x_1307_, v___x_1305_);
v___x_1309_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1300_);
lean_ctor_set(v___x_1309_, 1, v___x_1304_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1292_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_inc_ref(v_fileMap_1303_);
v___x_1311_ = l_Lean_FileMap_toPosition(v_fileMap_1303_, v_pos_1271_);
v___x_1312_ = 0;
lean_inc_ref(v_fileName_1302_);
v___x_1313_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1313_, 0, v_fileName_1302_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
lean_ctor_set(v___x_1313_, 2, v___x_1295_);
lean_ctor_set(v___x_1313_, 3, v___x_1299_);
lean_ctor_set(v___x_1313_, 4, v___x_1310_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*5, v_val_1264_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*5 + 1, v___x_1312_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*5 + 2, v_val_1264_);
v___x_1314_ = l_Lean_MessageLog_add(v___x_1313_, v___x_1287_);
v___y_1276_ = v___y_1283_;
v_msgLog_1277_ = v___x_1314_;
goto v___jp_1275_;
}
else
{
lean_dec_ref_known(v___x_1296_, 1);
lean_dec(v___x_1268_);
v___y_1276_ = v___y_1283_;
v_msgLog_1277_ = v___x_1287_;
goto v___jp_1275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v_val_1322_, lean_object* v_val_1323_, lean_object* v_val_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v___x_1327_, lean_object* v_a_1328_, lean_object* v_pos_1329_, lean_object* v___x_1330_, lean_object* v_infoSt_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v_val_36487__boxed_1333_; uint8_t v___x_36492__boxed_1334_; lean_object* v_res_1335_; 
v_val_36487__boxed_1333_ = lean_unbox(v_val_1322_);
v___x_36492__boxed_1334_ = lean_unbox(v___x_1327_);
v_res_1335_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1320_, v___x_1321_, v_val_36487__boxed_1333_, v_val_1323_, v_val_1324_, v___x_1325_, v___x_1326_, v___x_36492__boxed_1334_, v_a_1328_, v_pos_1329_, v___x_1330_, v_infoSt_1331_);
lean_dec_ref(v_infoSt_1331_);
lean_dec_ref(v___x_1330_);
lean_dec(v_pos_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v___x_1325_);
lean_dec_ref(v_val_1324_);
lean_dec(v_val_1323_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, uint8_t v_val_1339_, lean_object* v_as_1340_, size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_b_1343_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_usize_dec_lt(v_i_1342_, v_sz_1341_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v___x_1338_);
lean_dec_ref(v___x_1336_);
return v_b_1343_;
}
else
{
lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1364_; 
v_snd_1346_ = lean_ctor_get(v_b_1343_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_b_1343_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v_b_1343_, 0);
lean_dec(v_unused_1365_);
v___x_1348_ = v_b_1343_;
v_isShared_1349_ = v_isSharedCheck_1364_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_dec(v_b_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1364_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_a_1350_; lean_object* v_msg_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v_a_1350_ = lean_array_uget_borrowed(v_as_1340_, v_i_1342_);
v_msg_1351_ = lean_ctor_get(v_a_1350_, 1);
v___x_1352_ = lean_box(0);
lean_inc_ref(v___x_1336_);
v___x_1353_ = l_Lean_FileMap_toPosition(v___x_1336_, v___x_1337_);
v___x_1354_ = 0;
v___x_1355_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1351_);
lean_inc_ref(v___x_1338_);
v___x_1356_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1356_, 0, v___x_1338_);
lean_ctor_set(v___x_1356_, 1, v___x_1353_);
lean_ctor_set(v___x_1356_, 2, v___x_1352_);
lean_ctor_set(v___x_1356_, 3, v___x_1355_);
lean_ctor_set(v___x_1356_, 4, v_msg_1351_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5, v_val_1339_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5 + 1, v___x_1354_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5 + 2, v_val_1339_);
v___x_1357_ = l_Lean_MessageLog_add(v___x_1356_, v_snd_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1357_);
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1359_ = v___x_1348_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
size_t v___x_1360_; size_t v___x_1361_; 
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_add(v_i_1342_, v___x_1360_);
v_i_1342_ = v___x_1361_;
v_b_1343_ = v___x_1359_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1366_, lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v_val_1369_, lean_object* v_as_1370_, lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_b_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_val_36600__boxed_1375_; size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_val_36600__boxed_1375_ = lean_unbox(v_val_1369_);
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1366_, v___x_1367_, v___x_1368_, v_val_36600__boxed_1375_, v_as_1370_, v_sz_boxed_1376_, v_i_boxed_1377_, v_b_1373_);
lean_dec_ref(v_as_1370_);
lean_dec(v___x_1367_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1379_, lean_object* v___x_1380_, lean_object* v___x_1381_, uint8_t v_val_1382_, lean_object* v_as_1383_, size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_b_1386_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1385_, v_sz_1384_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v___x_1381_);
lean_dec_ref(v___x_1379_);
return v_b_1386_;
}
else
{
lean_object* v_snd_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1407_; 
v_snd_1389_ = lean_ctor_get(v_b_1386_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_b_1386_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_b_1386_, 0);
lean_dec(v_unused_1408_);
v___x_1391_ = v_b_1386_;
v_isShared_1392_ = v_isSharedCheck_1407_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snd_1389_);
lean_dec(v_b_1386_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1407_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_a_1393_; lean_object* v_msg_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v_a_1393_ = lean_array_uget_borrowed(v_as_1383_, v_i_1385_);
v_msg_1394_ = lean_ctor_get(v_a_1393_, 1);
v___x_1395_ = lean_box(0);
lean_inc_ref(v___x_1379_);
v___x_1396_ = l_Lean_FileMap_toPosition(v___x_1379_, v___x_1380_);
v___x_1397_ = 0;
v___x_1398_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1394_);
lean_inc_ref(v___x_1381_);
v___x_1399_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1399_, 0, v___x_1381_);
lean_ctor_set(v___x_1399_, 1, v___x_1396_);
lean_ctor_set(v___x_1399_, 2, v___x_1395_);
lean_ctor_set(v___x_1399_, 3, v___x_1398_);
lean_ctor_set(v___x_1399_, 4, v_msg_1394_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5, v_val_1382_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5 + 1, v___x_1397_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*5 + 2, v_val_1382_);
v___x_1400_ = l_Lean_MessageLog_add(v___x_1399_, v_snd_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v___x_1400_);
lean_ctor_set(v___x_1391_, 0, v___x_1395_);
v___x_1402_ = v___x_1391_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1385_, v___x_1403_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1379_, v___x_1380_, v___x_1381_, v_val_1382_, v_as_1383_, v_sz_1384_, v___x_1404_, v___x_1402_);
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v_val_1412_, lean_object* v_as_1413_, lean_object* v_sz_1414_, lean_object* v_i_1415_, lean_object* v_b_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v_val_36652__boxed_1418_; size_t v_sz_boxed_1419_; size_t v_i_boxed_1420_; lean_object* v_res_1421_; 
v_val_36652__boxed_1418_ = lean_unbox(v_val_1412_);
v_sz_boxed_1419_ = lean_unbox_usize(v_sz_1414_);
lean_dec(v_sz_1414_);
v_i_boxed_1420_ = lean_unbox_usize(v_i_1415_);
lean_dec(v_i_1415_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1409_, v___x_1410_, v___x_1411_, v_val_36652__boxed_1418_, v_as_1413_, v_sz_boxed_1419_, v_i_boxed_1420_, v_b_1416_);
lean_dec_ref(v_as_1413_);
lean_dec(v___x_1410_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, uint8_t v_val_1426_, lean_object* v_n_1427_, lean_object* v_b_1428_){
_start:
{
if (lean_obj_tag(v_n_1427_) == 0)
{
lean_object* v_cs_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v_fst_1436_; 
v_cs_1430_ = lean_ctor_get(v_n_1427_, 0);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_b_1428_);
v_sz_1433_ = lean_array_size(v_cs_1430_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1422_, v___x_1423_, v___x_1424_, v___x_1425_, v_val_1426_, v_cs_1430_, v_sz_1433_, v___x_1434_, v___x_1432_);
v_fst_1436_ = lean_ctor_get(v___x_1435_, 0);
if (lean_obj_tag(v_fst_1436_) == 0)
{
lean_object* v_snd_1437_; lean_object* v___x_1438_; 
v_snd_1437_ = lean_ctor_get(v___x_1435_, 1);
lean_inc(v_snd_1437_);
lean_dec_ref(v___x_1435_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v_snd_1437_);
return v___x_1438_;
}
else
{
lean_object* v_val_1439_; 
lean_inc_ref(v_fst_1436_);
lean_dec_ref(v___x_1435_);
v_val_1439_ = lean_ctor_get(v_fst_1436_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v_fst_1436_, 1);
return v_val_1439_;
}
}
else
{
lean_object* v_vs_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; size_t v_sz_1443_; size_t v___x_1444_; lean_object* v___x_1445_; lean_object* v_fst_1446_; 
v_vs_1440_ = lean_ctor_get(v_n_1427_, 0);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_b_1428_);
v_sz_1443_ = lean_array_size(v_vs_1440_);
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1423_, v___x_1424_, v___x_1425_, v_val_1426_, v_vs_1440_, v_sz_1443_, v___x_1444_, v___x_1442_);
v_fst_1446_ = lean_ctor_get(v___x_1445_, 0);
if (lean_obj_tag(v_fst_1446_) == 0)
{
lean_object* v_snd_1447_; lean_object* v___x_1448_; 
v_snd_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_snd_1447_);
lean_dec_ref(v___x_1445_);
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_snd_1447_);
return v___x_1448_;
}
else
{
lean_object* v_val_1449_; 
lean_inc_ref(v_fst_1446_);
lean_dec_ref(v___x_1445_);
v_val_1449_ = lean_ctor_get(v_fst_1446_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v_fst_1446_, 1);
return v_val_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1450_, lean_object* v___x_1451_, lean_object* v___x_1452_, lean_object* v___x_1453_, uint8_t v_val_1454_, lean_object* v_as_1455_, size_t v_sz_1456_, size_t v_i_1457_, lean_object* v_b_1458_){
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
lean_object* v___x_1465_; lean_object* v_a_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_box(0);
v_a_1466_ = lean_array_uget_borrowed(v_as_1455_, v_i_1457_);
lean_inc(v_snd_1461_);
lean_inc_ref(v___x_1453_);
lean_inc_ref(v___x_1451_);
v___x_1467_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1450_, v___x_1451_, v___x_1452_, v___x_1453_, v_val_1454_, v_a_1466_, v_snd_1461_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec_ref(v___x_1453_);
lean_dec_ref(v___x_1451_);
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1468_);
v___x_1470_ = v___x_1463_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_snd_1461_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; 
lean_dec(v_snd_1461_);
v_a_1472_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1467_, 1);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v_a_1472_);
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1474_ = v___x_1463_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_a_1472_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
size_t v___x_1475_; size_t v___x_1476_; 
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1457_, v___x_1475_);
v_i_1457_ = v___x_1476_;
v_b_1458_ = v___x_1474_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1481_, lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, lean_object* v_val_1485_, lean_object* v_as_1486_, lean_object* v_sz_1487_, lean_object* v_i_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_val_36703__boxed_1491_; size_t v_sz_boxed_1492_; size_t v_i_boxed_1493_; lean_object* v_res_1494_; 
v_val_36703__boxed_1491_ = lean_unbox(v_val_1485_);
v_sz_boxed_1492_ = lean_unbox_usize(v_sz_1487_);
lean_dec(v_sz_1487_);
v_i_boxed_1493_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1481_, v___x_1482_, v___x_1483_, v___x_1484_, v_val_36703__boxed_1491_, v_as_1486_, v_sz_boxed_1492_, v_i_boxed_1493_, v_b_1489_);
lean_dec_ref(v_as_1486_);
lean_dec(v___x_1483_);
lean_dec_ref(v_init_1481_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1495_, lean_object* v___x_1496_, lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v_val_1499_, lean_object* v_n_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_val_36719__boxed_1503_; lean_object* v_res_1504_; 
v_val_36719__boxed_1503_ = lean_unbox(v_val_1499_);
v_res_1504_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1495_, v___x_1496_, v___x_1497_, v___x_1498_, v_val_36719__boxed_1503_, v_n_1500_, v_b_1501_);
lean_dec_ref(v_n_1500_);
lean_dec(v___x_1497_);
lean_dec_ref(v_init_1495_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1505_, lean_object* v___x_1506_, lean_object* v___x_1507_, uint8_t v_val_1508_, lean_object* v_as_1509_, size_t v_sz_1510_, size_t v_i_1511_, lean_object* v_b_1512_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_usize_dec_lt(v_i_1511_, v_sz_1510_);
if (v___x_1514_ == 0)
{
lean_dec_ref(v___x_1507_);
lean_dec_ref(v___x_1505_);
return v_b_1512_;
}
else
{
lean_object* v_snd_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1533_; 
v_snd_1515_ = lean_ctor_get(v_b_1512_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_b_1512_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; 
v_unused_1534_ = lean_ctor_get(v_b_1512_, 0);
lean_dec(v_unused_1534_);
v___x_1517_ = v_b_1512_;
v_isShared_1518_ = v_isSharedCheck_1533_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_snd_1515_);
lean_dec(v_b_1512_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1533_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_a_1519_; lean_object* v_msg_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v_a_1519_ = lean_array_uget_borrowed(v_as_1509_, v_i_1511_);
v_msg_1520_ = lean_ctor_get(v_a_1519_, 1);
v___x_1521_ = lean_box(0);
lean_inc_ref(v___x_1505_);
v___x_1522_ = l_Lean_FileMap_toPosition(v___x_1505_, v___x_1506_);
v___x_1523_ = 0;
v___x_1524_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1520_);
lean_inc_ref(v___x_1507_);
v___x_1525_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1525_, 0, v___x_1507_);
lean_ctor_set(v___x_1525_, 1, v___x_1522_);
lean_ctor_set(v___x_1525_, 2, v___x_1521_);
lean_ctor_set(v___x_1525_, 3, v___x_1524_);
lean_ctor_set(v___x_1525_, 4, v_msg_1520_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*5, v_val_1508_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*5 + 1, v___x_1523_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*5 + 2, v_val_1508_);
v___x_1526_ = l_Lean_MessageLog_add(v___x_1525_, v_snd_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 1, v___x_1526_);
lean_ctor_set(v___x_1517_, 0, v___x_1521_);
v___x_1528_ = v___x_1517_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
size_t v___x_1529_; size_t v___x_1530_; 
v___x_1529_ = ((size_t)1ULL);
v___x_1530_ = lean_usize_add(v_i_1511_, v___x_1529_);
v_i_1511_ = v___x_1530_;
v_b_1512_ = v___x_1528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v___x_1537_, lean_object* v_val_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v_val_36801__boxed_1544_; size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_val_36801__boxed_1544_ = lean_unbox(v_val_1538_);
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1535_, v___x_1536_, v___x_1537_, v_val_36801__boxed_1544_, v_as_1539_, v_sz_boxed_1545_, v_i_boxed_1546_, v_b_1542_);
lean_dec_ref(v_as_1539_);
lean_dec(v___x_1536_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1548_, lean_object* v___x_1549_, lean_object* v___x_1550_, uint8_t v_val_1551_, lean_object* v_as_1552_, size_t v_sz_1553_, size_t v_i_1554_, lean_object* v_b_1555_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
if (v___x_1557_ == 0)
{
lean_dec_ref(v___x_1550_);
lean_dec_ref(v___x_1548_);
return v_b_1555_;
}
else
{
lean_object* v_snd_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1576_; 
v_snd_1558_ = lean_ctor_get(v_b_1555_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_b_1555_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_b_1555_, 0);
lean_dec(v_unused_1577_);
v___x_1560_ = v_b_1555_;
v_isShared_1561_ = v_isSharedCheck_1576_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_snd_1558_);
lean_dec(v_b_1555_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1576_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_a_1562_; lean_object* v_msg_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v_a_1562_ = lean_array_uget_borrowed(v_as_1552_, v_i_1554_);
v_msg_1563_ = lean_ctor_get(v_a_1562_, 1);
v___x_1564_ = lean_box(0);
lean_inc_ref(v___x_1548_);
v___x_1565_ = l_Lean_FileMap_toPosition(v___x_1548_, v___x_1549_);
v___x_1566_ = 0;
v___x_1567_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1563_);
lean_inc_ref(v___x_1550_);
v___x_1568_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1568_, 0, v___x_1550_);
lean_ctor_set(v___x_1568_, 1, v___x_1565_);
lean_ctor_set(v___x_1568_, 2, v___x_1564_);
lean_ctor_set(v___x_1568_, 3, v___x_1567_);
lean_ctor_set(v___x_1568_, 4, v_msg_1563_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*5, v_val_1551_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*5 + 1, v___x_1566_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*5 + 2, v_val_1551_);
v___x_1569_ = l_Lean_MessageLog_add(v___x_1568_, v_snd_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v___x_1569_);
lean_ctor_set(v___x_1560_, 0, v___x_1564_);
v___x_1571_ = v___x_1560_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
size_t v___x_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((size_t)1ULL);
v___x_1573_ = lean_usize_add(v_i_1554_, v___x_1572_);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1548_, v___x_1549_, v___x_1550_, v_val_1551_, v_as_1552_, v_sz_1553_, v___x_1573_, v___x_1571_);
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1578_, lean_object* v___x_1579_, lean_object* v___x_1580_, lean_object* v_val_1581_, lean_object* v_as_1582_, lean_object* v_sz_1583_, lean_object* v_i_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_val_36853__boxed_1587_; size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v_val_36853__boxed_1587_ = lean_unbox(v_val_1581_);
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1583_);
lean_dec(v_sz_1583_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1578_, v___x_1579_, v___x_1580_, v_val_36853__boxed_1587_, v_as_1582_, v_sz_boxed_1588_, v_i_boxed_1589_, v_b_1585_);
lean_dec_ref(v_as_1582_);
lean_dec(v___x_1579_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, uint8_t v_val_1594_, lean_object* v_t_1595_, lean_object* v_init_1596_){
_start:
{
lean_object* v_root_1598_; lean_object* v_tail_1599_; lean_object* v___x_1600_; 
v_root_1598_ = lean_ctor_get(v_t_1595_, 0);
v_tail_1599_ = lean_ctor_get(v_t_1595_, 1);
lean_inc_ref(v___x_1593_);
lean_inc_ref(v___x_1591_);
lean_inc_ref(v_init_1596_);
v___x_1600_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1596_, v___x_1591_, v___x_1592_, v___x_1593_, v_val_1594_, v_root_1598_, v_init_1596_);
lean_dec_ref(v_init_1596_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; 
lean_dec_ref(v___x_1593_);
lean_dec_ref(v___x_1591_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
return v_a_1601_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v_fst_1608_; 
v_a_1602_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1602_);
v_sz_1605_ = lean_array_size(v_tail_1599_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1591_, v___x_1592_, v___x_1593_, v_val_1594_, v_tail_1599_, v_sz_1605_, v___x_1606_, v___x_1604_);
v_fst_1608_ = lean_ctor_get(v___x_1607_, 0);
if (lean_obj_tag(v_fst_1608_) == 0)
{
lean_object* v_snd_1609_; 
v_snd_1609_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_snd_1609_);
lean_dec_ref(v___x_1607_);
return v_snd_1609_;
}
else
{
lean_object* v_val_1610_; 
lean_inc_ref(v_fst_1608_);
lean_dec_ref(v___x_1607_);
v_val_1610_ = lean_ctor_get(v_fst_1608_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_fst_1608_, 1);
return v_val_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1611_, lean_object* v___x_1612_, lean_object* v___x_1613_, lean_object* v_val_1614_, lean_object* v_t_1615_, lean_object* v_init_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v_val_36904__boxed_1618_; lean_object* v_res_1619_; 
v_val_36904__boxed_1618_ = lean_unbox(v_val_1614_);
v_res_1619_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1611_, v___x_1612_, v___x_1613_, v_val_36904__boxed_1618_, v_t_1615_, v_init_1616_);
lean_dec_ref(v_t_1615_);
lean_dec(v___x_1612_);
return v_res_1619_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = l_Lean_firstFrontendMacroScope;
v___x_1622_ = lean_nat_add(v___x_1621_, v___x_1620_);
return v___x_1622_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1633_, lean_object* v_opts_1634_, lean_object* v___x_1635_, lean_object* v___x_1636_, lean_object* v___x_1637_, size_t v___x_1638_, uint8_t v___x_1639_, lean_object* v_env_1640_, lean_object* v___x_1641_, lean_object* v___x_1642_, lean_object* v_pos_1643_, uint8_t v_val_1644_, lean_object* v___x_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, uint8_t v___x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v_toProcessingContext_1653_; lean_object* v_fileName_1654_; lean_object* v_fileMap_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint16_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v_fileName_1679_; lean_object* v_fileMap_1680_; lean_object* v_currNamespace_1681_; lean_object* v_openDecls_1682_; lean_object* v_initHeartbeats_1683_; lean_object* v_maxHeartbeats_1684_; lean_object* v_quotContext_1685_; lean_object* v_currMacroScope_1686_; lean_object* v_cancelTk_x3f_1687_; lean_object* v_inheritedTraceOptions_1688_; lean_object* v_currRecDepth_1689_; lean_object* v_ref_1690_; uint8_t v_suppressElabErrors_1691_; uint8_t v_isRecordingDeps_1692_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___y_1712_; uint8_t v___y_1734_; uint8_t v___y_1735_; lean_object* v_env_1736_; uint8_t v___x_1737_; uint8_t v___y_1739_; uint16_t v___x_1740_; uint16_t v___x_1741_; uint16_t v___x_1742_; uint8_t v___x_1743_; 
v_toProcessingContext_1653_ = lean_ctor_get(v_a_1633_, 0);
v_fileName_1654_ = lean_ctor_get(v_toProcessingContext_1653_, 1);
v_fileMap_1655_ = lean_ctor_get(v_toProcessingContext_1653_, 2);
v___x_1656_ = lean_box(0);
v___x_1657_ = l_Lean_Core_getMaxHeartbeats(v_opts_1634_);
v___x_1658_ = l_Lean_firstFrontendMacroScope;
v___x_1659_ = lean_box(0);
v___x_1660_ = l_Lean_OptionFlags_ofOptions(v_opts_1634_);
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1663_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1635_);
v___x_1664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1635_);
lean_ctor_set(v___x_1664_, 1, v___x_1661_);
lean_ctor_set(v___x_1664_, 2, v___x_1656_);
v___x_1665_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1666_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1667_ = lean_mk_empty_array_with_capacity(v___x_1636_);
v___x_1668_ = l_Lean_Options_empty;
lean_inc_n(v___x_1636_, 5);
lean_inc_ref_n(v___x_1667_, 3);
v___x_1669_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
lean_ctor_set(v___x_1669_, 2, v___x_1667_);
lean_ctor_set(v___x_1669_, 3, v___x_1636_);
lean_ctor_set(v___x_1669_, 4, v___x_1636_);
lean_ctor_set(v___x_1669_, 5, v___x_1636_);
v___x_1670_ = lean_mk_empty_array_with_capacity(v___x_1637_);
lean_inc_ref(v___x_1670_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
lean_ctor_set(v___x_1672_, 2, v___x_1636_);
lean_ctor_set(v___x_1672_, 3, v___x_1636_);
lean_ctor_set_usize(v___x_1672_, 4, v___x_1638_);
v___x_1673_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1672_, 2);
v___x_1674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1672_);
lean_ctor_set(v___x_1674_, 2, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1675_, 0, v___x_1665_);
lean_ctor_set(v___x_1675_, 1, v___x_1665_);
lean_ctor_set(v___x_1675_, 2, v___x_1672_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*3, v___x_1639_);
lean_inc_ref(v___x_1641_);
v___x_1676_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1676_, 0, v_env_1640_);
lean_ctor_set(v___x_1676_, 1, v___x_1662_);
lean_ctor_set(v___x_1676_, 2, v___x_1663_);
lean_ctor_set(v___x_1676_, 3, v___x_1664_);
lean_ctor_set(v___x_1676_, 4, v___x_1641_);
lean_ctor_set(v___x_1676_, 5, v___x_1666_);
lean_ctor_set(v___x_1676_, 6, v___x_1669_);
lean_ctor_set(v___x_1676_, 7, v___x_1674_);
lean_ctor_set(v___x_1676_, 8, v___x_1675_);
lean_ctor_set(v___x_1676_, 9, v___x_1667_);
v___x_1677_ = lean_st_mk_ref(v___x_1676_);
v___x_1709_ = lean_st_ref_get(v___x_1648_);
v___x_1710_ = lean_st_ref_get(v___x_1677_);
v_env_1736_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref(v_env_1736_);
lean_dec(v___x_1710_);
v___x_1737_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1736_);
lean_dec_ref(v_env_1736_);
v___x_1740_ = 512;
v___x_1741_ = lean_uint16_land(v___x_1660_, v___x_1740_);
v___x_1742_ = 0;
v___x_1743_ = lean_uint16_dec_eq(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
if (v___x_1650_ == 0)
{
v___y_1739_ = v___x_1650_;
goto v___jp_1738_;
}
else
{
v___y_1734_ = v___x_1650_;
v___y_1735_ = v___x_1737_;
goto v___jp_1733_;
}
}
else
{
v___y_1739_ = v_val_1644_;
goto v___jp_1738_;
}
v___jp_1678_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1693_ = l_Lean_maxRecDepth;
v___x_1694_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1634_, v___x_1693_);
lean_inc(v_currMacroScope_1686_);
lean_inc(v_openDecls_1682_);
v___x_1695_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1695_, 0, v_fileName_1679_);
lean_ctor_set(v___x_1695_, 1, v_fileMap_1680_);
lean_ctor_set(v___x_1695_, 2, v_opts_1634_);
lean_ctor_set(v___x_1695_, 3, v___x_1694_);
lean_ctor_set(v___x_1695_, 4, v_currNamespace_1681_);
lean_ctor_set(v___x_1695_, 5, v_openDecls_1682_);
lean_ctor_set(v___x_1695_, 6, v_initHeartbeats_1683_);
lean_ctor_set(v___x_1695_, 7, v_maxHeartbeats_1684_);
lean_ctor_set(v___x_1695_, 8, v_quotContext_1685_);
lean_ctor_set(v___x_1695_, 9, v_currMacroScope_1686_);
lean_ctor_set(v___x_1695_, 10, v_cancelTk_x3f_1687_);
lean_ctor_set(v___x_1695_, 11, v_inheritedTraceOptions_1688_);
lean_inc(v_ref_1690_);
v___x_1696_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_currRecDepth_1689_);
lean_ctor_set(v___x_1696_, 2, v_ref_1690_);
lean_ctor_set_uint16(v___x_1696_, sizeof(void*)*3, v___x_1660_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*3 + 2, v_suppressElabErrors_1691_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*3 + 3, v_isRecordingDeps_1692_);
v___x_1697_ = l_Lean_Language_SnapshotTree_trace(v___x_1642_, v___x_1696_, v___x_1677_);
lean_dec_ref_known(v___x_1696_, 3);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v___x_1698_; lean_object* v_traceState_1699_; lean_object* v_traces_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref_known(v___x_1697_, 1);
lean_dec_ref(v___x_1647_);
v___x_1698_ = lean_st_ref_get(v___x_1677_);
lean_dec(v___x_1677_);
v_traceState_1699_ = lean_ctor_get(v___x_1698_, 4);
lean_inc_ref(v_traceState_1699_);
lean_dec(v___x_1698_);
v_traces_1700_ = lean_ctor_get(v_traceState_1699_, 0);
lean_inc_ref(v_traces_1700_);
lean_dec_ref(v_traceState_1699_);
v___x_1701_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1654_);
lean_inc_ref(v_fileMap_1655_);
v___x_1702_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1655_, v_pos_1643_, v_fileName_1654_, v_val_1644_, v_traces_1700_, v___x_1701_);
lean_dec_ref(v_traces_1700_);
v___x_1703_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1702_);
v___x_1704_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1704_, 0, v___x_1645_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
lean_ctor_set(v___x_1704_, 2, v___x_1646_);
lean_ctor_set(v___x_1704_, 3, v___x_1641_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*4, v_val_1644_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v___x_1667_);
v___x_1706_ = lean_task_pure(v___x_1705_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec_ref_known(v___x_1697_, 1);
lean_dec(v___x_1677_);
lean_dec(v___x_1646_);
lean_dec_ref(v___x_1645_);
lean_dec_ref(v___x_1641_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1647_);
lean_ctor_set(v___x_1707_, 1, v___x_1667_);
v___x_1708_ = lean_task_pure(v___x_1707_);
return v___x_1708_;
}
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v_env_1714_; lean_object* v_nextMacroScope_1715_; lean_object* v_ngen_1716_; lean_object* v_auxDeclNGen_1717_; lean_object* v_traceState_1718_; lean_object* v_recordedDeps_1719_; lean_object* v_messages_1720_; lean_object* v_infoState_1721_; lean_object* v_snapshotTasks_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v___x_1713_ = lean_st_ref_take(v___x_1677_);
v_env_1714_ = lean_ctor_get(v___x_1713_, 0);
v_nextMacroScope_1715_ = lean_ctor_get(v___x_1713_, 1);
v_ngen_1716_ = lean_ctor_get(v___x_1713_, 2);
v_auxDeclNGen_1717_ = lean_ctor_get(v___x_1713_, 3);
v_traceState_1718_ = lean_ctor_get(v___x_1713_, 4);
v_recordedDeps_1719_ = lean_ctor_get(v___x_1713_, 6);
v_messages_1720_ = lean_ctor_get(v___x_1713_, 7);
v_infoState_1721_ = lean_ctor_get(v___x_1713_, 8);
v_snapshotTasks_1722_ = lean_ctor_get(v___x_1713_, 9);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v___x_1713_, 5);
lean_dec(v_unused_1732_);
v___x_1724_ = v___x_1713_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_snapshotTasks_1722_);
lean_inc(v_infoState_1721_);
lean_inc(v_messages_1720_);
lean_inc(v_recordedDeps_1719_);
lean_inc(v_traceState_1718_);
lean_inc(v_auxDeclNGen_1717_);
lean_inc(v_ngen_1716_);
lean_inc(v_nextMacroScope_1715_);
lean_inc(v_env_1714_);
lean_dec(v___x_1713_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_Kernel_enableDiag(v_env_1714_, v___y_1712_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 5, v___x_1666_);
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_nextMacroScope_1715_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_ngen_1716_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_auxDeclNGen_1717_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_traceState_1718_);
lean_ctor_set(v_reuseFailAlloc_1730_, 5, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1730_, 6, v_recordedDeps_1719_);
lean_ctor_set(v_reuseFailAlloc_1730_, 7, v_messages_1720_);
lean_ctor_set(v_reuseFailAlloc_1730_, 8, v_infoState_1721_);
lean_ctor_set(v_reuseFailAlloc_1730_, 9, v_snapshotTasks_1722_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_st_ref_put(v___x_1677_, v___x_1728_);
lean_inc(v___x_1636_);
lean_inc(v___x_1635_);
lean_inc_ref(v_fileMap_1655_);
lean_inc_ref(v_fileName_1654_);
v_fileName_1679_ = v_fileName_1654_;
v_fileMap_1680_ = v_fileMap_1655_;
v_currNamespace_1681_ = v___x_1635_;
v_openDecls_1682_ = v___x_1656_;
v_initHeartbeats_1683_ = v___x_1636_;
v_maxHeartbeats_1684_ = v___x_1657_;
v_quotContext_1685_ = v___x_1635_;
v_currMacroScope_1686_ = v___x_1658_;
v_cancelTk_x3f_1687_ = v___x_1649_;
v_inheritedTraceOptions_1688_ = v___x_1709_;
v_currRecDepth_1689_ = v___x_1636_;
v_ref_1690_ = v___x_1659_;
v_suppressElabErrors_1691_ = v_val_1644_;
v_isRecordingDeps_1692_ = v_val_1644_;
goto v___jp_1678_;
}
}
}
v___jp_1733_:
{
if (v___y_1735_ == 0)
{
v___y_1712_ = v___y_1734_;
goto v___jp_1711_;
}
else
{
lean_inc(v___x_1636_);
lean_inc(v___x_1635_);
lean_inc_ref(v_fileMap_1655_);
lean_inc_ref(v_fileName_1654_);
v_fileName_1679_ = v_fileName_1654_;
v_fileMap_1680_ = v_fileMap_1655_;
v_currNamespace_1681_ = v___x_1635_;
v_openDecls_1682_ = v___x_1656_;
v_initHeartbeats_1683_ = v___x_1636_;
v_maxHeartbeats_1684_ = v___x_1657_;
v_quotContext_1685_ = v___x_1635_;
v_currMacroScope_1686_ = v___x_1658_;
v_cancelTk_x3f_1687_ = v___x_1649_;
v_inheritedTraceOptions_1688_ = v___x_1709_;
v_currRecDepth_1689_ = v___x_1636_;
v_ref_1690_ = v___x_1659_;
v_suppressElabErrors_1691_ = v_val_1644_;
v_isRecordingDeps_1692_ = v_val_1644_;
goto v___jp_1678_;
}
}
v___jp_1738_:
{
if (v___x_1737_ == 0)
{
v___y_1734_ = v___y_1739_;
v___y_1735_ = v___x_1650_;
goto v___jp_1733_;
}
else
{
v___y_1712_ = v___y_1739_;
goto v___jp_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1744_ = _args[0];
lean_object* v_opts_1745_ = _args[1];
lean_object* v___x_1746_ = _args[2];
lean_object* v___x_1747_ = _args[3];
lean_object* v___x_1748_ = _args[4];
lean_object* v___x_1749_ = _args[5];
lean_object* v___x_1750_ = _args[6];
lean_object* v_env_1751_ = _args[7];
lean_object* v___x_1752_ = _args[8];
lean_object* v___x_1753_ = _args[9];
lean_object* v_pos_1754_ = _args[10];
lean_object* v_val_1755_ = _args[11];
lean_object* v___x_1756_ = _args[12];
lean_object* v___x_1757_ = _args[13];
lean_object* v___x_1758_ = _args[14];
lean_object* v___x_1759_ = _args[15];
lean_object* v___x_1760_ = _args[16];
lean_object* v___x_1761_ = _args[17];
lean_object* v_x_1762_ = _args[18];
lean_object* v___y_1763_ = _args[19];
_start:
{
size_t v___x_36964__boxed_1764_; uint8_t v___x_36965__boxed_1765_; uint8_t v_val_36968__boxed_1766_; uint8_t v___x_36974__boxed_1767_; lean_object* v_res_1768_; 
v___x_36964__boxed_1764_ = lean_unbox_usize(v___x_1749_);
lean_dec(v___x_1749_);
v___x_36965__boxed_1765_ = lean_unbox(v___x_1750_);
v_val_36968__boxed_1766_ = lean_unbox(v_val_1755_);
v___x_36974__boxed_1767_ = lean_unbox(v___x_1761_);
v_res_1768_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1744_, v_opts_1745_, v___x_1746_, v___x_1747_, v___x_1748_, v___x_36964__boxed_1764_, v___x_36965__boxed_1765_, v_env_1751_, v___x_1752_, v___x_1753_, v_pos_1754_, v_val_36968__boxed_1766_, v___x_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v___x_1760_, v___x_36974__boxed_1767_, v_x_1762_);
lean_dec(v___x_1759_);
lean_dec(v_pos_1754_);
lean_dec(v___x_1748_);
lean_dec_ref(v_a_1744_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1769_, lean_object* v___x_1770_, lean_object* v_parserState_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v_toProcessingContext_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_toProcessingContext_1773_ = lean_ctor_get(v_a_1769_, 0);
v___x_1774_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1773_);
v___x_1775_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1773_, v___x_1770_, v_parserState_1771_, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1776_, lean_object* v___x_1777_, lean_object* v_parserState_1778_, lean_object* v_x_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1776_, v___x_1777_, v_parserState_1778_, v_x_1779_);
lean_dec_ref(v_a_1776_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1782_, size_t v_i_1783_, size_t v_stop_1784_, lean_object* v_b_1785_){
_start:
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_usize_dec_eq(v_i_1783_, v_stop_1784_);
if (v___x_1787_ == 0)
{
lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; 
v___f_1788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1789_ = lean_array_uget_borrowed(v_as_1782_, v_i_1783_);
lean_inc(v___x_1789_);
v___x_1790_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1788_, v___x_1789_);
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_add(v_i_1783_, v___x_1791_);
v_i_1783_ = v___x_1792_;
v_b_1785_ = v___x_1790_;
goto _start;
}
else
{
return v_b_1785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1794_, lean_object* v_i_1795_, lean_object* v_stop_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_){
_start:
{
size_t v_i_boxed_1799_; size_t v_stop_boxed_1800_; lean_object* v_res_1801_; 
v_i_boxed_1799_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_stop_boxed_1800_ = lean_unbox_usize(v_stop_1796_);
lean_dec(v_stop_1796_);
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1794_, v_i_boxed_1799_, v_stop_boxed_1800_, v_b_1797_);
lean_dec_ref(v_as_1794_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1802_, lean_object* v_stx_1803_, lean_object* v_revCmds_1804_, lean_object* v_newParserState_1805_, lean_object* v_val_1806_, lean_object* v_sync_1807_, lean_object* v_val_1808_, lean_object* v_a_1809_, lean_object* v_oldNext_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v_sync_boxed_1812_; lean_object* v_res_1813_; 
v_sync_boxed_1812_ = lean_unbox(v_sync_1807_);
v_res_1813_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1802_, v_stx_1803_, v_revCmds_1804_, v_newParserState_1805_, v_val_1806_, v_sync_boxed_1812_, v_val_1808_, v_a_1809_, v_oldNext_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1814_, lean_object* v_stx_1815_, lean_object* v_revCmds_1816_, lean_object* v_newParserState_1817_, lean_object* v_val_1818_, uint8_t v_sync_1819_, lean_object* v_val_1820_, lean_object* v_a_1821_, lean_object* v_oldResult_1822_){
_start:
{
lean_object* v_task_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; 
v_task_1824_ = lean_ctor_get(v_val_1814_, 3);
lean_inc_ref(v_task_1824_);
lean_dec_ref(v_val_1814_);
v___x_1825_ = lean_box(v_sync_1819_);
lean_inc_ref(v_a_1821_);
v___f_1826_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1826_, 0, v_oldResult_1822_);
lean_closure_set(v___f_1826_, 1, v_stx_1815_);
lean_closure_set(v___f_1826_, 2, v_revCmds_1816_);
lean_closure_set(v___f_1826_, 3, v_newParserState_1817_);
lean_closure_set(v___f_1826_, 4, v_val_1818_);
lean_closure_set(v___f_1826_, 5, v___x_1825_);
lean_closure_set(v___f_1826_, 6, v_val_1820_);
lean_closure_set(v___f_1826_, 7, v_a_1821_);
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = 1;
v___x_1829_ = l_BaseIO_chainTask___redArg(v_task_1824_, v___f_1826_, v___x_1827_, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1830_, lean_object* v_stx_1831_, lean_object* v_revCmds_1832_, lean_object* v_newParserState_1833_, lean_object* v_val_1834_, lean_object* v_sync_1835_, lean_object* v_val_1836_, lean_object* v_a_1837_, lean_object* v_oldResult_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_sync_boxed_1840_; lean_object* v_res_1841_; 
v_sync_boxed_1840_ = lean_unbox(v_sync_1835_);
v_res_1841_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1830_, v_stx_1831_, v_revCmds_1832_, v_newParserState_1833_, v_val_1834_, v_sync_boxed_1840_, v_val_1836_, v_a_1837_, v_oldResult_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1841_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1850_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1851_ = l_Lean_Name_append(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1855_, lean_object* v_val_1856_, lean_object* v_fst_1857_, lean_object* v_revCmds_1858_, lean_object* v_fst_1859_, uint8_t v_val_1860_, lean_object* v_a_1861_, lean_object* v_snd_1862_, lean_object* v___x_1863_, uint8_t v___x_1864_, lean_object* v_fst_1865_, lean_object* v_val_1866_, lean_object* v_val_1867_, lean_object* v___x_1868_, lean_object* v___f_1869_, lean_object* v___f_1870_, lean_object* v___f_1871_, lean_object* v_pos_1872_, lean_object* v_cmdState_1873_, lean_object* v_val_1874_, lean_object* v___x_1875_, lean_object* v_opts_1876_, lean_object* v___x_1877_, lean_object* v_snd_1878_, lean_object* v_prom_1879_, lean_object* v_old_x3f_1880_, lean_object* v_parseCancelTk_1881_, lean_object* v_next_x3f_1882_){
_start:
{
lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v_snapshotTasks_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v_traceTask_1891_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; size_t v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v_env_1932_; lean_object* v_messages_1933_; lean_object* v_scopes_1934_; lean_object* v_infoState_1935_; lean_object* v_traceState_1936_; lean_object* v_snapshotTasks_1937_; lean_object* v_codeQualityEntryTasks_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v_reportedCmdState_1942_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; size_t v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v_reportedCmdState_1999_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; size_t v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2057_; 
if (lean_obj_tag(v_next_x3f_1882_) == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v_parseCancelTk_1881_);
v___x_2110_ = lean_box(0);
v___y_2057_ = v___x_2110_;
goto v___jp_2056_;
}
else
{
lean_object* v_toProcessingContext_2111_; lean_object* v_val_2112_; lean_object* v_pos_2113_; lean_object* v_endPos_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_toProcessingContext_2111_ = lean_ctor_get(v_a_1861_, 0);
v_val_2112_ = lean_ctor_get(v_next_x3f_1882_, 0);
v_pos_2113_ = lean_ctor_get(v_fst_1859_, 0);
v_endPos_2114_ = lean_ctor_get(v_toProcessingContext_2111_, 3);
v___x_2115_ = lean_box(0);
lean_inc(v_endPos_2114_);
lean_inc(v_pos_2113_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_pos_2113_);
lean_ctor_set(v___x_2116_, 1, v_endPos_2114_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_parseCancelTk_1881_);
v___x_2119_ = l_IO_Promise_result_x21___redArg(v_val_2112_);
v___x_2120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2115_);
lean_ctor_set(v___x_2120_, 1, v___x_2117_);
lean_ctor_set(v___x_2120_, 2, v___x_2118_);
lean_ctor_set(v___x_2120_, 3, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
v___y_2057_ = v___x_2121_;
goto v___jp_2056_;
}
v___jp_1884_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1892_, 0, v___y_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1855_);
lean_ctor_set(v___x_1892_, 2, v___y_1886_);
lean_ctor_set(v___x_1892_, 3, v_traceTask_1891_);
v___x_1893_ = lean_array_push(v_snapshotTasks_1888_, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___y_1885_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_io_promise_resolve(v___x_1894_, v_val_1856_);
if (lean_obj_tag(v_next_x3f_1882_) == 1)
{
lean_object* v_val_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_val_1896_ = lean_ctor_get(v_next_x3f_1882_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v_next_x3f_1882_, 1);
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_fst_1857_);
lean_ctor_set(v___x_1898_, 1, v_revCmds_1858_);
v___x_1899_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1897_, v_fst_1859_, v___y_1887_, v_val_1896_, v_val_1860_, v___y_1889_, v___x_1898_, v_a_1861_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
lean_dec_ref(v___y_1889_);
lean_dec_ref(v___y_1887_);
lean_dec(v_next_x3f_1882_);
lean_dec_ref(v_fst_1859_);
lean_dec(v_revCmds_1858_);
lean_dec(v_fst_1857_);
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
}
v___jp_1901_:
{
lean_object* v_snapshotTasks_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_snapshotTasks_1908_ = lean_ctor_get(v___y_1902_, 10);
lean_inc_ref(v_snapshotTasks_1908_);
v___x_1909_ = lean_mk_empty_array_with_capacity(v___y_1907_);
lean_dec(v___y_1907_);
lean_inc_ref(v___y_1904_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___y_1904_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_task_pure(v___x_1910_);
v___y_1885_ = v___y_1904_;
v___y_1886_ = v___y_1903_;
v___y_1887_ = v___y_1902_;
v_snapshotTasks_1888_ = v_snapshotTasks_1908_;
v___y_1889_ = v___y_1905_;
v___y_1890_ = v___y_1906_;
v_traceTask_1891_ = v___x_1911_;
goto v___jp_1884_;
}
v___jp_1912_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_opts_1952_; uint8_t v_hasTrace_1953_; 
v___x_1943_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1933_);
v___x_1944_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1944_, 0, v___y_1922_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
lean_ctor_set(v___x_1944_, 2, v___y_1940_);
lean_ctor_set(v___x_1944_, 3, v_traceState_1936_);
lean_ctor_set_uint8(v___x_1944_, sizeof(void*)*4, v_val_1860_);
v___x_1945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v_reportedCmdState_1942_);
lean_ctor_set(v___x_1945_, 2, v_codeQualityEntryTasks_1938_);
v___x_1946_ = lean_io_promise_resolve(v___x_1945_, v_val_1867_);
v___x_1947_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1935_);
lean_inc(v___y_1929_);
v___x_1948_ = l_BaseIO_chainTask___redArg(v___x_1947_, v___y_1927_, v___y_1929_, v___x_1864_);
v___x_1949_ = l_Lean_inheritedTraceOptions;
v___x_1950_ = lean_st_ref_get(v___x_1949_);
v___x_1951_ = l_List_head_x21___redArg(v___x_1868_, v_scopes_1934_);
lean_dec(v_scopes_1934_);
lean_dec_ref(v___x_1868_);
v_opts_1952_ = lean_ctor_get(v___x_1951_, 1);
lean_inc_ref(v_opts_1952_);
lean_dec(v___x_1951_);
v_hasTrace_1953_ = lean_ctor_get_uint8(v_opts_1952_, sizeof(void*)*1);
if (v_hasTrace_1953_ == 0)
{
lean_dec_ref(v_opts_1952_);
lean_dec(v___x_1950_);
lean_dec_ref(v___y_1941_);
lean_dec_ref(v_snapshotTasks_1937_);
lean_dec_ref(v_env_1932_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec(v_pos_1872_);
lean_dec_ref(v___f_1871_);
lean_dec_ref(v___f_1870_);
lean_dec_ref(v___f_1869_);
lean_dec(v___x_1863_);
v___y_1902_ = v___y_1931_;
v___y_1903_ = v___y_1921_;
v___y_1904_ = v___y_1939_;
v___y_1905_ = v___y_1923_;
v___y_1906_ = v___y_1928_;
v___y_1907_ = v___y_1929_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1950_, v_opts_1952_, v___x_1954_);
lean_dec(v___x_1950_);
if (v___x_1955_ == 0)
{
lean_dec_ref(v_opts_1952_);
lean_dec_ref(v___y_1941_);
lean_dec_ref(v_snapshotTasks_1937_);
lean_dec_ref(v_env_1932_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec(v_pos_1872_);
lean_dec_ref(v___f_1871_);
lean_dec_ref(v___f_1870_);
lean_dec_ref(v___f_1869_);
lean_dec(v___x_1863_);
v___y_1902_ = v___y_1931_;
v___y_1903_ = v___y_1921_;
v___y_1904_ = v___y_1939_;
v___y_1905_ = v___y_1923_;
v___y_1906_ = v___y_1928_;
v___y_1907_ = v___y_1929_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_inc_n(v___y_1929_, 3);
v___x_1956_ = lean_task_map(v___f_1869_, v___y_1924_, v___y_1929_, v___x_1864_);
lean_inc_n(v___y_1921_, 3);
lean_inc_n(v___y_1930_, 2);
lean_inc_n(v___y_1925_, 2);
v___x_1957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1957_, 0, v___y_1925_);
lean_ctor_set(v___x_1957_, 1, v___y_1930_);
lean_ctor_set(v___x_1957_, 2, v___y_1921_);
lean_ctor_set(v___x_1957_, 3, v___x_1956_);
v___x_1958_ = lean_task_map(v___f_1870_, v___y_1941_, v___y_1929_, v___x_1864_);
v___x_1959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1959_, 0, v___y_1925_);
lean_ctor_set(v___x_1959_, 1, v___y_1930_);
lean_ctor_set(v___x_1959_, 2, v___y_1921_);
lean_ctor_set(v___x_1959_, 3, v___x_1958_);
v___x_1960_ = lean_task_map(v___f_1871_, v___y_1926_, v___y_1929_, v___x_1864_);
v___x_1961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1961_, 0, v___y_1925_);
lean_ctor_set(v___x_1961_, 1, v___y_1930_);
lean_ctor_set(v___x_1961_, 2, v___y_1921_);
lean_ctor_set(v___x_1961_, 3, v___x_1960_);
v___x_1962_ = lean_unsigned_to_nat(3u);
v___x_1963_ = lean_mk_empty_array_with_capacity(v___x_1962_);
v___x_1964_ = lean_array_push(v___x_1963_, v___x_1957_);
v___x_1965_ = lean_array_push(v___x_1964_, v___x_1959_);
v___x_1966_ = lean_array_push(v___x_1965_, v___x_1961_);
v___x_1967_ = l_Array_append___redArg(v___x_1966_, v_snapshotTasks_1937_);
lean_inc_ref(v___y_1939_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1939_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_box_usize(v___y_1920_);
v___x_1970_ = lean_box(v___x_1864_);
v___x_1971_ = lean_box(v_val_1860_);
v___x_1972_ = lean_box(v___x_1955_);
lean_inc_ref(v___x_1968_);
lean_inc_ref(v___y_1917_);
lean_inc_ref(v_a_1861_);
v___f_1973_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1973_, 0, v_a_1861_);
lean_closure_set(v___f_1973_, 1, v_opts_1952_);
lean_closure_set(v___f_1973_, 2, v___x_1863_);
lean_closure_set(v___f_1973_, 3, v___y_1918_);
lean_closure_set(v___f_1973_, 4, v___y_1914_);
lean_closure_set(v___f_1973_, 5, v___x_1969_);
lean_closure_set(v___f_1973_, 6, v___x_1970_);
lean_closure_set(v___f_1973_, 7, v_env_1932_);
lean_closure_set(v___f_1973_, 8, v___y_1917_);
lean_closure_set(v___f_1973_, 9, v___x_1968_);
lean_closure_set(v___f_1973_, 10, v_pos_1872_);
lean_closure_set(v___f_1973_, 11, v___x_1971_);
lean_closure_set(v___f_1973_, 12, v___y_1919_);
lean_closure_set(v___f_1973_, 13, v___y_1915_);
lean_closure_set(v___f_1973_, 14, v___y_1916_);
lean_closure_set(v___f_1973_, 15, v___x_1949_);
lean_closure_set(v___f_1973_, 16, v___y_1913_);
lean_closure_set(v___f_1973_, 17, v___x_1972_);
v___x_1974_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1968_);
v___x_1975_ = lean_io_bind_task(v___x_1974_, v___f_1973_, v___y_1929_, v_val_1860_);
v___y_1885_ = v___y_1939_;
v___y_1886_ = v___y_1921_;
v___y_1887_ = v___y_1931_;
v_snapshotTasks_1888_ = v_snapshotTasks_1937_;
v___y_1889_ = v___y_1923_;
v___y_1890_ = v___y_1928_;
v_traceTask_1891_ = v___x_1975_;
goto v___jp_1884_;
}
}
}
v___jp_1976_:
{
lean_object* v_env_2000_; lean_object* v_messages_2001_; lean_object* v_scopes_2002_; lean_object* v_infoState_2003_; lean_object* v_traceState_2004_; lean_object* v_snapshotTasks_2005_; lean_object* v_codeQualityEntryTasks_2006_; 
v_env_2000_ = lean_ctor_get(v___y_1995_, 0);
lean_inc_ref(v_env_2000_);
v_messages_2001_ = lean_ctor_get(v___y_1995_, 1);
lean_inc_ref(v_messages_2001_);
v_scopes_2002_ = lean_ctor_get(v___y_1995_, 2);
lean_inc(v_scopes_2002_);
v_infoState_2003_ = lean_ctor_get(v___y_1995_, 8);
lean_inc_ref(v_infoState_2003_);
v_traceState_2004_ = lean_ctor_get(v___y_1995_, 9);
lean_inc_ref(v_traceState_2004_);
v_snapshotTasks_2005_ = lean_ctor_get(v___y_1995_, 10);
lean_inc_ref(v_snapshotTasks_2005_);
v_codeQualityEntryTasks_2006_ = lean_ctor_get(v___y_1995_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2006_);
v___y_1913_ = v___y_1977_;
v___y_1914_ = v___y_1978_;
v___y_1915_ = v___y_1979_;
v___y_1916_ = v___y_1981_;
v___y_1917_ = v___y_1980_;
v___y_1918_ = v___y_1982_;
v___y_1919_ = v___y_1984_;
v___y_1920_ = v___y_1983_;
v___y_1921_ = v___y_1985_;
v___y_1922_ = v___y_1986_;
v___y_1923_ = v___y_1987_;
v___y_1924_ = v___y_1988_;
v___y_1925_ = v___y_1989_;
v___y_1926_ = v___y_1990_;
v___y_1927_ = v___y_1991_;
v___y_1928_ = v___y_1992_;
v___y_1929_ = v___y_1993_;
v___y_1930_ = v___y_1994_;
v___y_1931_ = v___y_1995_;
v_env_1932_ = v_env_2000_;
v_messages_1933_ = v_messages_2001_;
v_scopes_1934_ = v_scopes_2002_;
v_infoState_1935_ = v_infoState_2003_;
v_traceState_1936_ = v_traceState_2004_;
v_snapshotTasks_1937_ = v_snapshotTasks_2005_;
v_codeQualityEntryTasks_1938_ = v_codeQualityEntryTasks_2006_;
v___y_1939_ = v___y_1996_;
v___y_1940_ = v___y_1997_;
v___y_1941_ = v___y_1998_;
v_reportedCmdState_1942_ = v_reportedCmdState_1999_;
goto v___jp_1912_;
}
v___jp_2007_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___f_2028_; uint8_t v___x_2029_; 
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___y_2023_);
lean_ctor_set(v___x_2024_, 1, v_val_1866_);
lean_inc_ref(v___y_2011_);
lean_inc_n(v_pos_1872_, 2);
lean_inc(v_revCmds_1858_);
lean_inc(v_fst_1857_);
v___x_2025_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1857_, v_revCmds_1858_, v_cmdState_1873_, v_pos_1872_, v___x_2024_, v___y_2011_, v_a_1861_);
v___x_2026_ = lean_box(v_val_1860_);
v___x_2027_ = lean_box(v___x_1864_);
lean_inc_ref(v_a_1861_);
lean_inc(v___y_2015_);
lean_inc_ref(v___x_1868_);
lean_inc_ref(v___x_2025_);
lean_inc_ref(v___y_2014_);
lean_inc_ref(v___y_2019_);
v___f_2028_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2028_, 0, v___y_2019_);
lean_closure_set(v___f_2028_, 1, v___y_2014_);
lean_closure_set(v___f_2028_, 2, v___x_2026_);
lean_closure_set(v___f_2028_, 3, v_val_1874_);
lean_closure_set(v___f_2028_, 4, v___x_2025_);
lean_closure_set(v___f_2028_, 5, v___x_1868_);
lean_closure_set(v___f_2028_, 6, v___y_2015_);
lean_closure_set(v___f_2028_, 7, v___x_2027_);
lean_closure_set(v___f_2028_, 8, v_a_1861_);
lean_closure_set(v___f_2028_, 9, v_pos_1872_);
lean_closure_set(v___f_2028_, 10, v___x_1875_);
v___x_2029_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1876_, v___x_1877_);
if (v___x_2029_ == 0)
{
lean_inc_ref(v___x_2025_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc(v___y_2008_);
v___y_1977_ = v___y_2008_;
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2013_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2018_;
v___y_1984_ = v___y_2019_;
v___y_1985_ = v___y_2008_;
v___y_1986_ = v___y_2019_;
v___y_1987_ = v___y_2011_;
v___y_1988_ = v___y_2017_;
v___y_1989_ = v___y_2009_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___f_2028_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2015_;
v___y_1994_ = v___y_2016_;
v___y_1995_ = v___x_2025_;
v___y_1996_ = v___y_2013_;
v___y_1997_ = v___y_2012_;
v___y_1998_ = v___y_2022_;
v_reportedCmdState_1999_ = v___x_2025_;
goto v___jp_1976_;
}
else
{
uint8_t v___x_2030_; 
lean_inc(v_fst_1857_);
v___x_2030_ = l_Lean_Parser_isTerminalCommand(v_fst_1857_);
if (v___x_2030_ == 0)
{
if (v___x_2029_ == 0)
{
lean_inc_ref(v___x_2025_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc(v___y_2008_);
v___y_1977_ = v___y_2008_;
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2013_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2018_;
v___y_1984_ = v___y_2019_;
v___y_1985_ = v___y_2008_;
v___y_1986_ = v___y_2019_;
v___y_1987_ = v___y_2011_;
v___y_1988_ = v___y_2017_;
v___y_1989_ = v___y_2009_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___f_2028_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2015_;
v___y_1994_ = v___y_2016_;
v___y_1995_ = v___x_2025_;
v___y_1996_ = v___y_2013_;
v___y_1997_ = v___y_2012_;
v___y_1998_ = v___y_2022_;
v_reportedCmdState_1999_ = v___x_2025_;
goto v___jp_1976_;
}
else
{
lean_object* v_env_2031_; lean_object* v_messages_2032_; lean_object* v_scopes_2033_; lean_object* v_infoState_2034_; lean_object* v_traceState_2035_; lean_object* v_snapshotTasks_2036_; lean_object* v_codeQualityEntryTasks_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_env_2031_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_ref_n(v_env_2031_, 2);
v_messages_2032_ = lean_ctor_get(v___x_2025_, 1);
lean_inc_ref(v_messages_2032_);
v_scopes_2033_ = lean_ctor_get(v___x_2025_, 2);
lean_inc(v_scopes_2033_);
v_infoState_2034_ = lean_ctor_get(v___x_2025_, 8);
lean_inc_ref(v_infoState_2034_);
v_traceState_2035_ = lean_ctor_get(v___x_2025_, 9);
lean_inc_ref(v_traceState_2035_);
v_snapshotTasks_2036_ = lean_ctor_get(v___x_2025_, 10);
lean_inc_ref(v_snapshotTasks_2036_);
v_codeQualityEntryTasks_2037_ = lean_ctor_get(v___x_2025_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2037_);
v___x_2038_ = lean_mk_empty_array_with_capacity(v___y_2010_);
lean_inc_ref(v___x_2038_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_inc_n(v___y_2015_, 4);
v___x_2040_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2038_);
lean_ctor_set(v___x_2040_, 2, v___y_2015_);
lean_ctor_set(v___x_2040_, 3, v___y_2015_);
lean_ctor_set_usize(v___x_2040_, 4, v___y_2018_);
v___x_2041_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2040_, 2);
v___x_2042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2040_);
lean_ctor_set(v___x_2042_, 2, v___x_2041_);
v___x_2043_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2044_ = l_Lean_Options_empty;
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_mk_empty_array_with_capacity(v___y_2015_);
lean_inc_ref_n(v___x_2046_, 3);
lean_inc_n(v___x_1863_, 2);
v___x_2047_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2047_, 0, v___x_2043_);
lean_ctor_set(v___x_2047_, 1, v___x_2044_);
lean_ctor_set(v___x_2047_, 2, v___x_1863_);
lean_ctor_set(v___x_2047_, 3, v___x_2045_);
lean_ctor_set(v___x_2047_, 4, v___x_2045_);
lean_ctor_set(v___x_2047_, 5, v___x_2046_);
lean_ctor_set(v___x_2047_, 6, v___x_2046_);
lean_ctor_set(v___x_2047_, 7, v___x_2045_);
lean_ctor_set(v___x_2047_, 8, v___x_2045_);
lean_ctor_set(v___x_2047_, 9, v___x_2045_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*10, v_val_1860_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*10 + 1, v_val_1860_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*10 + 2, v_val_1860_);
v___x_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v___x_2045_);
v___x_2049_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2050_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2051_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1863_);
v___x_2052_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2053_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_ctor_set(v___x_2053_, 2, v___x_2040_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*3, v___x_1864_);
v___x_2054_ = lean_box(0);
lean_inc_ref(v___y_2014_);
v___x_2055_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2055_, 0, v_env_2031_);
lean_ctor_set(v___x_2055_, 1, v___x_2042_);
lean_ctor_set(v___x_2055_, 2, v___x_2048_);
lean_ctor_set(v___x_2055_, 3, v___x_2041_);
lean_ctor_set(v___x_2055_, 4, v___x_2049_);
lean_ctor_set(v___x_2055_, 5, v___y_2015_);
lean_ctor_set(v___x_2055_, 6, v___x_2050_);
lean_ctor_set(v___x_2055_, 7, v___x_2051_);
lean_ctor_set(v___x_2055_, 8, v___x_2053_);
lean_ctor_set(v___x_2055_, 9, v___y_2014_);
lean_ctor_set(v___x_2055_, 10, v___x_2046_);
lean_ctor_set(v___x_2055_, 11, v___x_2054_);
lean_ctor_set(v___x_2055_, 12, v___x_2046_);
lean_inc_ref(v___y_2019_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc(v___y_2008_);
v___y_1913_ = v___y_2008_;
v___y_1914_ = v___y_2010_;
v___y_1915_ = v___y_2012_;
v___y_1916_ = v___y_2013_;
v___y_1917_ = v___y_2014_;
v___y_1918_ = v___y_2015_;
v___y_1919_ = v___y_2019_;
v___y_1920_ = v___y_2018_;
v___y_1921_ = v___y_2008_;
v___y_1922_ = v___y_2019_;
v___y_1923_ = v___y_2011_;
v___y_1924_ = v___y_2017_;
v___y_1925_ = v___y_2009_;
v___y_1926_ = v___y_2021_;
v___y_1927_ = v___f_2028_;
v___y_1928_ = v___y_2020_;
v___y_1929_ = v___y_2015_;
v___y_1930_ = v___y_2016_;
v___y_1931_ = v___x_2025_;
v_env_1932_ = v_env_2031_;
v_messages_1933_ = v_messages_2032_;
v_scopes_1934_ = v_scopes_2033_;
v_infoState_1935_ = v_infoState_2034_;
v_traceState_1936_ = v_traceState_2035_;
v_snapshotTasks_1937_ = v_snapshotTasks_2036_;
v_codeQualityEntryTasks_1938_ = v_codeQualityEntryTasks_2037_;
v___y_1939_ = v___y_2013_;
v___y_1940_ = v___y_2012_;
v___y_1941_ = v___y_2022_;
v_reportedCmdState_1942_ = v___x_2055_;
goto v___jp_1912_;
}
}
else
{
lean_inc_ref(v___x_2025_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc(v___y_2008_);
v___y_1977_ = v___y_2008_;
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2013_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2018_;
v___y_1984_ = v___y_2019_;
v___y_1985_ = v___y_2008_;
v___y_1986_ = v___y_2019_;
v___y_1987_ = v___y_2011_;
v___y_1988_ = v___y_2017_;
v___y_1989_ = v___y_2009_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___f_2028_;
v___y_1992_ = v___y_2020_;
v___y_1993_ = v___y_2015_;
v___y_1994_ = v___y_2016_;
v___y_1995_ = v___x_2025_;
v___y_1996_ = v___y_2013_;
v___y_1997_ = v___y_2012_;
v___y_1998_ = v___y_2022_;
v_reportedCmdState_1999_ = v___x_2025_;
goto v___jp_1976_;
}
}
}
v___jp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2058_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1862_);
v___x_2059_ = l_IO_CancelToken_new();
v___x_2060_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1863_);
v___x_2061_ = l_Lean_Name_str___override(v___x_1863_, v___x_2060_);
v___x_2062_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2063_ = l_Lean_Name_str___override(v___x_2061_, v___x_2062_);
v___x_2064_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2065_ = l_Lean_Name_str___override(v___x_2063_, v___x_2064_);
v___x_2066_ = l_Lean_Name_str___override(v___x_2065_, v___x_2062_);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = l_Lean_Name_num___override(v___x_2066_, v___x_2067_);
v___x_2069_ = l_Lean_Name_str___override(v___x_2068_, v___x_2062_);
v___x_2070_ = l_Lean_Name_str___override(v___x_2069_, v___x_2064_);
v___x_2071_ = l_Lean_Name_str___override(v___x_2070_, v___x_2062_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2073_ = l_Lean_Name_str___override(v___x_2071_, v___x_2072_);
v___x_2074_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2075_ = l_Lean_Name_str___override(v___x_2073_, v___x_2074_);
v___x_2076_ = l_Lean_Name_toString(v___x_2075_, v___x_1864_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_unsigned_to_nat(32u);
v___x_2079_ = ((size_t)5ULL);
v___x_2080_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2076_, 2);
v___x_2081_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
lean_ctor_set(v___x_2081_, 1, v___x_2058_);
lean_ctor_set(v___x_2081_, 2, v___x_2077_);
lean_ctor_set(v___x_2081_, 3, v___x_2080_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*4, v_val_1860_);
v___x_2082_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2083_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2083_, 0, v___x_2076_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set(v___x_2083_, 2, v___x_2077_);
lean_ctor_set(v___x_2083_, 3, v___x_2080_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*4, v_val_1860_);
lean_inc(v_fst_1865_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_fst_1865_);
v___x_2085_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2084_);
lean_inc_ref(v___x_2059_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2059_);
v___x_2087_ = l_IO_Promise_result_x21___redArg(v_val_1866_);
lean_inc_ref(v___x_2087_);
lean_inc(v___x_2085_);
lean_inc_ref_n(v___x_2084_, 3);
v___x_2088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2084_);
lean_ctor_set(v___x_2088_, 1, v___x_2085_);
lean_ctor_set(v___x_2088_, 2, v___x_2086_);
lean_ctor_set(v___x_2088_, 3, v___x_2087_);
v___x_2089_ = l_IO_Promise_result_x21___redArg(v_val_1867_);
lean_inc_ref(v___x_2089_);
lean_inc_n(v___x_1855_, 3);
v___x_2090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2084_);
lean_ctor_set(v___x_2090_, 1, v___x_1855_);
lean_ctor_set(v___x_2090_, 2, v___x_2077_);
lean_ctor_set(v___x_2090_, 3, v___x_2089_);
v___x_2091_ = l_IO_Promise_result_x21___redArg(v_val_1874_);
lean_inc_ref(v___x_2091_);
v___x_2092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2084_);
lean_ctor_set(v___x_2092_, 1, v___x_1855_);
lean_ctor_set(v___x_2092_, 2, v___x_2077_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
v___x_2093_ = l_IO_Promise_result_x21___redArg(v_val_1856_);
v___x_2094_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2077_);
lean_ctor_set(v___x_2094_, 1, v___x_1855_);
lean_ctor_set(v___x_2094_, 2, v___x_2077_);
lean_ctor_set(v___x_2094_, 3, v___x_2093_);
lean_inc_ref(v___x_2083_);
v___x_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2083_);
lean_ctor_set(v___x_2095_, 1, v___x_2088_);
lean_ctor_set(v___x_2095_, 2, v___x_2090_);
lean_ctor_set(v___x_2095_, 3, v___x_2092_);
lean_ctor_set(v___x_2095_, 4, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2081_);
lean_ctor_set(v___x_2096_, 1, v_fst_1865_);
lean_ctor_set(v___x_2096_, 2, v_snd_1878_);
lean_ctor_set(v___x_2096_, 3, v___x_2095_);
lean_ctor_set(v___x_2096_, 4, v___y_2057_);
v___x_2097_ = lean_io_promise_resolve(v___x_2096_, v_prom_1879_);
if (lean_obj_tag(v_old_x3f_1880_) == 0)
{
v___y_2008_ = v___x_2077_;
v___y_2009_ = v___x_2084_;
v___y_2010_ = v___x_2078_;
v___y_2011_ = v___x_2059_;
v___y_2012_ = v___x_2077_;
v___y_2013_ = v___x_2083_;
v___y_2014_ = v___x_2080_;
v___y_2015_ = v___x_2067_;
v___y_2016_ = v___x_2085_;
v___y_2017_ = v___x_2087_;
v___y_2018_ = v___x_2079_;
v___y_2019_ = v___x_2076_;
v___y_2020_ = v___x_2077_;
v___y_2021_ = v___x_2091_;
v___y_2022_ = v___x_2089_;
v___y_2023_ = v___x_2077_;
goto v___jp_2007_;
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2109_; 
v_val_2098_ = lean_ctor_get(v_old_x3f_1880_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_old_x3f_1880_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2100_ = v_old_x3f_1880_;
v_isShared_2101_ = v_isSharedCheck_2109_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_val_2098_);
lean_dec(v_old_x3f_1880_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2109_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_elabSnap_2102_; lean_object* v_stx_2103_; lean_object* v_elabSnap_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v_elabSnap_2102_ = lean_ctor_get(v_val_2098_, 3);
lean_inc_ref(v_elabSnap_2102_);
v_stx_2103_ = lean_ctor_get(v_val_2098_, 1);
lean_inc(v_stx_2103_);
lean_dec(v_val_2098_);
v_elabSnap_2104_ = lean_ctor_get(v_elabSnap_2102_, 1);
lean_inc_ref(v_elabSnap_2104_);
lean_dec_ref(v_elabSnap_2102_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_stx_2103_);
lean_ctor_set(v___x_2105_, 1, v_elabSnap_2104_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2105_);
v___x_2107_ = v___x_2100_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v___y_2008_ = v___x_2077_;
v___y_2009_ = v___x_2084_;
v___y_2010_ = v___x_2078_;
v___y_2011_ = v___x_2059_;
v___y_2012_ = v___x_2077_;
v___y_2013_ = v___x_2083_;
v___y_2014_ = v___x_2080_;
v___y_2015_ = v___x_2067_;
v___y_2016_ = v___x_2085_;
v___y_2017_ = v___x_2087_;
v___y_2018_ = v___x_2079_;
v___y_2019_ = v___x_2076_;
v___y_2020_ = v___x_2077_;
v___y_2021_ = v___x_2091_;
v___y_2022_ = v___x_2089_;
v___y_2023_ = v___x_2107_;
goto v___jp_2007_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2123_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2127_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2128_, lean_object* v_revCmds_2129_, lean_object* v_fst_2130_, uint8_t v_val_2131_, lean_object* v_a_2132_, lean_object* v_snd_2133_, lean_object* v___x_2134_, uint8_t v___x_2135_, lean_object* v___x_2136_, lean_object* v___f_2137_, lean_object* v___f_2138_, lean_object* v___f_2139_, lean_object* v_pos_2140_, lean_object* v_cmdState_2141_, lean_object* v___x_2142_, lean_object* v_opts_2143_, lean_object* v_prom_2144_, lean_object* v_old_x3f_2145_, lean_object* v_parseCancelTk_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___y_2153_; lean_object* v_snapshotTasks_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v_traceTask_2161_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2185_; lean_object* v___y_2186_; size_t v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v_env_2194_; lean_object* v_messages_2195_; lean_object* v_scopes_2196_; lean_object* v_infoState_2197_; lean_object* v_traceState_2198_; lean_object* v_snapshotTasks_2199_; lean_object* v_codeQualityEntryTasks_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v_reportedCmdState_2216_; lean_object* v___y_2251_; lean_object* v___y_2252_; size_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v_reportedCmdState_2275_; lean_object* v___x_2283_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; size_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v_fst_2414_; lean_object* v_snd_2415_; uint8_t v___x_2427_; 
v___x_2148_ = lean_io_promise_new();
v___x_2149_ = lean_io_promise_new();
v___x_2150_ = lean_io_promise_new();
v___x_2151_ = lean_io_promise_new();
v___x_2283_ = l_Lean_internal_cmdlineSnapshots;
v___x_2427_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2143_, v___x_2283_);
if (v___x_2427_ == 0)
{
lean_inc_ref(v_fst_2130_);
lean_inc(v_fst_2128_);
v_fst_2414_ = v_fst_2128_;
v_snd_2415_ = v_fst_2130_;
goto v___jp_2413_;
}
else
{
uint8_t v___x_2428_; 
lean_inc(v_fst_2128_);
v___x_2428_ = l_Lean_Parser_isTerminalCommand(v_fst_2128_);
if (v___x_2428_ == 0)
{
if (v___x_2427_ == 0)
{
lean_inc_ref(v_fst_2130_);
lean_inc(v_fst_2128_);
v_fst_2414_ = v_fst_2128_;
v_snd_2415_ = v_fst_2130_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2414_ = v___x_2429_;
v_snd_2415_ = v___x_2430_;
goto v___jp_2413_;
}
}
else
{
lean_inc_ref(v_fst_2130_);
lean_inc(v_fst_2128_);
v_fst_2414_ = v_fst_2128_;
v_snd_2415_ = v_fst_2130_;
goto v___jp_2413_;
}
}
v___jp_2152_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2157_);
lean_ctor_set(v___x_2162_, 1, v___y_2160_);
lean_ctor_set(v___x_2162_, 2, v___y_2155_);
lean_ctor_set(v___x_2162_, 3, v_traceTask_2161_);
v___x_2163_ = lean_array_push(v_snapshotTasks_2154_, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___y_2158_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_io_promise_resolve(v___x_2164_, v___x_2151_);
lean_dec(v___x_2151_);
if (lean_obj_tag(v___y_2156_) == 1)
{
lean_object* v_val_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_val_2166_ = lean_ctor_get(v___y_2156_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v___y_2156_, 1);
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_fst_2128_);
lean_ctor_set(v___x_2168_, 1, v_revCmds_2129_);
v___x_2169_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2167_, v_fst_2130_, v___y_2153_, v_val_2166_, v_val_2131_, v___y_2159_, v___x_2168_, v_a_2132_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; 
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_fst_2130_);
lean_dec(v_revCmds_2129_);
lean_dec(v_fst_2128_);
v___x_2170_ = lean_box(0);
return v___x_2170_;
}
}
v___jp_2171_:
{
lean_object* v_snapshotTasks_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_snapshotTasks_2180_ = lean_ctor_get(v___y_2172_, 10);
lean_inc_ref(v_snapshotTasks_2180_);
v___x_2181_ = lean_mk_empty_array_with_capacity(v___y_2173_);
lean_dec(v___y_2173_);
lean_inc_ref(v___y_2177_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___y_2177_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = lean_task_pure(v___x_2182_);
v___y_2153_ = v___y_2172_;
v_snapshotTasks_2154_ = v_snapshotTasks_2180_;
v___y_2155_ = v___y_2174_;
v___y_2156_ = v___y_2175_;
v___y_2157_ = v___y_2176_;
v___y_2158_ = v___y_2177_;
v___y_2159_ = v___y_2179_;
v___y_2160_ = v___y_2178_;
v_traceTask_2161_ = v___x_2183_;
goto v___jp_2152_;
}
v___jp_2184_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_opts_2226_; uint8_t v_hasTrace_2227_; 
v___x_2217_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2195_);
v___x_2218_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2218_, 0, v___y_2209_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_ctor_set(v___x_2218_, 2, v___y_2212_);
lean_ctor_set(v___x_2218_, 3, v_traceState_2198_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*4, v_val_2131_);
v___x_2219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_reportedCmdState_2216_);
lean_ctor_set(v___x_2219_, 2, v_codeQualityEntryTasks_2200_);
v___x_2220_ = lean_io_promise_resolve(v___x_2219_, v___x_2149_);
lean_dec(v___x_2149_);
v___x_2221_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2197_);
lean_inc(v___y_2208_);
v___x_2222_ = l_BaseIO_chainTask___redArg(v___x_2221_, v___y_2202_, v___y_2208_, v___x_2135_);
v___x_2223_ = l_Lean_inheritedTraceOptions;
v___x_2224_ = lean_st_ref_get(v___x_2223_);
v___x_2225_ = l_List_head_x21___redArg(v___x_2136_, v_scopes_2196_);
lean_dec(v_scopes_2196_);
lean_dec_ref(v___x_2136_);
v_opts_2226_ = lean_ctor_get(v___x_2225_, 1);
lean_inc_ref(v_opts_2226_);
lean_dec(v___x_2225_);
v_hasTrace_2227_ = lean_ctor_get_uint8(v_opts_2226_, sizeof(void*)*1);
if (v_hasTrace_2227_ == 0)
{
lean_dec_ref(v_opts_2226_);
lean_dec(v___x_2224_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_snapshotTasks_2199_);
lean_dec_ref(v_env_2194_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2185_);
lean_dec(v_pos_2140_);
lean_dec_ref(v___f_2139_);
lean_dec_ref(v___f_2138_);
lean_dec_ref(v___f_2137_);
lean_dec(v___x_2134_);
v___y_2172_ = v___y_2193_;
v___y_2173_ = v___y_2208_;
v___y_2174_ = v___y_2210_;
v___y_2175_ = v___y_2211_;
v___y_2176_ = v___y_2203_;
v___y_2177_ = v___y_2213_;
v___y_2178_ = v___y_2214_;
v___y_2179_ = v___y_2215_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2224_, v_opts_2226_, v___x_2228_);
lean_dec(v___x_2224_);
if (v___x_2229_ == 0)
{
lean_dec_ref(v_opts_2226_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_snapshotTasks_2199_);
lean_dec_ref(v_env_2194_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2185_);
lean_dec(v_pos_2140_);
lean_dec_ref(v___f_2139_);
lean_dec_ref(v___f_2138_);
lean_dec_ref(v___f_2137_);
lean_dec(v___x_2134_);
v___y_2172_ = v___y_2193_;
v___y_2173_ = v___y_2208_;
v___y_2174_ = v___y_2210_;
v___y_2175_ = v___y_2211_;
v___y_2176_ = v___y_2203_;
v___y_2177_ = v___y_2213_;
v___y_2178_ = v___y_2214_;
v___y_2179_ = v___y_2215_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_inc_n(v___y_2208_, 3);
v___x_2230_ = lean_task_map(v___f_2137_, v___y_2207_, v___y_2208_, v___x_2135_);
lean_inc_n(v___y_2210_, 3);
lean_inc_n(v___y_2204_, 2);
lean_inc_n(v___y_2206_, 2);
v___x_2231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2231_, 0, v___y_2206_);
lean_ctor_set(v___x_2231_, 1, v___y_2204_);
lean_ctor_set(v___x_2231_, 2, v___y_2210_);
lean_ctor_set(v___x_2231_, 3, v___x_2230_);
v___x_2232_ = lean_task_map(v___f_2138_, v___y_2201_, v___y_2208_, v___x_2135_);
v___x_2233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2233_, 0, v___y_2206_);
lean_ctor_set(v___x_2233_, 1, v___y_2204_);
lean_ctor_set(v___x_2233_, 2, v___y_2210_);
lean_ctor_set(v___x_2233_, 3, v___x_2232_);
v___x_2234_ = lean_task_map(v___f_2139_, v___y_2205_, v___y_2208_, v___x_2135_);
v___x_2235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2235_, 0, v___y_2206_);
lean_ctor_set(v___x_2235_, 1, v___y_2204_);
lean_ctor_set(v___x_2235_, 2, v___y_2210_);
lean_ctor_set(v___x_2235_, 3, v___x_2234_);
v___x_2236_ = lean_unsigned_to_nat(3u);
v___x_2237_ = lean_mk_empty_array_with_capacity(v___x_2236_);
v___x_2238_ = lean_array_push(v___x_2237_, v___x_2231_);
v___x_2239_ = lean_array_push(v___x_2238_, v___x_2233_);
v___x_2240_ = lean_array_push(v___x_2239_, v___x_2235_);
v___x_2241_ = l_Array_append___redArg(v___x_2240_, v_snapshotTasks_2199_);
lean_inc_ref(v___y_2213_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___y_2213_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_box_usize(v___y_2187_);
v___x_2244_ = lean_box(v___x_2135_);
v___x_2245_ = lean_box(v_val_2131_);
v___x_2246_ = lean_box(v___x_2229_);
lean_inc_ref(v___x_2242_);
lean_inc_ref(v___y_2186_);
lean_inc_ref(v_a_2132_);
v___f_2247_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2247_, 0, v_a_2132_);
lean_closure_set(v___f_2247_, 1, v_opts_2226_);
lean_closure_set(v___f_2247_, 2, v___x_2134_);
lean_closure_set(v___f_2247_, 3, v___y_2190_);
lean_closure_set(v___f_2247_, 4, v___y_2189_);
lean_closure_set(v___f_2247_, 5, v___x_2243_);
lean_closure_set(v___f_2247_, 6, v___x_2244_);
lean_closure_set(v___f_2247_, 7, v_env_2194_);
lean_closure_set(v___f_2247_, 8, v___y_2186_);
lean_closure_set(v___f_2247_, 9, v___x_2242_);
lean_closure_set(v___f_2247_, 10, v_pos_2140_);
lean_closure_set(v___f_2247_, 11, v___x_2245_);
lean_closure_set(v___f_2247_, 12, v___y_2192_);
lean_closure_set(v___f_2247_, 13, v___y_2185_);
lean_closure_set(v___f_2247_, 14, v___y_2188_);
lean_closure_set(v___f_2247_, 15, v___x_2223_);
lean_closure_set(v___f_2247_, 16, v___y_2191_);
lean_closure_set(v___f_2247_, 17, v___x_2246_);
v___x_2248_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2242_);
v___x_2249_ = lean_io_bind_task(v___x_2248_, v___f_2247_, v___y_2208_, v_val_2131_);
v___y_2153_ = v___y_2193_;
v_snapshotTasks_2154_ = v_snapshotTasks_2199_;
v___y_2155_ = v___y_2210_;
v___y_2156_ = v___y_2211_;
v___y_2157_ = v___y_2203_;
v___y_2158_ = v___y_2213_;
v___y_2159_ = v___y_2215_;
v___y_2160_ = v___y_2214_;
v_traceTask_2161_ = v___x_2249_;
goto v___jp_2152_;
}
}
}
v___jp_2250_:
{
lean_object* v_env_2276_; lean_object* v_messages_2277_; lean_object* v_scopes_2278_; lean_object* v_infoState_2279_; lean_object* v_traceState_2280_; lean_object* v_snapshotTasks_2281_; lean_object* v_codeQualityEntryTasks_2282_; 
v_env_2276_ = lean_ctor_get(v___y_2259_, 0);
lean_inc_ref(v_env_2276_);
v_messages_2277_ = lean_ctor_get(v___y_2259_, 1);
lean_inc_ref(v_messages_2277_);
v_scopes_2278_ = lean_ctor_get(v___y_2259_, 2);
lean_inc(v_scopes_2278_);
v_infoState_2279_ = lean_ctor_get(v___y_2259_, 8);
lean_inc_ref(v_infoState_2279_);
v_traceState_2280_ = lean_ctor_get(v___y_2259_, 9);
lean_inc_ref(v_traceState_2280_);
v_snapshotTasks_2281_ = lean_ctor_get(v___y_2259_, 10);
lean_inc_ref(v_snapshotTasks_2281_);
v_codeQualityEntryTasks_2282_ = lean_ctor_get(v___y_2259_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2282_);
v___y_2185_ = v___y_2252_;
v___y_2186_ = v___y_2251_;
v___y_2187_ = v___y_2253_;
v___y_2188_ = v___y_2254_;
v___y_2189_ = v___y_2255_;
v___y_2190_ = v___y_2256_;
v___y_2191_ = v___y_2257_;
v___y_2192_ = v___y_2258_;
v___y_2193_ = v___y_2259_;
v_env_2194_ = v_env_2276_;
v_messages_2195_ = v_messages_2277_;
v_scopes_2196_ = v_scopes_2278_;
v_infoState_2197_ = v_infoState_2279_;
v_traceState_2198_ = v_traceState_2280_;
v_snapshotTasks_2199_ = v_snapshotTasks_2281_;
v_codeQualityEntryTasks_2200_ = v_codeQualityEntryTasks_2282_;
v___y_2201_ = v___y_2260_;
v___y_2202_ = v___y_2261_;
v___y_2203_ = v___y_2262_;
v___y_2204_ = v___y_2263_;
v___y_2205_ = v___y_2264_;
v___y_2206_ = v___y_2265_;
v___y_2207_ = v___y_2266_;
v___y_2208_ = v___y_2267_;
v___y_2209_ = v___y_2268_;
v___y_2210_ = v___y_2269_;
v___y_2211_ = v___y_2270_;
v___y_2212_ = v___y_2271_;
v___y_2213_ = v___y_2272_;
v___y_2214_ = v___y_2273_;
v___y_2215_ = v___y_2274_;
v_reportedCmdState_2216_ = v_reportedCmdState_2275_;
goto v___jp_2184_;
}
v___jp_2284_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___f_2307_; uint8_t v___x_2308_; 
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___y_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2148_);
lean_inc_ref(v___y_2286_);
lean_inc_n(v_pos_2140_, 2);
lean_inc(v_revCmds_2129_);
lean_inc(v_fst_2128_);
v___x_2304_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2128_, v_revCmds_2129_, v_cmdState_2141_, v_pos_2140_, v___x_2303_, v___y_2286_, v_a_2132_);
v___x_2305_ = lean_box(v_val_2131_);
v___x_2306_ = lean_box(v___x_2135_);
lean_inc_ref(v_a_2132_);
lean_inc(v___y_2293_);
lean_inc_ref(v___x_2136_);
lean_inc_ref(v___x_2304_);
lean_inc_ref(v___y_2289_);
lean_inc_ref(v___y_2296_);
v___f_2307_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2307_, 0, v___y_2296_);
lean_closure_set(v___f_2307_, 1, v___y_2289_);
lean_closure_set(v___f_2307_, 2, v___x_2305_);
lean_closure_set(v___f_2307_, 3, v___x_2150_);
lean_closure_set(v___f_2307_, 4, v___x_2304_);
lean_closure_set(v___f_2307_, 5, v___x_2136_);
lean_closure_set(v___f_2307_, 6, v___y_2293_);
lean_closure_set(v___f_2307_, 7, v___x_2306_);
lean_closure_set(v___f_2307_, 8, v_a_2132_);
lean_closure_set(v___f_2307_, 9, v_pos_2140_);
lean_closure_set(v___f_2307_, 10, v___x_2142_);
v___x_2308_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2143_, v___x_2283_);
if (v___x_2308_ == 0)
{
lean_inc_ref(v___x_2304_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2294_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2287_);
v___y_2251_ = v___y_2289_;
v___y_2252_ = v___y_2287_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v___y_2255_ = v___y_2292_;
v___y_2256_ = v___y_2293_;
v___y_2257_ = v___y_2294_;
v___y_2258_ = v___y_2296_;
v___y_2259_ = v___x_2304_;
v___y_2260_ = v___y_2297_;
v___y_2261_ = v___f_2307_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2288_;
v___y_2264_ = v___y_2299_;
v___y_2265_ = v___y_2285_;
v___y_2266_ = v___y_2295_;
v___y_2267_ = v___y_2293_;
v___y_2268_ = v___y_2296_;
v___y_2269_ = v___y_2294_;
v___y_2270_ = v___y_2300_;
v___y_2271_ = v___y_2287_;
v___y_2272_ = v___y_2291_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2286_;
v_reportedCmdState_2275_ = v___x_2304_;
goto v___jp_2250_;
}
else
{
uint8_t v___x_2309_; 
lean_inc(v_fst_2128_);
v___x_2309_ = l_Lean_Parser_isTerminalCommand(v_fst_2128_);
if (v___x_2309_ == 0)
{
if (v___x_2308_ == 0)
{
lean_inc_ref(v___x_2304_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2294_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2287_);
v___y_2251_ = v___y_2289_;
v___y_2252_ = v___y_2287_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v___y_2255_ = v___y_2292_;
v___y_2256_ = v___y_2293_;
v___y_2257_ = v___y_2294_;
v___y_2258_ = v___y_2296_;
v___y_2259_ = v___x_2304_;
v___y_2260_ = v___y_2297_;
v___y_2261_ = v___f_2307_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2288_;
v___y_2264_ = v___y_2299_;
v___y_2265_ = v___y_2285_;
v___y_2266_ = v___y_2295_;
v___y_2267_ = v___y_2293_;
v___y_2268_ = v___y_2296_;
v___y_2269_ = v___y_2294_;
v___y_2270_ = v___y_2300_;
v___y_2271_ = v___y_2287_;
v___y_2272_ = v___y_2291_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2286_;
v_reportedCmdState_2275_ = v___x_2304_;
goto v___jp_2250_;
}
else
{
lean_object* v_env_2310_; lean_object* v_messages_2311_; lean_object* v_scopes_2312_; lean_object* v_infoState_2313_; lean_object* v_traceState_2314_; lean_object* v_snapshotTasks_2315_; lean_object* v_codeQualityEntryTasks_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_env_2310_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_ref_n(v_env_2310_, 2);
v_messages_2311_ = lean_ctor_get(v___x_2304_, 1);
lean_inc_ref(v_messages_2311_);
v_scopes_2312_ = lean_ctor_get(v___x_2304_, 2);
lean_inc(v_scopes_2312_);
v_infoState_2313_ = lean_ctor_get(v___x_2304_, 8);
lean_inc_ref(v_infoState_2313_);
v_traceState_2314_ = lean_ctor_get(v___x_2304_, 9);
lean_inc_ref(v_traceState_2314_);
v_snapshotTasks_2315_ = lean_ctor_get(v___x_2304_, 10);
lean_inc_ref(v_snapshotTasks_2315_);
v_codeQualityEntryTasks_2316_ = lean_ctor_get(v___x_2304_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2316_);
v___x_2317_ = lean_mk_empty_array_with_capacity(v___y_2292_);
lean_inc_ref(v___x_2317_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_inc_n(v___y_2293_, 4);
v___x_2319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2317_);
lean_ctor_set(v___x_2319_, 2, v___y_2293_);
lean_ctor_set(v___x_2319_, 3, v___y_2293_);
lean_ctor_set_usize(v___x_2319_, 4, v___y_2290_);
v___x_2320_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2319_, 2);
v___x_2321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2319_);
lean_ctor_set(v___x_2321_, 2, v___x_2320_);
v___x_2322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2323_ = l_Lean_Options_empty;
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_mk_empty_array_with_capacity(v___y_2293_);
lean_inc_ref_n(v___x_2325_, 3);
lean_inc_n(v___x_2134_, 2);
v___x_2326_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2326_, 0, v___x_2322_);
lean_ctor_set(v___x_2326_, 1, v___x_2323_);
lean_ctor_set(v___x_2326_, 2, v___x_2134_);
lean_ctor_set(v___x_2326_, 3, v___x_2324_);
lean_ctor_set(v___x_2326_, 4, v___x_2324_);
lean_ctor_set(v___x_2326_, 5, v___x_2325_);
lean_ctor_set(v___x_2326_, 6, v___x_2325_);
lean_ctor_set(v___x_2326_, 7, v___x_2324_);
lean_ctor_set(v___x_2326_, 8, v___x_2324_);
lean_ctor_set(v___x_2326_, 9, v___x_2324_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*10, v_val_2131_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*10 + 1, v_val_2131_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*10 + 2, v_val_2131_);
v___x_2327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2324_);
v___x_2328_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2329_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2330_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2134_);
v___x_2331_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2332_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
lean_ctor_set(v___x_2332_, 2, v___x_2319_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*3, v___x_2135_);
v___x_2333_ = lean_box(0);
lean_inc_ref(v___y_2289_);
v___x_2334_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2334_, 0, v_env_2310_);
lean_ctor_set(v___x_2334_, 1, v___x_2321_);
lean_ctor_set(v___x_2334_, 2, v___x_2327_);
lean_ctor_set(v___x_2334_, 3, v___x_2320_);
lean_ctor_set(v___x_2334_, 4, v___x_2328_);
lean_ctor_set(v___x_2334_, 5, v___y_2293_);
lean_ctor_set(v___x_2334_, 6, v___x_2329_);
lean_ctor_set(v___x_2334_, 7, v___x_2330_);
lean_ctor_set(v___x_2334_, 8, v___x_2332_);
lean_ctor_set(v___x_2334_, 9, v___y_2289_);
lean_ctor_set(v___x_2334_, 10, v___x_2325_);
lean_ctor_set(v___x_2334_, 11, v___x_2333_);
lean_ctor_set(v___x_2334_, 12, v___x_2325_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2287_);
v___y_2185_ = v___y_2287_;
v___y_2186_ = v___y_2289_;
v___y_2187_ = v___y_2290_;
v___y_2188_ = v___y_2291_;
v___y_2189_ = v___y_2292_;
v___y_2190_ = v___y_2293_;
v___y_2191_ = v___y_2294_;
v___y_2192_ = v___y_2296_;
v___y_2193_ = v___x_2304_;
v_env_2194_ = v_env_2310_;
v_messages_2195_ = v_messages_2311_;
v_scopes_2196_ = v_scopes_2312_;
v_infoState_2197_ = v_infoState_2313_;
v_traceState_2198_ = v_traceState_2314_;
v_snapshotTasks_2199_ = v_snapshotTasks_2315_;
v_codeQualityEntryTasks_2200_ = v_codeQualityEntryTasks_2316_;
v___y_2201_ = v___y_2297_;
v___y_2202_ = v___f_2307_;
v___y_2203_ = v___y_2298_;
v___y_2204_ = v___y_2288_;
v___y_2205_ = v___y_2299_;
v___y_2206_ = v___y_2285_;
v___y_2207_ = v___y_2295_;
v___y_2208_ = v___y_2293_;
v___y_2209_ = v___y_2296_;
v___y_2210_ = v___y_2294_;
v___y_2211_ = v___y_2300_;
v___y_2212_ = v___y_2287_;
v___y_2213_ = v___y_2291_;
v___y_2214_ = v___y_2301_;
v___y_2215_ = v___y_2286_;
v_reportedCmdState_2216_ = v___x_2334_;
goto v___jp_2184_;
}
}
else
{
lean_inc_ref(v___x_2304_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2294_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2287_);
v___y_2251_ = v___y_2289_;
v___y_2252_ = v___y_2287_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v___y_2255_ = v___y_2292_;
v___y_2256_ = v___y_2293_;
v___y_2257_ = v___y_2294_;
v___y_2258_ = v___y_2296_;
v___y_2259_ = v___x_2304_;
v___y_2260_ = v___y_2297_;
v___y_2261_ = v___f_2307_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2288_;
v___y_2264_ = v___y_2299_;
v___y_2265_ = v___y_2285_;
v___y_2266_ = v___y_2295_;
v___y_2267_ = v___y_2293_;
v___y_2268_ = v___y_2296_;
v___y_2269_ = v___y_2294_;
v___y_2270_ = v___y_2300_;
v___y_2271_ = v___y_2287_;
v___y_2272_ = v___y_2291_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2286_;
v_reportedCmdState_2275_ = v___x_2304_;
goto v___jp_2250_;
}
}
}
v___jp_2335_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2341_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2133_);
v___x_2342_ = l_IO_CancelToken_new();
v___x_2343_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2134_);
v___x_2344_ = l_Lean_Name_str___override(v___x_2134_, v___x_2343_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2346_ = l_Lean_Name_str___override(v___x_2344_, v___x_2345_);
v___x_2347_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2348_ = l_Lean_Name_str___override(v___x_2346_, v___x_2347_);
v___x_2349_ = l_Lean_Name_str___override(v___x_2348_, v___x_2345_);
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = l_Lean_Name_num___override(v___x_2349_, v___x_2350_);
v___x_2352_ = l_Lean_Name_str___override(v___x_2351_, v___x_2345_);
v___x_2353_ = l_Lean_Name_str___override(v___x_2352_, v___x_2347_);
v___x_2354_ = l_Lean_Name_str___override(v___x_2353_, v___x_2345_);
v___x_2355_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2356_ = l_Lean_Name_str___override(v___x_2354_, v___x_2355_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2358_ = l_Lean_Name_str___override(v___x_2356_, v___x_2357_);
v___x_2359_ = l_Lean_Name_toString(v___x_2358_, v___x_2135_);
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_unsigned_to_nat(32u);
v___x_2362_ = lean_mk_empty_array_with_capacity(v___x_2361_);
lean_dec_ref(v___x_2362_);
v___x_2363_ = ((size_t)5ULL);
v___x_2364_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2359_, 2);
v___x_2365_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2365_, 0, v___x_2359_);
lean_ctor_set(v___x_2365_, 1, v___x_2341_);
lean_ctor_set(v___x_2365_, 2, v___x_2360_);
lean_ctor_set(v___x_2365_, 3, v___x_2364_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*4, v_val_2131_);
v___x_2366_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2367_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2359_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
lean_ctor_set(v___x_2367_, 2, v___x_2360_);
lean_ctor_set(v___x_2367_, 3, v___x_2364_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*4, v_val_2131_);
lean_inc(v___y_2337_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___y_2337_);
v___x_2369_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2368_);
lean_inc_ref(v___x_2342_);
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2342_);
v___x_2371_ = l_IO_Promise_result_x21___redArg(v___x_2148_);
lean_inc_ref(v___x_2371_);
lean_inc(v___x_2369_);
lean_inc_ref_n(v___x_2368_, 3);
v___x_2372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2368_);
lean_ctor_set(v___x_2372_, 1, v___x_2369_);
lean_ctor_set(v___x_2372_, 2, v___x_2370_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
v___x_2373_ = l_IO_Promise_result_x21___redArg(v___x_2149_);
lean_inc_ref(v___x_2373_);
lean_inc_n(v___y_2339_, 3);
v___x_2374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2368_);
lean_ctor_set(v___x_2374_, 1, v___y_2339_);
lean_ctor_set(v___x_2374_, 2, v___x_2360_);
lean_ctor_set(v___x_2374_, 3, v___x_2373_);
v___x_2375_ = l_IO_Promise_result_x21___redArg(v___x_2150_);
lean_inc_ref(v___x_2375_);
v___x_2376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2368_);
lean_ctor_set(v___x_2376_, 1, v___y_2339_);
lean_ctor_set(v___x_2376_, 2, v___x_2360_);
lean_ctor_set(v___x_2376_, 3, v___x_2375_);
v___x_2377_ = l_IO_Promise_result_x21___redArg(v___x_2151_);
v___x_2378_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2360_);
lean_ctor_set(v___x_2378_, 1, v___y_2339_);
lean_ctor_set(v___x_2378_, 2, v___x_2360_);
lean_ctor_set(v___x_2378_, 3, v___x_2377_);
lean_inc_ref(v___x_2367_);
v___x_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2367_);
lean_ctor_set(v___x_2379_, 1, v___x_2372_);
lean_ctor_set(v___x_2379_, 2, v___x_2374_);
lean_ctor_set(v___x_2379_, 3, v___x_2376_);
lean_ctor_set(v___x_2379_, 4, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2365_);
lean_ctor_set(v___x_2380_, 1, v___y_2337_);
lean_ctor_set(v___x_2380_, 2, v___y_2338_);
lean_ctor_set(v___x_2380_, 3, v___x_2379_);
lean_ctor_set(v___x_2380_, 4, v___y_2340_);
v___x_2381_ = lean_io_promise_resolve(v___x_2380_, v_prom_2144_);
if (lean_obj_tag(v_old_x3f_2145_) == 0)
{
v___y_2285_ = v___x_2368_;
v___y_2286_ = v___x_2342_;
v___y_2287_ = v___x_2360_;
v___y_2288_ = v___x_2369_;
v___y_2289_ = v___x_2364_;
v___y_2290_ = v___x_2363_;
v___y_2291_ = v___x_2367_;
v___y_2292_ = v___x_2361_;
v___y_2293_ = v___x_2350_;
v___y_2294_ = v___x_2360_;
v___y_2295_ = v___x_2371_;
v___y_2296_ = v___x_2359_;
v___y_2297_ = v___x_2373_;
v___y_2298_ = v___x_2360_;
v___y_2299_ = v___x_2375_;
v___y_2300_ = v___y_2336_;
v___y_2301_ = v___y_2339_;
v___y_2302_ = v___x_2360_;
goto v___jp_2284_;
}
else
{
lean_object* v_val_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2393_; 
v_val_2382_ = lean_ctor_get(v_old_x3f_2145_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_old_x3f_2145_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2384_ = v_old_x3f_2145_;
v_isShared_2385_ = v_isSharedCheck_2393_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_val_2382_);
lean_dec(v_old_x3f_2145_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2393_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_elabSnap_2386_; lean_object* v_stx_2387_; lean_object* v_elabSnap_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v_elabSnap_2386_ = lean_ctor_get(v_val_2382_, 3);
lean_inc_ref(v_elabSnap_2386_);
v_stx_2387_ = lean_ctor_get(v_val_2382_, 1);
lean_inc(v_stx_2387_);
lean_dec(v_val_2382_);
v_elabSnap_2388_ = lean_ctor_get(v_elabSnap_2386_, 1);
lean_inc_ref(v_elabSnap_2388_);
lean_dec_ref(v_elabSnap_2386_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_stx_2387_);
lean_ctor_set(v___x_2389_, 1, v_elabSnap_2388_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2389_);
v___x_2391_ = v___x_2384_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
v___y_2285_ = v___x_2368_;
v___y_2286_ = v___x_2342_;
v___y_2287_ = v___x_2360_;
v___y_2288_ = v___x_2369_;
v___y_2289_ = v___x_2364_;
v___y_2290_ = v___x_2363_;
v___y_2291_ = v___x_2367_;
v___y_2292_ = v___x_2361_;
v___y_2293_ = v___x_2350_;
v___y_2294_ = v___x_2360_;
v___y_2295_ = v___x_2371_;
v___y_2296_ = v___x_2359_;
v___y_2297_ = v___x_2373_;
v___y_2298_ = v___x_2360_;
v___y_2299_ = v___x_2375_;
v___y_2300_ = v___y_2336_;
v___y_2301_ = v___y_2339_;
v___y_2302_ = v___x_2391_;
goto v___jp_2284_;
}
}
}
}
v___jp_2394_:
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2397_);
lean_inc(v_fst_2128_);
v___x_2399_ = l_Lean_Parser_isTerminalCommand(v_fst_2128_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; lean_object* v_toProcessingContext_2401_; lean_object* v_pos_2402_; lean_object* v_endPos_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2400_ = lean_io_promise_new();
v_toProcessingContext_2401_ = lean_ctor_get(v_a_2132_, 0);
v_pos_2402_ = lean_ctor_get(v_fst_2130_, 0);
v_endPos_2403_ = lean_ctor_get(v_toProcessingContext_2401_, 3);
lean_inc(v___x_2400_);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2400_);
v___x_2405_ = lean_box(0);
lean_inc(v_endPos_2403_);
lean_inc(v_pos_2402_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_pos_2402_);
lean_ctor_set(v___x_2406_, 1, v_endPos_2403_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_parseCancelTk_2146_);
v___x_2409_ = l_IO_Promise_result_x21___redArg(v___x_2400_);
lean_dec(v___x_2400_);
v___x_2410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2405_);
lean_ctor_set(v___x_2410_, 1, v___x_2407_);
lean_ctor_set(v___x_2410_, 2, v___x_2408_);
lean_ctor_set(v___x_2410_, 3, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
v___y_2336_ = v___x_2404_;
v___y_2337_ = v___y_2395_;
v___y_2338_ = v___y_2396_;
v___y_2339_ = v___x_2398_;
v___y_2340_ = v___x_2411_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2412_; 
lean_dec_ref(v_parseCancelTk_2146_);
v___x_2412_ = lean_box(0);
v___y_2336_ = v___x_2412_;
v___y_2337_ = v___y_2395_;
v___y_2338_ = v___y_2396_;
v___y_2339_ = v___x_2398_;
v___y_2340_ = v___x_2412_;
goto v___jp_2335_;
}
}
v___jp_2413_:
{
lean_object* v___x_2416_; 
lean_inc(v_fst_2128_);
v___x_2416_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2128_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_box(0);
v___y_2395_ = v_fst_2414_;
v___y_2396_ = v_snd_2415_;
v___y_2397_ = v___x_2417_;
goto v___jp_2394_;
}
else
{
lean_object* v_val_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_val_2418_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v___x_2416_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_val_2418_);
lean_dec(v___x_2416_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_inc(v_val_2418_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_val_2418_);
lean_ctor_set(v___x_2422_, 1, v_val_2418_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
v___y_2395_ = v_fst_2414_;
v___y_2396_ = v_snd_2415_;
v___y_2397_ = v___x_2424_;
goto v___jp_2394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2431_ = _args[0];
lean_object* v_revCmds_2432_ = _args[1];
lean_object* v_fst_2433_ = _args[2];
lean_object* v_val_2434_ = _args[3];
lean_object* v_a_2435_ = _args[4];
lean_object* v_snd_2436_ = _args[5];
lean_object* v___x_2437_ = _args[6];
lean_object* v___x_2438_ = _args[7];
lean_object* v___x_2439_ = _args[8];
lean_object* v___f_2440_ = _args[9];
lean_object* v___f_2441_ = _args[10];
lean_object* v___f_2442_ = _args[11];
lean_object* v_pos_2443_ = _args[12];
lean_object* v_cmdState_2444_ = _args[13];
lean_object* v___x_2445_ = _args[14];
lean_object* v_opts_2446_ = _args[15];
lean_object* v_prom_2447_ = _args[16];
lean_object* v_old_x3f_2448_ = _args[17];
lean_object* v_parseCancelTk_2449_ = _args[18];
lean_object* v___y_2450_ = _args[19];
_start:
{
uint8_t v_val_37622__boxed_2451_; uint8_t v___x_37625__boxed_2452_; lean_object* v_res_2453_; 
v_val_37622__boxed_2451_ = lean_unbox(v_val_2434_);
v___x_37625__boxed_2452_ = lean_unbox(v___x_2438_);
v_res_2453_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2431_, v_revCmds_2432_, v_fst_2433_, v_val_37622__boxed_2451_, v_a_2435_, v_snd_2436_, v___x_2437_, v___x_37625__boxed_2452_, v___x_2439_, v___f_2440_, v___f_2441_, v___f_2442_, v_pos_2443_, v_cmdState_2444_, v___x_2445_, v_opts_2446_, v_prom_2447_, v_old_x3f_2448_, v_parseCancelTk_2449_);
lean_dec(v_prom_2447_);
lean_dec_ref(v_opts_2446_);
lean_dec_ref(v_a_2435_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2456_, lean_object* v_parserState_2457_, lean_object* v_cmdState_2458_, lean_object* v_prom_2459_, uint8_t v_sync_2460_, lean_object* v_parseCancelTk_2461_, lean_object* v_revCmds_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v___y_2468_; lean_object* v_toSnapshot_2470_; lean_object* v_stx_2471_; lean_object* v_parserState_2472_; lean_object* v_elabSnap_2473_; lean_object* v_val_2474_; lean_object* v_newParserState_2475_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; uint8_t v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; uint8_t v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v_fst_2551_; lean_object* v_snd_2552_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___x_2647_; 
v___f_2506_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2507_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2508_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2509_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2510_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2647_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2456_) == 1)
{
lean_object* v_val_2680_; lean_object* v_nextCmdSnap_x3f_2681_; 
v_val_2680_ = lean_ctor_get(v_old_x3f_2456_, 0);
v_nextCmdSnap_x3f_2681_ = lean_ctor_get(v_val_2680_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2681_) == 0)
{
goto v___jp_2648_;
}
else
{
lean_object* v_toSnapshot_2682_; lean_object* v_stx_2683_; lean_object* v_parserState_2684_; lean_object* v_elabSnap_2685_; lean_object* v_val_2686_; lean_object* v___x_2687_; 
v_toSnapshot_2682_ = lean_ctor_get(v_val_2680_, 0);
v_stx_2683_ = lean_ctor_get(v_val_2680_, 1);
v_parserState_2684_ = lean_ctor_get(v_val_2680_, 2);
v_elabSnap_2685_ = lean_ctor_get(v_val_2680_, 3);
v_val_2686_ = lean_ctor_get(v_nextCmdSnap_x3f_2681_, 0);
lean_inc(v_val_2686_);
v___x_2687_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2686_);
if (lean_obj_tag(v___x_2687_) == 1)
{
lean_object* v_val_2688_; lean_object* v_nextCmdSnap_x3f_2689_; 
v_val_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v_nextCmdSnap_x3f_2689_ = lean_ctor_get(v_val_2688_, 4);
lean_inc(v_nextCmdSnap_x3f_2689_);
lean_dec(v_val_2688_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2689_) == 0)
{
goto v___jp_2648_;
}
else
{
lean_object* v_val_2690_; lean_object* v___x_2691_; 
v_val_2690_ = lean_ctor_get(v_nextCmdSnap_x3f_2689_, 0);
lean_inc(v_val_2690_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2689_, 1);
v___x_2691_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2690_);
if (lean_obj_tag(v___x_2691_) == 1)
{
lean_object* v_val_2692_; lean_object* v_parserState_2693_; lean_object* v_pos_2694_; uint8_t v___x_2695_; 
v_val_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_val_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v_parserState_2693_ = lean_ctor_get(v_val_2692_, 2);
lean_inc_ref(v_parserState_2693_);
lean_dec(v_val_2692_);
v_pos_2694_ = lean_ctor_get(v_parserState_2693_, 0);
lean_inc(v_pos_2694_);
lean_dec_ref(v_parserState_2693_);
v___x_2695_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2694_, v_a_2463_);
lean_dec(v_pos_2694_);
if (v___x_2695_ == 0)
{
goto v___jp_2648_;
}
else
{
lean_inc(v_val_2686_);
lean_inc_ref(v_elabSnap_2685_);
lean_inc_ref_n(v_parserState_2684_, 2);
lean_inc(v_stx_2683_);
lean_inc_ref(v_toSnapshot_2682_);
lean_dec_ref_known(v_old_x3f_2456_, 1);
lean_dec_ref(v_parseCancelTk_2461_);
lean_dec_ref(v_cmdState_2458_);
lean_dec_ref(v_parserState_2457_);
v_toSnapshot_2470_ = v_toSnapshot_2682_;
v_stx_2471_ = v_stx_2683_;
v_parserState_2472_ = v_parserState_2684_;
v_elabSnap_2473_ = v_elabSnap_2685_;
v_val_2474_ = v_val_2686_;
v_newParserState_2475_ = v_parserState_2684_;
goto v___jp_2469_;
}
}
else
{
lean_dec(v___x_2691_);
goto v___jp_2648_;
}
}
}
else
{
lean_dec(v___x_2687_);
goto v___jp_2648_;
}
}
}
else
{
goto v___jp_2648_;
}
v___jp_2465_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_box(0);
return v___x_2466_;
}
v___jp_2467_:
{
goto v___jp_2465_;
}
v___jp_2469_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_resultSnap_2478_; lean_object* v_task_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2502_; 
v___x_2476_ = lean_io_promise_new();
v___x_2477_ = l_IO_CancelToken_new();
v_resultSnap_2478_ = lean_ctor_get(v_elabSnap_2473_, 2);
lean_inc_ref(v_resultSnap_2478_);
v_task_2479_ = lean_ctor_get(v_resultSnap_2478_, 3);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_resultSnap_2478_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; lean_object* v_unused_2504_; lean_object* v_unused_2505_; 
v_unused_2503_ = lean_ctor_get(v_resultSnap_2478_, 2);
lean_dec(v_unused_2503_);
v_unused_2504_ = lean_ctor_get(v_resultSnap_2478_, 1);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_resultSnap_2478_, 0);
lean_dec(v_unused_2505_);
v___x_2481_ = v_resultSnap_2478_;
v_isShared_2482_ = v_isSharedCheck_2502_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_task_2479_);
lean_dec(v_resultSnap_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2502_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v_toProcessingContext_2488_; lean_object* v_pos_2489_; lean_object* v_endPos_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2483_ = lean_box(v_sync_2460_);
lean_inc_ref(v_a_2463_);
lean_inc_ref(v___x_2477_);
lean_inc(v___x_2476_);
lean_inc_ref(v_newParserState_2475_);
lean_inc(v_stx_2471_);
v___f_2484_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2484_, 0, v_val_2474_);
lean_closure_set(v___f_2484_, 1, v_stx_2471_);
lean_closure_set(v___f_2484_, 2, v_revCmds_2462_);
lean_closure_set(v___f_2484_, 3, v_newParserState_2475_);
lean_closure_set(v___f_2484_, 4, v___x_2476_);
lean_closure_set(v___f_2484_, 5, v___x_2483_);
lean_closure_set(v___f_2484_, 6, v___x_2477_);
lean_closure_set(v___f_2484_, 7, v_a_2463_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = 1;
v___x_2487_ = l_BaseIO_chainTask___redArg(v_task_2479_, v___f_2484_, v___x_2485_, v___x_2486_);
v_toProcessingContext_2488_ = lean_ctor_get(v_a_2463_, 0);
v_pos_2489_ = lean_ctor_get(v_newParserState_2475_, 0);
lean_inc(v_pos_2489_);
lean_dec_ref(v_newParserState_2475_);
v_endPos_2490_ = lean_ctor_get(v_toProcessingContext_2488_, 3);
v___x_2491_ = lean_box(0);
lean_inc(v_endPos_2490_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v_pos_2489_);
lean_ctor_set(v___x_2492_, 1, v_endPos_2490_);
v___x_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2477_);
v___x_2495_ = l_IO_Promise_result_x21___redArg(v___x_2476_);
lean_dec(v___x_2476_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 3, v___x_2495_);
lean_ctor_set(v___x_2481_, 2, v___x_2494_);
lean_ctor_set(v___x_2481_, 1, v___x_2493_);
lean_ctor_set(v___x_2481_, 0, v___x_2491_);
v___x_2497_ = v___x_2481_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2499_, 0, v_toSnapshot_2470_);
lean_ctor_set(v___x_2499_, 1, v_stx_2471_);
lean_ctor_set(v___x_2499_, 2, v_parserState_2472_);
lean_ctor_set(v___x_2499_, 3, v_elabSnap_2473_);
lean_ctor_set(v___x_2499_, 4, v___x_2498_);
v___x_2500_ = lean_io_promise_resolve(v___x_2499_, v_prom_2459_);
lean_dec(v_prom_2459_);
return v___x_2500_;
}
}
}
v___jp_2511_:
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2528_);
v___x_2530_ = l_Lean_Parser_isTerminalCommand(v___y_2522_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_io_promise_new();
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
v___x_2533_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2529_, v___y_2520_, v___y_2517_, v_revCmds_2462_, v___y_2512_, v___y_2515_, v_a_2463_, v___y_2524_, v___y_2521_, v___y_2518_, v___y_2514_, v___y_2526_, v___y_2516_, v___x_2509_, v___f_2508_, v___f_2507_, v___f_2506_, v___y_2527_, v_cmdState_2458_, v___y_2525_, v___x_2510_, v___y_2513_, v___y_2523_, v___y_2519_, v_prom_2459_, v_old_x3f_2456_, v_parseCancelTk_2461_, v___x_2532_);
lean_dec(v_prom_2459_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2516_);
lean_dec(v___y_2520_);
v___y_2468_ = v___x_2533_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_box(0);
v___x_2535_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2529_, v___y_2520_, v___y_2517_, v_revCmds_2462_, v___y_2512_, v___y_2515_, v_a_2463_, v___y_2524_, v___y_2521_, v___y_2518_, v___y_2514_, v___y_2526_, v___y_2516_, v___x_2509_, v___f_2508_, v___f_2507_, v___f_2506_, v___y_2527_, v_cmdState_2458_, v___y_2525_, v___x_2510_, v___y_2513_, v___y_2523_, v___y_2519_, v_prom_2459_, v_old_x3f_2456_, v_parseCancelTk_2461_, v___x_2534_);
lean_dec(v_prom_2459_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2516_);
lean_dec(v___y_2520_);
v___y_2468_ = v___x_2535_;
goto v___jp_2467_;
}
}
v___jp_2536_:
{
lean_object* v___x_2553_; 
lean_inc(v___y_2550_);
v___x_2553_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2550_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_box(0);
v___y_2512_ = v___y_2537_;
v___y_2513_ = v___y_2538_;
v___y_2514_ = v_fst_2551_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v___y_2541_;
v___y_2518_ = v___y_2542_;
v___y_2519_ = v_snd_2552_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v___y_2544_;
v___y_2522_ = v___y_2550_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___x_2554_;
goto v___jp_2511_;
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
v_val_2555_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2557_ = v___x_2553_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_val_2555_);
lean_dec(v___x_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_inc(v_val_2555_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_val_2555_);
lean_ctor_set(v___x_2559_, 1, v_val_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
v___y_2512_ = v___y_2537_;
v___y_2513_ = v___y_2538_;
v___y_2514_ = v_fst_2551_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v___y_2541_;
v___y_2518_ = v___y_2542_;
v___y_2519_ = v_snd_2552_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v___y_2544_;
v___y_2522_ = v___y_2550_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___x_2561_;
goto v___jp_2511_;
}
}
}
}
v___jp_2564_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2569_ = l_Lean_Name_str___override(v___y_2566_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2571_ = l_Lean_Name_str___override(v___x_2569_, v___x_2570_);
v___x_2572_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2573_ = l_Lean_Name_str___override(v___x_2571_, v___x_2572_);
v___x_2574_ = l_Lean_Name_str___override(v___x_2573_, v___x_2570_);
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = l_Lean_Name_num___override(v___x_2574_, v___x_2575_);
v___x_2577_ = l_Lean_Name_str___override(v___x_2576_, v___x_2570_);
v___x_2578_ = l_Lean_Name_str___override(v___x_2577_, v___x_2572_);
v___x_2579_ = l_Lean_Name_str___override(v___x_2578_, v___x_2570_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2581_ = l_Lean_Name_str___override(v___x_2579_, v___x_2580_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2583_ = l_Lean_Name_str___override(v___x_2581_, v___x_2582_);
v___x_2584_ = l_Lean_Name_toString(v___x_2583_, v___y_2567_);
v___x_2585_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2588_ = 0;
v___x_2589_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2584_);
lean_ctor_set(v___x_2589_, 1, v___x_2585_);
lean_ctor_set(v___x_2589_, 2, v___x_2586_);
lean_ctor_set(v___x_2589_, 3, v___x_2587_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*4, v___x_2588_);
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2592_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2589_, 3);
v___x_2593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2589_);
lean_ctor_set(v___x_2593_, 1, v_cmdState_2458_);
lean_ctor_set(v___x_2593_, 2, v___x_2592_);
v___x_2594_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2586_, v___x_2593_);
v___x_2595_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2586_, v___x_2589_);
v___x_2596_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2589_);
lean_ctor_set(v___x_2597_, 1, v___x_2591_);
lean_ctor_set(v___x_2597_, 2, v___x_2594_);
lean_ctor_set(v___x_2597_, 3, v___x_2595_);
lean_ctor_set(v___x_2597_, 4, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2589_);
lean_ctor_set(v___x_2598_, 1, v___x_2590_);
lean_ctor_set(v___x_2598_, 2, v___y_2565_);
lean_ctor_set(v___x_2598_, 3, v___x_2597_);
lean_ctor_set(v___x_2598_, 4, v___x_2586_);
v___x_2599_ = lean_io_promise_resolve(v___x_2598_, v_prom_2459_);
lean_dec(v_prom_2459_);
v___x_2600_ = lean_box(0);
return v___x_2600_;
}
v___jp_2601_:
{
v___y_2565_ = v___y_2602_;
v___y_2566_ = v___y_2603_;
v___y_2567_ = v___y_2604_;
goto v___jp_2564_;
}
v___jp_2606_:
{
uint8_t v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = l_IO_CancelToken_isSet(v_parseCancelTk_2461_);
v___x_2618_ = 1;
if (v___x_2617_ == 0)
{
lean_dec(v___y_2615_);
if (v_sync_2460_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2619_ = lean_io_promise_new();
v___x_2620_ = lean_io_promise_new();
v___x_2621_ = lean_io_promise_new();
v___x_2622_ = lean_io_promise_new();
v___x_2623_ = l_Lean_internal_cmdlineSnapshots;
v___x_2624_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2613_, v___x_2623_);
lean_dec_ref(v___y_2613_);
if (v___x_2624_ == 0)
{
lean_inc(v___y_2616_);
v___y_2537_ = v___y_2608_;
v___y_2538_ = v___y_2607_;
v___y_2539_ = v___x_2617_;
v___y_2540_ = v___x_2620_;
v___y_2541_ = v___y_2610_;
v___y_2542_ = v___x_2618_;
v___y_2543_ = v___x_2622_;
v___y_2544_ = v___y_2609_;
v___y_2545_ = v___x_2623_;
v___y_2546_ = v___y_2611_;
v___y_2547_ = v___x_2621_;
v___y_2548_ = v___x_2619_;
v___y_2549_ = v___y_2612_;
v___y_2550_ = v___y_2616_;
v_fst_2551_ = v___y_2616_;
v_snd_2552_ = v___y_2614_;
goto v___jp_2536_;
}
else
{
uint8_t v___x_2625_; 
lean_inc(v___y_2616_);
v___x_2625_ = l_Lean_Parser_isTerminalCommand(v___y_2616_);
if (v___x_2625_ == 0)
{
if (v___x_2624_ == 0)
{
lean_inc(v___y_2616_);
v___y_2537_ = v___y_2608_;
v___y_2538_ = v___y_2607_;
v___y_2539_ = v___x_2617_;
v___y_2540_ = v___x_2620_;
v___y_2541_ = v___y_2610_;
v___y_2542_ = v___x_2618_;
v___y_2543_ = v___x_2622_;
v___y_2544_ = v___y_2609_;
v___y_2545_ = v___x_2623_;
v___y_2546_ = v___y_2611_;
v___y_2547_ = v___x_2621_;
v___y_2548_ = v___x_2619_;
v___y_2549_ = v___y_2612_;
v___y_2550_ = v___y_2616_;
v_fst_2551_ = v___y_2616_;
v_snd_2552_ = v___y_2614_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v___y_2614_);
v___x_2626_ = lean_box(0);
v___x_2627_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2537_ = v___y_2608_;
v___y_2538_ = v___y_2607_;
v___y_2539_ = v___x_2617_;
v___y_2540_ = v___x_2620_;
v___y_2541_ = v___y_2610_;
v___y_2542_ = v___x_2618_;
v___y_2543_ = v___x_2622_;
v___y_2544_ = v___y_2609_;
v___y_2545_ = v___x_2623_;
v___y_2546_ = v___y_2611_;
v___y_2547_ = v___x_2621_;
v___y_2548_ = v___x_2619_;
v___y_2549_ = v___y_2612_;
v___y_2550_ = v___y_2616_;
v_fst_2551_ = v___x_2626_;
v_snd_2552_ = v___x_2627_;
goto v___jp_2536_;
}
}
else
{
lean_inc(v___y_2616_);
v___y_2537_ = v___y_2608_;
v___y_2538_ = v___y_2607_;
v___y_2539_ = v___x_2617_;
v___y_2540_ = v___x_2620_;
v___y_2541_ = v___y_2610_;
v___y_2542_ = v___x_2618_;
v___y_2543_ = v___x_2622_;
v___y_2544_ = v___y_2609_;
v___y_2545_ = v___x_2623_;
v___y_2546_ = v___y_2611_;
v___y_2547_ = v___x_2621_;
v___y_2548_ = v___x_2619_;
v___y_2549_ = v___y_2612_;
v___y_2550_ = v___y_2616_;
v_fst_2551_ = v___y_2616_;
v_snd_2552_ = v___y_2614_;
goto v___jp_2536_;
}
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v___y_2613_);
v___x_2628_ = lean_box(v___x_2617_);
v___x_2629_ = lean_box(v___x_2618_);
lean_inc_ref(v_a_2463_);
v___f_2630_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2630_, 0, v___y_2610_);
lean_closure_set(v___f_2630_, 1, v_revCmds_2462_);
lean_closure_set(v___f_2630_, 2, v___y_2608_);
lean_closure_set(v___f_2630_, 3, v___x_2628_);
lean_closure_set(v___f_2630_, 4, v_a_2463_);
lean_closure_set(v___f_2630_, 5, v___y_2611_);
lean_closure_set(v___f_2630_, 6, v___y_2609_);
lean_closure_set(v___f_2630_, 7, v___x_2629_);
lean_closure_set(v___f_2630_, 8, v___x_2509_);
lean_closure_set(v___f_2630_, 9, v___f_2508_);
lean_closure_set(v___f_2630_, 10, v___f_2507_);
lean_closure_set(v___f_2630_, 11, v___f_2506_);
lean_closure_set(v___f_2630_, 12, v___y_2612_);
lean_closure_set(v___f_2630_, 13, v_cmdState_2458_);
lean_closure_set(v___f_2630_, 14, v___x_2510_);
lean_closure_set(v___f_2630_, 15, v___y_2607_);
lean_closure_set(v___f_2630_, 16, v_prom_2459_);
lean_closure_set(v___f_2630_, 17, v_old_x3f_2456_);
lean_closure_set(v___f_2630_, 18, v_parseCancelTk_2461_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_io_as_task(v___f_2630_, v___x_2631_);
lean_dec_ref(v___x_2632_);
goto v___jp_2465_;
}
}
else
{
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v_revCmds_2462_);
lean_dec_ref(v_parseCancelTk_2461_);
if (lean_obj_tag(v_old_x3f_2456_) == 1)
{
lean_object* v_val_2633_; lean_object* v___x_2634_; lean_object* v_children_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_val_2633_ = lean_ctor_get(v_old_x3f_2456_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_old_x3f_2456_, 1);
v___x_2634_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2633_);
v_children_2635_ = lean_ctor_get(v___x_2634_, 1);
lean_inc_ref(v_children_2635_);
lean_dec_ref(v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_array_get_size(v_children_2635_);
v___x_2638_ = lean_nat_dec_lt(v___x_2636_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_dec_ref(v_children_2635_);
v___y_2565_ = v___y_2614_;
v___y_2566_ = v___y_2615_;
v___y_2567_ = v___x_2618_;
goto v___jp_2564_;
}
else
{
lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2639_ = lean_box(0);
v___x_2640_ = lean_nat_dec_le(v___x_2637_, v___x_2637_);
if (v___x_2640_ == 0)
{
if (v___x_2638_ == 0)
{
lean_dec_ref(v_children_2635_);
v___y_2565_ = v___y_2614_;
v___y_2566_ = v___y_2615_;
v___y_2567_ = v___x_2618_;
goto v___jp_2564_;
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = lean_usize_of_nat(v___x_2637_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2635_, v___x_2641_, v___x_2642_, v___x_2639_);
lean_dec_ref(v_children_2635_);
v___y_2602_ = v___y_2614_;
v___y_2603_ = v___y_2615_;
v___y_2604_ = v___x_2618_;
v___y_2605_ = v___x_2643_;
goto v___jp_2601_;
}
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2637_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2635_, v___x_2644_, v___x_2645_, v___x_2639_);
lean_dec_ref(v_children_2635_);
v___y_2602_ = v___y_2614_;
v___y_2603_ = v___y_2615_;
v___y_2604_ = v___x_2618_;
v___y_2605_ = v___x_2646_;
goto v___jp_2601_;
}
}
}
else
{
lean_dec(v_old_x3f_2456_);
v___y_2565_ = v___y_2614_;
v___y_2566_ = v___y_2615_;
v___y_2567_ = v___x_2618_;
goto v___jp_2564_;
}
}
}
v___jp_2648_:
{
lean_object* v_env_2649_; lean_object* v_scopes_2650_; lean_object* v___x_2651_; lean_object* v_opts_2652_; lean_object* v_currNamespace_2653_; lean_object* v_openDecls_2654_; lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v_snd_2660_; 
v_env_2649_ = lean_ctor_get(v_cmdState_2458_, 0);
v_scopes_2650_ = lean_ctor_get(v_cmdState_2458_, 2);
v___x_2651_ = l_List_head_x21___redArg(v___x_2509_, v_scopes_2650_);
v_opts_2652_ = lean_ctor_get(v___x_2651_, 1);
lean_inc_ref_n(v_opts_2652_, 2);
v_currNamespace_2653_ = lean_ctor_get(v___x_2651_, 2);
lean_inc(v_currNamespace_2653_);
v_openDecls_2654_ = lean_ctor_get(v___x_2651_, 3);
lean_inc(v_openDecls_2654_);
lean_dec(v___x_2651_);
lean_inc_ref(v_env_2649_);
v___x_2655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2655_, 0, v_env_2649_);
lean_ctor_set(v___x_2655_, 1, v_opts_2652_);
lean_ctor_set(v___x_2655_, 2, v_currNamespace_2653_);
lean_ctor_set(v___x_2655_, 3, v_openDecls_2654_);
lean_inc_ref(v_parserState_2457_);
lean_inc_ref(v_a_2463_);
v___f_2656_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2656_, 0, v_a_2463_);
lean_closure_set(v___f_2656_, 1, v___x_2655_);
lean_closure_set(v___f_2656_, 2, v_parserState_2457_);
v___x_2657_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_profileit(v___x_2657_, v_opts_2652_, v___f_2656_, v___x_2658_);
v_snd_2660_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_snd_2660_);
if (lean_obj_tag(v_old_x3f_2456_) == 1)
{
lean_object* v_val_2661_; lean_object* v_fst_2662_; lean_object* v_fst_2663_; lean_object* v_snd_2664_; lean_object* v_pos_2665_; lean_object* v_toSnapshot_2666_; lean_object* v_stx_2667_; lean_object* v_parserState_2668_; lean_object* v_elabSnap_2669_; lean_object* v_nextCmdSnap_x3f_2670_; uint8_t v___x_2671_; 
v_val_2661_ = lean_ctor_get(v_old_x3f_2456_, 0);
v_fst_2662_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_n(v_fst_2662_, 2);
lean_dec(v___x_2659_);
v_fst_2663_ = lean_ctor_get(v_snd_2660_, 0);
lean_inc(v_fst_2663_);
v_snd_2664_ = lean_ctor_get(v_snd_2660_, 1);
lean_inc(v_snd_2664_);
lean_dec(v_snd_2660_);
v_pos_2665_ = lean_ctor_get(v_parserState_2457_, 0);
lean_inc(v_pos_2665_);
lean_dec_ref(v_parserState_2457_);
v_toSnapshot_2666_ = lean_ctor_get(v_val_2661_, 0);
v_stx_2667_ = lean_ctor_get(v_val_2661_, 1);
v_parserState_2668_ = lean_ctor_get(v_val_2661_, 2);
v_elabSnap_2669_ = lean_ctor_get(v_val_2661_, 3);
v_nextCmdSnap_x3f_2670_ = lean_ctor_get(v_val_2661_, 4);
lean_inc(v_stx_2667_);
v___x_2671_ = l_Lean_Syntax_eqWithInfo(v_fst_2662_, v_stx_2667_);
if (v___x_2671_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2670_) == 0)
{
lean_inc(v_fst_2662_);
lean_inc(v_fst_2663_);
lean_inc_ref(v_opts_2652_);
v___y_2607_ = v_opts_2652_;
v___y_2608_ = v_fst_2663_;
v___y_2609_ = v___x_2658_;
v___y_2610_ = v_fst_2662_;
v___y_2611_ = v_snd_2664_;
v___y_2612_ = v_pos_2665_;
v___y_2613_ = v_opts_2652_;
v___y_2614_ = v_fst_2663_;
v___y_2615_ = v___x_2658_;
v___y_2616_ = v_fst_2662_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2672_; lean_object* v___x_2673_; 
v_val_2672_ = lean_ctor_get(v_nextCmdSnap_x3f_2670_, 0);
lean_inc(v_val_2672_);
v___x_2673_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2647_, v_val_2672_);
lean_inc(v_fst_2662_);
lean_inc(v_fst_2663_);
lean_inc_ref(v_opts_2652_);
v___y_2607_ = v_opts_2652_;
v___y_2608_ = v_fst_2663_;
v___y_2609_ = v___x_2658_;
v___y_2610_ = v_fst_2662_;
v___y_2611_ = v_snd_2664_;
v___y_2612_ = v_pos_2665_;
v___y_2613_ = v_opts_2652_;
v___y_2614_ = v_fst_2663_;
v___y_2615_ = v___x_2658_;
v___y_2616_ = v_fst_2662_;
goto v___jp_2606_;
}
}
else
{
lean_inc(v_val_2661_);
lean_dec(v_pos_2665_);
lean_dec(v_snd_2664_);
lean_dec(v_fst_2662_);
lean_dec_ref_known(v_old_x3f_2456_, 1);
lean_dec_ref(v_opts_2652_);
lean_dec_ref(v_parseCancelTk_2461_);
lean_dec_ref(v_cmdState_2458_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2670_) == 1)
{
lean_object* v_val_2674_; 
lean_inc_ref(v_nextCmdSnap_x3f_2670_);
lean_inc_ref(v_elabSnap_2669_);
lean_inc_ref(v_parserState_2668_);
lean_inc(v_stx_2667_);
lean_inc_ref(v_toSnapshot_2666_);
lean_dec(v_val_2661_);
v_val_2674_ = lean_ctor_get(v_nextCmdSnap_x3f_2670_, 0);
lean_inc(v_val_2674_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2670_, 1);
v_toSnapshot_2470_ = v_toSnapshot_2666_;
v_stx_2471_ = v_stx_2667_;
v_parserState_2472_ = v_parserState_2668_;
v_elabSnap_2473_ = v_elabSnap_2669_;
v_val_2474_ = v_val_2674_;
v_newParserState_2475_ = v_fst_2663_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2675_; 
lean_dec(v_fst_2663_);
lean_dec(v_revCmds_2462_);
v___x_2675_ = lean_io_promise_resolve(v_val_2661_, v_prom_2459_);
lean_dec(v_prom_2459_);
return v___x_2675_;
}
}
}
else
{
lean_object* v_fst_2676_; lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v_pos_2679_; 
v_fst_2676_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_n(v_fst_2676_, 2);
lean_dec(v___x_2659_);
v_fst_2677_ = lean_ctor_get(v_snd_2660_, 0);
lean_inc_n(v_fst_2677_, 2);
v_snd_2678_ = lean_ctor_get(v_snd_2660_, 1);
lean_inc(v_snd_2678_);
lean_dec(v_snd_2660_);
v_pos_2679_ = lean_ctor_get(v_parserState_2457_, 0);
lean_inc(v_pos_2679_);
lean_dec_ref(v_parserState_2457_);
lean_inc_ref(v_opts_2652_);
v___y_2607_ = v_opts_2652_;
v___y_2608_ = v_fst_2677_;
v___y_2609_ = v___x_2658_;
v___y_2610_ = v_fst_2676_;
v___y_2611_ = v_snd_2678_;
v___y_2612_ = v_pos_2679_;
v___y_2613_ = v_opts_2652_;
v___y_2614_ = v_fst_2677_;
v___y_2615_ = v___x_2658_;
v___y_2616_ = v_fst_2676_;
goto v___jp_2606_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2696_, lean_object* v_stx_2697_, lean_object* v_revCmds_2698_, lean_object* v_newParserState_2699_, lean_object* v_val_2700_, uint8_t v_sync_2701_, lean_object* v_val_2702_, lean_object* v_a_2703_, lean_object* v_oldNext_2704_){
_start:
{
lean_object* v_cmdState_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_cmdState_2706_ = lean_ctor_get(v_oldResult_2696_, 1);
lean_inc_ref(v_cmdState_2706_);
lean_dec_ref(v_oldResult_2696_);
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_oldNext_2704_);
v___x_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_stx_2697_);
lean_ctor_set(v___x_2708_, 1, v_revCmds_2698_);
v___x_2709_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2707_, v_newParserState_2699_, v_cmdState_2706_, v_val_2700_, v_sync_2701_, v_val_2702_, v___x_2708_, v_a_2703_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2710_ = _args[0];
lean_object* v_val_2711_ = _args[1];
lean_object* v_fst_2712_ = _args[2];
lean_object* v_revCmds_2713_ = _args[3];
lean_object* v_fst_2714_ = _args[4];
lean_object* v_val_2715_ = _args[5];
lean_object* v_a_2716_ = _args[6];
lean_object* v_snd_2717_ = _args[7];
lean_object* v___x_2718_ = _args[8];
lean_object* v___x_2719_ = _args[9];
lean_object* v_fst_2720_ = _args[10];
lean_object* v_val_2721_ = _args[11];
lean_object* v_val_2722_ = _args[12];
lean_object* v___x_2723_ = _args[13];
lean_object* v___f_2724_ = _args[14];
lean_object* v___f_2725_ = _args[15];
lean_object* v___f_2726_ = _args[16];
lean_object* v_pos_2727_ = _args[17];
lean_object* v_cmdState_2728_ = _args[18];
lean_object* v_val_2729_ = _args[19];
lean_object* v___x_2730_ = _args[20];
lean_object* v_opts_2731_ = _args[21];
lean_object* v___x_2732_ = _args[22];
lean_object* v_snd_2733_ = _args[23];
lean_object* v_prom_2734_ = _args[24];
lean_object* v_old_x3f_2735_ = _args[25];
lean_object* v_parseCancelTk_2736_ = _args[26];
lean_object* v_next_x3f_2737_ = _args[27];
lean_object* v___y_2738_ = _args[28];
_start:
{
uint8_t v_val_37412__boxed_2739_; uint8_t v___x_37415__boxed_2740_; lean_object* v_res_2741_; 
v_val_37412__boxed_2739_ = lean_unbox(v_val_2715_);
v___x_37415__boxed_2740_ = lean_unbox(v___x_2719_);
v_res_2741_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2710_, v_val_2711_, v_fst_2712_, v_revCmds_2713_, v_fst_2714_, v_val_37412__boxed_2739_, v_a_2716_, v_snd_2717_, v___x_2718_, v___x_37415__boxed_2740_, v_fst_2720_, v_val_2721_, v_val_2722_, v___x_2723_, v___f_2724_, v___f_2725_, v___f_2726_, v_pos_2727_, v_cmdState_2728_, v_val_2729_, v___x_2730_, v_opts_2731_, v___x_2732_, v_snd_2733_, v_prom_2734_, v_old_x3f_2735_, v_parseCancelTk_2736_, v_next_x3f_2737_);
lean_dec(v_prom_2734_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v_opts_2731_);
lean_dec(v_val_2722_);
lean_dec_ref(v_a_2716_);
lean_dec(v_val_2711_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2742_, lean_object* v_parserState_2743_, lean_object* v_cmdState_2744_, lean_object* v_prom_2745_, lean_object* v_sync_2746_, lean_object* v_parseCancelTk_2747_, lean_object* v_revCmds_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
uint8_t v_sync_boxed_2751_; lean_object* v_res_2752_; 
v_sync_boxed_2751_ = lean_unbox(v_sync_2746_);
v_res_2752_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2742_, v_parserState_2743_, v_cmdState_2744_, v_prom_2745_, v_sync_boxed_2751_, v_parseCancelTk_2747_, v_revCmds_2748_, v_a_2749_);
lean_dec_ref(v_a_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2753_, size_t v_i_2754_, size_t v_stop_2755_, lean_object* v_b_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2753_, v_i_2754_, v_stop_2755_, v_b_2756_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2760_, lean_object* v_i_2761_, lean_object* v_stop_2762_, lean_object* v_b_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
size_t v_i_boxed_2766_; size_t v_stop_boxed_2767_; lean_object* v_res_2768_; 
v_i_boxed_2766_ = lean_unbox_usize(v_i_2761_);
lean_dec(v_i_2761_);
v_stop_boxed_2767_ = lean_unbox_usize(v_stop_2762_);
lean_dec(v_stop_2762_);
v_res_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2760_, v_i_boxed_2766_, v_stop_boxed_2767_, v_b_2763_, v___y_2764_);
lean_dec_ref(v___y_2764_);
lean_dec_ref(v_as_2760_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2769_, lean_object* v_opt_2770_){
_start:
{
lean_object* v_name_2771_; lean_object* v_map_2772_; lean_object* v___x_2773_; 
v_name_2771_ = lean_ctor_get(v_opt_2770_, 0);
v_map_2772_ = lean_ctor_get(v_opts_2769_, 0);
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2772_, v_name_2771_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_box(0);
return v___x_2774_;
}
else
{
lean_object* v_val_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2784_; 
v_val_2775_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2777_ = v___x_2773_;
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_val_2775_);
lean_dec(v___x_2773_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2784_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
if (lean_obj_tag(v_val_2775_) == 0)
{
lean_object* v_v_2779_; lean_object* v___x_2781_; 
v_v_2779_ = lean_ctor_get(v_val_2775_, 0);
lean_inc_ref(v_v_2779_);
lean_dec_ref_known(v_val_2775_, 1);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v_v_2779_);
v___x_2781_ = v___x_2777_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_v_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
else
{
lean_object* v___x_2783_; 
lean_del_object(v___x_2777_);
lean_dec(v_val_2775_);
v___x_2783_ = lean_box(0);
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2785_, lean_object* v_opt_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2785_, v_opt_2786_);
lean_dec_ref(v_opt_2786_);
lean_dec_ref(v_opts_2785_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2788_);
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2792_, 0, v_x_2789_);
lean_ctor_set(v___x_2792_, 1, v___x_2790_);
lean_ctor_set(v___x_2792_, 2, v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2799_ = l_Lean_Array_toPArray_x27___redArg(v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
if (lean_obj_tag(v_a_2800_) == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = l_List_reverse___redArg(v_a_2801_);
return v___x_2802_;
}
else
{
lean_object* v_head_2803_; lean_object* v_tail_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2817_; 
v_head_2803_ = lean_ctor_get(v_a_2800_, 0);
v_tail_2804_ = lean_ctor_get(v_a_2800_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2800_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2806_ = v_a_2800_;
v_isShared_2807_ = v_isSharedCheck_2817_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_tail_2804_);
lean_inc(v_head_2803_);
lean_dec(v_a_2800_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2817_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2808_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v_head_2803_);
v___x_2810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
v___x_2811_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 1, v_a_2801_);
lean_ctor_set(v___x_2806_, 0, v___x_2812_);
v___x_2814_ = v___x_2806_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_a_2801_);
v___x_2814_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
v_a_2800_ = v_tail_2804_;
v_a_2801_ = v___x_2814_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2818_; double v___x_2819_; 
v___x_2818_ = lean_unsigned_to_nat(1000000000u);
v___x_2819_ = lean_float_of_nat(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2837_ = l_Lean_MessageData_ofFormat(v___x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2838_, lean_object* v_stx_2839_, lean_object* v_origStx_2840_, lean_object* v_toProcessingContext_2841_, lean_object* v___x_2842_, lean_object* v_fileMap_2843_, lean_object* v_parserState_2844_, lean_object* v_a_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_toProcessingContext_2851_; lean_object* v___x_2852_; 
v_toProcessingContext_2851_ = lean_ctor_get(v___y_2849_, 0);
lean_inc_ref(v_toProcessingContext_2851_);
lean_inc(v_stx_2839_);
v___x_2852_ = lean_apply_3(v_setupImports_2838_, v_stx_2839_, v_toProcessingContext_2851_, lean_box(0));
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_3065_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_3065_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_3065_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; 
lean_dec_ref(v___x_2848_);
lean_dec(v___x_2846_);
lean_dec_ref(v_parserState_2844_);
lean_dec_ref(v_fileMap_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_toProcessingContext_2841_);
lean_dec(v_origStx_2840_);
lean_dec(v_stx_2839_);
v_a_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v_a_2853_, 1);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_3064_; 
v_a_2861_ = lean_ctor_get(v_a_2853_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_2863_ = v_a_2853_;
v_isShared_2864_ = v_isSharedCheck_3064_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v_a_2853_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_3064_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v_mainModuleName_2866_; lean_object* v_package_x3f_2867_; uint8_t v_isModule_2868_; lean_object* v_imports_2869_; lean_object* v_opts_2870_; uint32_t v_trustLevel_2871_; lean_object* v_importArts_2872_; lean_object* v_plugins_2873_; double v___x_2874_; double v___x_2875_; double v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2881_; 
v___x_2865_ = lean_io_mono_nanos_now();
v_mainModuleName_2866_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_mainModuleName_2866_);
v_package_x3f_2867_ = lean_ctor_get(v_a_2861_, 1);
lean_inc(v_package_x3f_2867_);
v_isModule_2868_ = lean_ctor_get_uint8(v_a_2861_, sizeof(void*)*6 + 4);
v_imports_2869_ = lean_ctor_get(v_a_2861_, 2);
lean_inc_ref(v_imports_2869_);
v_opts_2870_ = lean_ctor_get(v_a_2861_, 3);
lean_inc_ref(v_opts_2870_);
v_trustLevel_2871_ = lean_ctor_get_uint32(v_a_2861_, sizeof(void*)*6);
v_importArts_2872_ = lean_ctor_get(v_a_2861_, 4);
lean_inc(v_importArts_2872_);
v_plugins_2873_ = lean_ctor_get(v_a_2861_, 5);
lean_inc_ref(v_plugins_2873_);
lean_dec(v_a_2861_);
v___x_2874_ = lean_float_of_nat(v___x_2865_);
v___x_2875_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2876_ = lean_float_div(v___x_2874_, v___x_2875_);
v___x_2877_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2839_);
v___x_2878_ = l_Lean_MessageLog_empty;
v___x_2879_ = 1;
lean_inc(v_stx_2839_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v_stx_2839_);
v___x_2881_ = v___x_2863_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_stx_2839_);
v___x_2881_ = v_reuseFailAlloc_3063_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_origStx_2840_);
lean_inc_ref(v___x_2881_);
lean_inc_ref(v_opts_2870_);
v___x_2883_ = l_Lean_Elab_processHeaderCore(v___x_2877_, v_imports_2869_, v_isModule_2868_, v_opts_2870_, v___x_2878_, v_toProcessingContext_2841_, v_trustLevel_2871_, v_plugins_2873_, v___x_2879_, v_mainModuleName_2866_, v_package_x3f_2867_, v_importArts_2872_, v___x_2881_, v___x_2882_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_3054_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_3054_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_3054_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_fst_2888_; lean_object* v_snd_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_3053_; 
v_fst_2888_ = lean_ctor_get(v_a_2884_, 0);
v_snd_2889_ = lean_ctor_get(v_a_2884_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_a_2884_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_2891_ = v_a_2884_;
v_isShared_2892_ = v_isSharedCheck_3053_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_snd_2889_);
lean_inc(v_fst_2888_);
lean_dec(v_a_2884_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_3053_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; double v___x_2894_; double v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v_traceState_2913_; 
v___x_2893_ = lean_io_mono_nanos_now();
v___x_2894_ = lean_float_of_nat(v___x_2893_);
v___x_2895_ = lean_float_div(v___x_2894_, v___x_2875_);
lean_inc(v_snd_2889_);
v___x_2896_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2889_);
v___x_2897_ = l_Lean_MessageLog_hasErrors(v_snd_2889_);
if (v___x_2897_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_del_object(v___x_2855_);
lean_dec_ref(v___x_2848_);
v___x_3022_ = l_Lean_trace_profiler_output;
v___x_3023_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2870_, v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = l_Lean_trace_profiler_serve;
v___x_3025_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2870_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2913_ = v___x_3026_;
goto v___jp_2912_;
}
else
{
goto v___jp_3006_;
}
}
else
{
lean_dec_ref_known(v___x_3023_, 1);
goto v___jp_3006_;
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint64_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_del_object(v___x_2891_);
lean_dec(v_snd_2889_);
lean_dec(v_fst_2888_);
lean_del_object(v___x_2886_);
lean_dec_ref(v___x_2881_);
lean_dec_ref(v_opts_2870_);
lean_dec(v___x_2846_);
lean_dec_ref(v_parserState_2844_);
lean_dec_ref(v_fileMap_2843_);
lean_dec(v_stx_2839_);
v___x_3027_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3028_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3029_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2842_, 2);
v___x_3030_ = l_Lean_Name_num___override(v___x_3029_, v___x_2842_);
v___x_3031_ = l_Lean_Name_str___override(v___x_3030_, v___x_3027_);
v___x_3032_ = l_Lean_Name_str___override(v___x_3031_, v___x_3028_);
v___x_3033_ = l_Lean_Name_str___override(v___x_3032_, v___x_3027_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3035_ = l_Lean_Name_str___override(v___x_3033_, v___x_3034_);
v___x_3036_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3037_ = l_Lean_Name_str___override(v___x_3035_, v___x_3036_);
v___x_3038_ = l_Lean_Name_toString(v___x_3037_, v___x_2879_);
v___x_3039_ = lean_box(0);
v___x_3040_ = 0ULL;
v___x_3041_ = lean_unsigned_to_nat(32u);
v___x_3042_ = lean_mk_empty_array_with_capacity(v___x_3041_);
v___x_3043_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3044_ = ((size_t)5ULL);
v___x_3045_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3042_);
lean_ctor_set(v___x_3045_, 2, v___x_2842_);
lean_ctor_set(v___x_3045_, 3, v___x_2842_);
lean_ctor_set_usize(v___x_3045_, 4, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set_uint64(v___x_3046_, sizeof(void*)*1, v___x_3040_);
v___x_3047_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3047_, 0, v___x_3038_);
lean_ctor_set(v___x_3047_, 1, v___x_2896_);
lean_ctor_set(v___x_3047_, 2, v___x_3039_);
lean_ctor_set(v___x_3047_, 3, v___x_3046_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*4, v___x_2897_);
v___x_3048_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2848_);
v___x_3049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
lean_ctor_set(v___x_3049_, 2, v___x_3039_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_3049_);
v___x_3051_ = v___x_2855_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
v___jp_2898_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___y_2904_);
v___x_2906_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2906_, 0, v___y_2902_);
lean_ctor_set(v___x_2906_, 1, v___x_2896_);
lean_ctor_set(v___x_2906_, 2, v___x_2905_);
lean_ctor_set(v___x_2906_, 3, v___y_2899_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*4, v___x_2897_);
v___x_2907_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2903_, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2908_, 0, v___y_2901_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
lean_ctor_set(v___x_2908_, 2, v___y_2900_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2908_);
v___x_2910_ = v___x_2886_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
v___jp_2912_:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Language_Lean_reparseOptions(v_opts_2870_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v_env_2917_; lean_object* v_messages_2918_; lean_object* v_scopes_2919_; lean_object* v_usedQuotCtxts_2920_; lean_object* v_nextMacroScope_2921_; lean_object* v_maxRecDepth_2922_; lean_object* v_ngen_2923_; lean_object* v_auxDeclNGen_2924_; lean_object* v_snapshotTasks_2925_; lean_object* v_prevLinterStates_2926_; lean_object* v_codeQualityEntryTasks_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2995_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
lean_inc(v_fst_2888_);
v___x_2916_ = l_Lean_Elab_Command_mkState(v_fst_2888_, v_snd_2889_, v_a_2915_);
v_env_2917_ = lean_ctor_get(v___x_2916_, 0);
v_messages_2918_ = lean_ctor_get(v___x_2916_, 1);
v_scopes_2919_ = lean_ctor_get(v___x_2916_, 2);
v_usedQuotCtxts_2920_ = lean_ctor_get(v___x_2916_, 3);
v_nextMacroScope_2921_ = lean_ctor_get(v___x_2916_, 4);
v_maxRecDepth_2922_ = lean_ctor_get(v___x_2916_, 5);
v_ngen_2923_ = lean_ctor_get(v___x_2916_, 6);
v_auxDeclNGen_2924_ = lean_ctor_get(v___x_2916_, 7);
v_snapshotTasks_2925_ = lean_ctor_get(v___x_2916_, 10);
v_prevLinterStates_2926_ = lean_ctor_get(v___x_2916_, 11);
v_codeQualityEntryTasks_2927_ = lean_ctor_get(v___x_2916_, 12);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; lean_object* v_unused_2997_; 
v_unused_2996_ = lean_ctor_get(v___x_2916_, 9);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v___x_2916_, 8);
lean_dec(v_unused_2997_);
v___x_2929_ = v___x_2916_;
v_isShared_2930_ = v_isSharedCheck_2995_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2927_);
lean_inc(v_prevLinterStates_2926_);
lean_inc(v_snapshotTasks_2925_);
lean_inc(v_auxDeclNGen_2924_);
lean_inc(v_ngen_2923_);
lean_inc(v_maxRecDepth_2922_);
lean_inc(v_nextMacroScope_2921_);
lean_inc(v_usedQuotCtxts_2920_);
lean_inc(v_scopes_2919_);
lean_inc(v_messages_2918_);
lean_inc(v_env_2917_);
lean_dec(v___x_2916_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2995_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2931_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2932_ = lean_box(0);
lean_inc_n(v___x_2842_, 4);
v___x_2933_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2842_);
lean_ctor_set(v___x_2933_, 1, v___x_2842_);
lean_ctor_set(v___x_2933_, 2, v___x_2842_);
lean_ctor_set(v___x_2933_, 3, v___x_2842_);
lean_ctor_set(v___x_2933_, 4, v___x_2931_);
lean_ctor_set(v___x_2933_, 5, v___x_2931_);
lean_ctor_set(v___x_2933_, 6, v___x_2931_);
lean_ctor_set(v___x_2933_, 7, v___x_2931_);
lean_ctor_set(v___x_2933_, 8, v___x_2931_);
lean_ctor_set(v___x_2933_, 9, v___x_2931_);
lean_ctor_set(v___x_2933_, 10, v___x_2931_);
v___x_2934_ = l_Lean_Options_empty;
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_box(0);
v___x_2937_ = lean_unsigned_to_nat(1u);
v___x_2938_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2939_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2939_, 0, v_fst_2888_);
lean_ctor_set(v___x_2939_, 1, v___x_2932_);
lean_ctor_set(v___x_2939_, 2, v_fileMap_2843_);
lean_ctor_set(v___x_2939_, 3, v___x_2933_);
lean_ctor_set(v___x_2939_, 4, v___x_2934_);
lean_ctor_set(v___x_2939_, 5, v___x_2935_);
lean_ctor_set(v___x_2939_, 6, v___x_2936_);
lean_ctor_set(v___x_2939_, 7, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
v___x_2941_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2839_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v_stx_2839_);
lean_ctor_set(v___x_2891_, 0, v___x_2941_);
v___x_2943_ = v___x_2891_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_stx_2839_);
v___x_2943_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_unsigned_to_nat(2u);
v___x_2946_ = l_Lean_Syntax_getArg(v_stx_2839_, v___x_2945_);
lean_dec(v_stx_2839_);
v___x_2947_ = l_Lean_Syntax_getArgs(v___x_2946_);
lean_dec(v___x_2946_);
v___x_2948_ = lean_array_to_list(v___x_2947_);
v___x_2949_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2948_, v___x_2936_);
v___x_2950_ = l_Lean_List_toPArray_x27___redArg(v___x_2949_);
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2944_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2940_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2937_);
v___x_2954_ = lean_array_push(v___x_2953_, v___x_2952_);
v___x_2955_ = l_Lean_Array_toPArray_x27___redArg(v___x_2954_);
lean_dec_ref(v___x_2954_);
lean_inc_ref(v___x_2955_);
v___x_2956_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2956_, 0, v___x_2931_);
lean_ctor_set(v___x_2956_, 1, v___x_2931_);
lean_ctor_set(v___x_2956_, 2, v___x_2955_);
lean_ctor_set_uint8(v___x_2956_, sizeof(void*)*3, v___x_2879_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 9, v_traceState_2913_);
lean_ctor_set(v___x_2929_, 8, v___x_2956_);
v___x_2958_ = v___x_2929_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_env_2917_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_messages_2918_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_scopes_2919_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_usedQuotCtxts_2920_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_nextMacroScope_2921_);
lean_ctor_set(v_reuseFailAlloc_2993_, 5, v_maxRecDepth_2922_);
lean_ctor_set(v_reuseFailAlloc_2993_, 6, v_ngen_2923_);
lean_ctor_set(v_reuseFailAlloc_2993_, 7, v_auxDeclNGen_2924_);
lean_ctor_set(v_reuseFailAlloc_2993_, 8, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2993_, 9, v_traceState_2913_);
lean_ctor_set(v_reuseFailAlloc_2993_, 10, v_snapshotTasks_2925_);
lean_ctor_set(v_reuseFailAlloc_2993_, 11, v_prevLinterStates_2926_);
lean_ctor_set(v_reuseFailAlloc_2993_, 12, v_codeQualityEntryTasks_2927_);
v___x_2958_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; size_t v___x_2969_; lean_object* v___x_2970_; lean_object* v_size_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint64_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2959_ = lean_io_promise_new();
v___x_2960_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_2960_);
lean_inc(v___x_2959_);
lean_inc_ref(v___x_2958_);
v___x_2961_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2932_, v_parserState_2844_, v___x_2958_, v___x_2959_, v___x_2879_, v___x_2960_, v___x_2936_, v_a_2845_);
v___x_2962_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2963_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2964_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2842_, 3);
v___x_2965_ = l_Lean_Name_num___override(v___x_2964_, v___x_2842_);
v___x_2966_ = lean_unsigned_to_nat(32u);
v___x_2967_ = lean_mk_empty_array_with_capacity(v___x_2966_);
v___x_2968_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2969_ = ((size_t)5ULL);
v___x_2970_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v___x_2967_);
lean_ctor_set(v___x_2970_, 2, v___x_2842_);
lean_ctor_set(v___x_2970_, 3, v___x_2842_);
lean_ctor_set_usize(v___x_2970_, 4, v___x_2969_);
v_size_2971_ = lean_ctor_get(v___x_2955_, 2);
v___x_2972_ = l_Lean_Name_str___override(v___x_2965_, v___x_2962_);
v___x_2973_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2846_);
v___x_2974_ = l_Lean_Name_str___override(v___x_2972_, v___x_2963_);
v___x_2975_ = l_Lean_Name_str___override(v___x_2974_, v___x_2962_);
v___x_2976_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2977_ = l_Lean_Name_str___override(v___x_2975_, v___x_2976_);
v___x_2978_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2979_ = l_Lean_Name_str___override(v___x_2977_, v___x_2978_);
v___x_2980_ = l_Lean_Name_toString(v___x_2979_, v___x_2879_);
v___x_2981_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2982_ = 0ULL;
v___x_2983_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2983_, 0, v___x_2970_);
lean_ctor_set_uint64(v___x_2983_, sizeof(void*)*1, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2960_);
v___x_2985_ = l_IO_Promise_result_x21___redArg(v___x_2959_);
lean_dec(v___x_2959_);
v___x_2986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2846_);
lean_ctor_set(v___x_2986_, 1, v___x_2973_);
lean_ctor_set(v___x_2986_, 2, v___x_2984_);
lean_ctor_set(v___x_2986_, 3, v___x_2985_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2958_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_inc_ref(v___x_2983_);
lean_inc_ref(v___x_2980_);
v___x_2989_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2989_, 0, v___x_2980_);
lean_ctor_set(v___x_2989_, 1, v___x_2981_);
lean_ctor_set(v___x_2989_, 2, v___x_2932_);
lean_ctor_set(v___x_2989_, 3, v___x_2983_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*4, v___x_2897_);
v___x_2990_ = lean_nat_dec_lt(v___x_2842_, v_size_2971_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2842_);
v___x_2991_ = l_outOfBounds___redArg(v___x_2847_);
v___y_2899_ = v___x_2983_;
v___y_2900_ = v___x_2988_;
v___y_2901_ = v___x_2989_;
v___y_2902_ = v___x_2980_;
v___y_2903_ = v___x_2881_;
v___y_2904_ = v___x_2991_;
goto v___jp_2898_;
}
else
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2847_, v___x_2955_, v___x_2842_);
lean_dec(v___x_2842_);
lean_dec_ref(v___x_2955_);
v___y_2899_ = v___x_2983_;
v___y_2900_ = v___x_2988_;
v___y_2901_ = v___x_2989_;
v___y_2902_ = v___x_2980_;
v___y_2903_ = v___x_2881_;
v___y_2904_ = v___x_2992_;
goto v___jp_2898_;
}
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v_traceState_2913_);
lean_dec_ref(v___x_2896_);
lean_del_object(v___x_2891_);
lean_dec(v_snd_2889_);
lean_dec(v_fst_2888_);
lean_del_object(v___x_2886_);
lean_dec_ref(v___x_2881_);
lean_dec(v___x_2846_);
lean_dec_ref(v_parserState_2844_);
lean_dec_ref(v_fileMap_2843_);
lean_dec(v___x_2842_);
lean_dec(v_stx_2839_);
v_a_2998_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2914_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2914_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
v___jp_3006_:
{
uint64_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3007_ = 0ULL;
v___x_3008_ = lean_box(0);
v___x_3009_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_3010_ = lean_box(0);
v___x_3011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3012_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3012_, 0, v___x_3009_);
lean_ctor_set(v___x_3012_, 1, v___x_3010_);
lean_ctor_set(v___x_3012_, 2, v___x_3011_);
lean_ctor_set_float(v___x_3012_, sizeof(void*)*3, v___x_2876_);
lean_ctor_set_float(v___x_3012_, sizeof(void*)*3 + 8, v___x_2895_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*3 + 16, v___x_2879_);
v___x_3013_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_2842_);
v___x_3015_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3012_);
lean_ctor_set(v___x_3015_, 1, v___x_3013_);
lean_ctor_set(v___x_3015_, 2, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3008_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = lean_unsigned_to_nat(1u);
v___x_3018_ = lean_mk_empty_array_with_capacity(v___x_3017_);
v___x_3019_ = lean_array_push(v___x_3018_, v___x_3016_);
v___x_3020_ = l_Lean_Array_toPArray_x27___redArg(v___x_3019_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set_uint64(v___x_3021_, sizeof(void*)*1, v___x_3007_);
v_traceState_2913_ = v___x_3021_;
goto v___jp_2912_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v___x_2881_);
lean_dec_ref(v_opts_2870_);
lean_del_object(v___x_2855_);
lean_dec_ref(v___x_2848_);
lean_dec(v___x_2846_);
lean_dec_ref(v_parserState_2844_);
lean_dec_ref(v_fileMap_2843_);
lean_dec(v___x_2842_);
lean_dec(v_stx_2839_);
v_a_3055_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2883_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2883_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
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
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v___x_2848_);
lean_dec(v___x_2846_);
lean_dec_ref(v_parserState_2844_);
lean_dec_ref(v_fileMap_2843_);
lean_dec(v___x_2842_);
lean_dec_ref(v_toProcessingContext_2841_);
lean_dec(v_origStx_2840_);
lean_dec(v_stx_2839_);
v_a_3066_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2852_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2852_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3074_, lean_object* v_stx_3075_, lean_object* v_origStx_3076_, lean_object* v_toProcessingContext_3077_, lean_object* v___x_3078_, lean_object* v_fileMap_3079_, lean_object* v_parserState_3080_, lean_object* v_a_3081_, lean_object* v___x_3082_, lean_object* v___x_3083_, lean_object* v___x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3074_, v_stx_3075_, v_origStx_3076_, v_toProcessingContext_3077_, v___x_3078_, v_fileMap_3079_, v_parserState_3080_, v_a_3081_, v___x_3082_, v___x_3083_, v___x_3084_, v___y_3085_);
lean_dec_ref(v___y_3085_);
lean_dec_ref(v___x_3083_);
lean_dec_ref(v_a_3081_);
return v_res_3087_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___f_3089_; 
v___x_3088_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3089_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3089_, 0, v___x_3088_);
return v___f_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3090_, lean_object* v_stx_3091_, lean_object* v_origStx_3092_, lean_object* v_parserState_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_toProcessingContext_3096_; lean_object* v_fileMap_3097_; lean_object* v_endPos_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_toProcessingContext_3096_ = lean_ctor_get(v_a_3094_, 0);
v_fileMap_3097_ = lean_ctor_get(v_toProcessingContext_3096_, 2);
v_endPos_3098_ = lean_ctor_get(v_toProcessingContext_3096_, 3);
v___x_3099_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3100_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3101_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3094_, 2);
lean_inc_ref(v_fileMap_3097_);
lean_inc_ref(v_toProcessingContext_3096_);
v___f_3104_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3104_, 0, v_setupImports_3090_);
lean_closure_set(v___f_3104_, 1, v_stx_3091_);
lean_closure_set(v___f_3104_, 2, v_origStx_3092_);
lean_closure_set(v___f_3104_, 3, v_toProcessingContext_3096_);
lean_closure_set(v___f_3104_, 4, v___x_3103_);
lean_closure_set(v___f_3104_, 5, v_fileMap_3097_);
lean_closure_set(v___f_3104_, 6, v_parserState_3093_);
lean_closure_set(v___f_3104_, 7, v_a_3094_);
lean_closure_set(v___f_3104_, 8, v___x_3102_);
lean_closure_set(v___f_3104_, 9, v___x_3101_);
lean_closure_set(v___f_3104_, 10, v___x_3099_);
lean_inc(v_endPos_3098_);
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v_endPos_3098_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
v___x_3107_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3107_, 0, lean_box(0));
lean_closure_set(v___x_3107_, 1, v___f_3100_);
lean_closure_set(v___x_3107_, 2, v___f_3104_);
lean_closure_set(v___x_3107_, 3, v_a_3094_);
v___x_3108_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3102_, v___x_3102_, v___x_3106_, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3109_, lean_object* v_stx_3110_, lean_object* v_origStx_3111_, lean_object* v_parserState_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3109_, v_stx_3110_, v_origStx_3111_, v_parserState_3112_, v_a_3113_);
lean_dec_ref(v_a_3113_);
return v_res_3115_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_box(0);
v___x_3117_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3116_);
return v___x_3117_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = 1;
v___x_3123_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3124_ = l_Lean_Name_toString(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3125_ = 0;
v___x_3126_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3127_ = lean_box(0);
v___x_3128_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3129_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3130_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v___x_3128_);
lean_ctor_set(v___x_3130_, 2, v___x_3127_);
lean_ctor_set(v___x_3130_, 3, v___x_3126_);
lean_ctor_set_uint8(v___x_3130_, sizeof(void*)*4, v___x_3125_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3131_, lean_object* v_cmdState_3132_, lean_object* v_a_3133_, lean_object* v_toSnapshot_3134_, lean_object* v_newStx_3135_, lean_object* v_oldCmd_3136_){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v_diagnostics_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3166_; 
v___x_3138_ = lean_io_promise_new();
v___x_3139_ = l_IO_CancelToken_new();
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_oldCmd_3136_);
v___x_3141_ = 1;
v___x_3142_ = lean_box(0);
lean_inc_ref(v___x_3139_);
lean_inc(v___x_3138_);
lean_inc_ref(v_cmdState_3132_);
v___x_3143_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3140_, v_newParserState_3131_, v_cmdState_3132_, v___x_3138_, v___x_3141_, v___x_3139_, v___x_3142_, v_a_3133_);
v_diagnostics_3144_ = lean_ctor_get(v_toSnapshot_3134_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_toSnapshot_3134_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3167_ = lean_ctor_get(v_toSnapshot_3134_, 3);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_toSnapshot_3134_, 2);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_toSnapshot_3134_, 0);
lean_dec(v_unused_3169_);
v___x_3146_ = v_toSnapshot_3134_;
v_isShared_3147_ = v_isSharedCheck_3166_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_diagnostics_3144_);
lean_dec(v_toSnapshot_3134_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3166_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3150_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3151_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3139_);
v___x_3153_ = l_IO_Promise_result_x21___redArg(v___x_3138_);
lean_dec(v___x_3138_);
v___x_3154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3148_);
lean_ctor_set(v___x_3154_, 1, v___x_3149_);
lean_ctor_set(v___x_3154_, 2, v___x_3152_);
lean_ctor_set(v___x_3154_, 3, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_cmdState_3132_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
v___x_3157_ = 0;
v___x_3158_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_newStx_3135_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 3, v___x_3151_);
lean_ctor_set(v___x_3146_, 2, v___x_3148_);
lean_ctor_set(v___x_3146_, 0, v___x_3150_);
v___x_3161_ = v___x_3146_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_diagnostics_3144_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v___x_3151_);
v___x_3161_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*4, v___x_3157_);
v___x_3162_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3159_, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3158_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
lean_ctor_set(v___x_3163_, 2, v___x_3156_);
v___x_3164_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3148_, v___x_3163_);
return v___x_3164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3170_, lean_object* v_cmdState_3171_, lean_object* v_a_3172_, lean_object* v_toSnapshot_3173_, lean_object* v_newStx_3174_, lean_object* v_oldCmd_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3170_, v_cmdState_3171_, v_a_3172_, v_toSnapshot_3173_, v_newStx_3174_, v_oldCmd_3175_);
lean_dec_ref(v_a_3172_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3178_, lean_object* v_a_3179_, lean_object* v_newStx_3180_, lean_object* v___x_3181_, lean_object* v_oldProcessed_3182_){
_start:
{
lean_object* v_result_x3f_3184_; 
v_result_x3f_3184_ = lean_ctor_get(v_oldProcessed_3182_, 2);
if (lean_obj_tag(v_result_x3f_3184_) == 1)
{
lean_object* v_val_3185_; lean_object* v_firstCmdSnap_3186_; lean_object* v_toSnapshot_3187_; lean_object* v_cmdState_3188_; lean_object* v_stx_x3f_3189_; lean_object* v___f_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; 
v_val_3185_ = lean_ctor_get(v_result_x3f_3184_, 0);
lean_inc(v_val_3185_);
v_firstCmdSnap_3186_ = lean_ctor_get(v_val_3185_, 1);
lean_inc_ref(v_firstCmdSnap_3186_);
v_toSnapshot_3187_ = lean_ctor_get(v_oldProcessed_3182_, 0);
lean_inc_ref(v_toSnapshot_3187_);
lean_dec_ref(v_oldProcessed_3182_);
v_cmdState_3188_ = lean_ctor_get(v_val_3185_, 0);
lean_inc_ref(v_cmdState_3188_);
lean_dec(v_val_3185_);
v_stx_x3f_3189_ = lean_ctor_get(v_firstCmdSnap_3186_, 0);
lean_inc(v_stx_x3f_3189_);
lean_inc_ref(v_a_3179_);
v___f_3190_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3190_, 0, v_newParserState_3178_);
lean_closure_set(v___f_3190_, 1, v_cmdState_3188_);
lean_closure_set(v___f_3190_, 2, v_a_3179_);
lean_closure_set(v___f_3190_, 3, v_toSnapshot_3187_);
lean_closure_set(v___f_3190_, 4, v_newStx_3180_);
v___x_3191_ = lean_box(0);
v___x_3192_ = 1;
v___x_3193_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3186_, v___f_3190_, v_stx_x3f_3189_, v___x_3181_, v___x_3191_, v___x_3192_);
return v___x_3193_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v___x_3181_);
lean_dec_ref(v_newParserState_3178_);
v___x_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3194_, 0, v_newStx_3180_);
v___x_3195_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3194_, v_oldProcessed_3182_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3196_, lean_object* v_a_3197_, lean_object* v_newStx_3198_, lean_object* v___x_3199_, lean_object* v_oldProcessed_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3196_, v_a_3197_, v_newStx_3198_, v___x_3199_, v_oldProcessed_3200_);
lean_dec_ref(v_a_3197_);
return v_res_3202_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3203_ = 0;
v___x_3204_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3205_ = lean_box(0);
v___x_3206_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3207_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set(v___x_3208_, 1, v___x_3206_);
lean_ctor_set(v___x_3208_, 2, v___x_3205_);
lean_ctor_set(v___x_3208_, 3, v___x_3204_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*4, v___x_3203_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3209_, lean_object* v_a_3210_, lean_object* v_old_3211_, lean_object* v_newStx_3212_, lean_object* v_newParserState_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_result_x3f_3216_; 
v_result_x3f_3216_ = lean_ctor_get(v_old_3211_, 4);
lean_inc(v_result_x3f_3216_);
if (lean_obj_tag(v_result_x3f_3216_) == 1)
{
lean_object* v_val_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3271_; 
v_val_3217_ = lean_ctor_get(v_result_x3f_3216_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_result_x3f_3216_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3219_ = v_result_x3f_3216_;
v_isShared_3220_ = v_isSharedCheck_3271_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_val_3217_);
lean_dec(v_result_x3f_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3271_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_processedSnap_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3269_; 
v_processedSnap_3221_ = lean_ctor_get(v_val_3217_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_val_3217_);
if (v_isSharedCheck_3269_ == 0)
{
lean_object* v_unused_3270_; 
v_unused_3270_ = lean_ctor_get(v_val_3217_, 0);
lean_dec(v_unused_3270_);
v___x_3223_ = v_val_3217_;
v_isShared_3224_ = v_isSharedCheck_3269_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_processedSnap_3221_);
lean_dec(v_val_3217_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3269_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v_toSnapshot_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3264_; 
v_toSnapshot_3225_ = lean_ctor_get(v_old_3211_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_old_3211_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; lean_object* v_unused_3266_; lean_object* v_unused_3267_; lean_object* v_unused_3268_; 
v_unused_3265_ = lean_ctor_get(v_old_3211_, 4);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_old_3211_, 3);
lean_dec(v_unused_3266_);
v_unused_3267_ = lean_ctor_get(v_old_3211_, 2);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_old_3211_, 1);
lean_dec(v_unused_3268_);
v___x_3227_ = v_old_3211_;
v_isShared_3228_ = v_isSharedCheck_3264_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_toSnapshot_3225_);
lean_dec(v_old_3211_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3264_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_pos_3229_; lean_object* v_endPos_3230_; lean_object* v_stx_x3f_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___f_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v_diagnostics_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3260_; 
v_pos_3229_ = lean_ctor_get(v_newParserState_3213_, 0);
v_endPos_3230_ = lean_ctor_get(v_toProcessingContext_3209_, 3);
v_stx_x3f_3231_ = lean_ctor_get(v_processedSnap_3221_, 0);
lean_inc(v_stx_x3f_3231_);
lean_inc(v_endPos_3230_);
lean_inc(v_pos_3229_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_pos_3229_);
lean_ctor_set(v___x_3232_, 1, v_endPos_3230_);
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_inc_ref(v___x_3233_);
lean_inc(v_newStx_3212_);
lean_inc_ref(v_a_3210_);
lean_inc_ref(v_newParserState_3213_);
v___f_3234_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3234_, 0, v_newParserState_3213_);
lean_closure_set(v___f_3234_, 1, v_a_3210_);
lean_closure_set(v___f_3234_, 2, v_newStx_3212_);
lean_closure_set(v___f_3234_, 3, v___x_3233_);
v___x_3235_ = lean_box(0);
v___x_3236_ = 1;
v___x_3237_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3221_, v___f_3234_, v_stx_x3f_3231_, v___x_3233_, v___x_3235_, v___x_3236_);
v_diagnostics_3238_ = lean_ctor_get(v_toSnapshot_3225_, 1);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_toSnapshot_3225_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; lean_object* v_unused_3262_; lean_object* v_unused_3263_; 
v_unused_3261_ = lean_ctor_get(v_toSnapshot_3225_, 3);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_toSnapshot_3225_, 2);
lean_dec(v_unused_3262_);
v_unused_3263_ = lean_ctor_get(v_toSnapshot_3225_, 0);
lean_dec(v_unused_3263_);
v___x_3240_ = v_toSnapshot_3225_;
v_isShared_3241_ = v_isSharedCheck_3260_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_diagnostics_3238_);
lean_dec(v_toSnapshot_3225_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3260_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3242_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3243_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v___x_3237_);
lean_ctor_set(v___x_3223_, 0, v_newParserState_3213_);
v___x_3245_ = v___x_3223_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_newParserState_3213_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3237_);
v___x_3245_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v___x_3245_);
v___x_3247_ = v___x_3219_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
uint8_t v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3248_ = 0;
v___x_3249_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3212_);
v___x_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_newStx_3212_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 3, v___x_3243_);
lean_ctor_set(v___x_3240_, 2, v___x_3235_);
lean_ctor_set(v___x_3240_, 0, v___x_3242_);
v___x_3252_ = v___x_3240_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_diagnostics_3238_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v___x_3243_);
v___x_3252_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*4, v___x_3248_);
v___x_3253_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3250_, v___x_3252_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 4, v___x_3247_);
lean_ctor_set(v___x_3227_, 3, v_newStx_3212_);
lean_ctor_set(v___x_3227_, 2, v_toProcessingContext_3209_);
lean_ctor_set(v___x_3227_, 1, v___x_3253_);
lean_ctor_set(v___x_3227_, 0, v___x_3249_);
v___x_3255_ = v___x_3227_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_toProcessingContext_3209_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_newStx_3212_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v___x_3247_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
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
lean_dec(v_result_x3f_3216_);
lean_dec_ref(v_newParserState_3213_);
lean_dec(v_newStx_3212_);
lean_dec_ref(v_toProcessingContext_3209_);
return v_old_3211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3272_, lean_object* v_a_3273_, lean_object* v_old_3274_, lean_object* v_newStx_3275_, lean_object* v_newParserState_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3272_, v_a_3273_, v_old_3274_, v_newStx_3275_, v_newParserState_3276_, v___y_3277_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_a_3273_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3280_, lean_object* v_setupImports_3281_, lean_object* v_old_x3f_3282_, lean_object* v___x_3283_, lean_object* v___f_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
lean_inc_ref(v_toProcessingContext_3280_);
v___x_3287_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3280_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3356_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3356_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3356_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v_snd_3292_; lean_object* v_fst_3293_; lean_object* v_fst_3294_; lean_object* v_snd_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3355_; 
v_snd_3292_ = lean_ctor_get(v_a_3288_, 1);
lean_inc(v_snd_3292_);
v_fst_3293_ = lean_ctor_get(v_a_3288_, 0);
lean_inc(v_fst_3293_);
lean_dec(v_a_3288_);
v_fst_3294_ = lean_ctor_get(v_snd_3292_, 0);
v_snd_3295_ = lean_ctor_get(v_snd_3292_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_snd_3292_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3297_ = v_snd_3292_;
v_isShared_3298_ = v_isSharedCheck_3355_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_snd_3295_);
lean_inc(v_fst_3294_);
lean_dec(v_snd_3292_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3355_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint8_t v___x_3299_; 
v___x_3299_ = l_Lean_MessageLog_hasErrors(v_snd_3295_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___y_3302_; 
lean_inc(v_fst_3293_);
v___x_3300_ = l_Lean_Syntax_unsetTrailing(v_fst_3293_);
if (lean_obj_tag(v_old_x3f_3282_) == 1)
{
lean_object* v_val_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3338_; 
v_val_3323_ = lean_ctor_get(v_old_x3f_3282_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_old_x3f_3282_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3325_ = v_old_x3f_3282_;
v_isShared_3326_ = v_isSharedCheck_3338_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_val_3323_);
lean_dec(v_old_x3f_3282_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3338_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_stx_3327_; lean_object* v_result_x3f_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v_stx_3327_ = lean_ctor_get(v_val_3323_, 3);
v_result_x3f_3328_ = lean_ctor_get(v_val_3323_, 4);
lean_inc(v_stx_3327_);
v___x_3329_ = l_Lean_Syntax_unsetTrailing(v_stx_3327_);
lean_inc(v___x_3300_);
v___x_3330_ = l_Lean_Syntax_eqWithInfo(v___x_3300_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_inc(v_result_x3f_3328_);
lean_del_object(v___x_3325_);
lean_dec(v_val_3323_);
lean_dec_ref(v___f_3284_);
if (lean_obj_tag(v_result_x3f_3328_) == 0)
{
lean_dec_ref(v___x_3283_);
v___y_3302_ = v___y_3285_;
goto v___jp_3301_;
}
else
{
lean_object* v_val_3331_; lean_object* v_processedSnap_3332_; lean_object* v___x_3333_; 
v_val_3331_ = lean_ctor_get(v_result_x3f_3328_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v_result_x3f_3328_, 1);
v_processedSnap_3332_ = lean_ctor_get(v_val_3331_, 1);
lean_inc_ref(v_processedSnap_3332_);
lean_dec(v_val_3331_);
v___x_3333_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3283_, v_processedSnap_3332_);
v___y_3302_ = v___y_3285_;
goto v___jp_3301_;
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
lean_dec(v___x_3300_);
lean_del_object(v___x_3297_);
lean_dec(v_snd_3295_);
lean_del_object(v___x_3290_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_setupImports_3281_);
lean_dec_ref(v_toProcessingContext_3280_);
lean_inc_ref(v___y_3285_);
v___x_3334_ = lean_apply_5(v___f_3284_, v_val_3323_, v_fst_3293_, v_fst_3294_, v___y_3285_, lean_box(0));
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3334_);
v___x_3336_ = v___x_3325_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_dec_ref(v___f_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v_old_x3f_3282_);
v___y_3302_ = v___y_3285_;
goto v___jp_3301_;
}
v___jp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3303_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3295_);
lean_inc(v_fst_3294_);
lean_inc(v_fst_3293_);
v___x_3304_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3281_, v___x_3300_, v_fst_3293_, v_fst_3294_, v___y_3302_);
v___x_3305_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3306_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_unsigned_to_nat(32u);
v___x_3309_ = lean_mk_empty_array_with_capacity(v___x_3308_);
lean_dec_ref(v___x_3309_);
v___x_3310_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___x_3304_);
v___x_3312_ = v___x_3297_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_fst_3294_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v___x_3304_);
v___x_3312_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3314_, 0, v___x_3305_);
lean_ctor_set(v___x_3314_, 1, v___x_3306_);
lean_ctor_set(v___x_3314_, 2, v___x_3307_);
lean_ctor_set(v___x_3314_, 3, v___x_3310_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*4, v___x_3299_);
lean_inc(v_fst_3293_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v_fst_3293_);
v___x_3316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3316_, 0, v___x_3305_);
lean_ctor_set(v___x_3316_, 1, v___x_3303_);
lean_ctor_set(v___x_3316_, 2, v___x_3307_);
lean_ctor_set(v___x_3316_, 3, v___x_3310_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*4, v___x_3299_);
v___x_3317_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3315_, v___x_3316_);
v___x_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3314_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
lean_ctor_set(v___x_3318_, 2, v_toProcessingContext_3280_);
lean_ctor_set(v___x_3318_, 3, v_fst_3293_);
lean_ctor_set(v___x_3318_, 4, v___x_3313_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3318_);
v___x_3320_ = v___x_3290_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
lean_del_object(v___x_3297_);
lean_dec(v_fst_3294_);
lean_dec_ref(v___f_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v_old_x3f_3282_);
lean_dec_ref(v_setupImports_3281_);
v___x_3339_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3295_);
v___x_3340_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3341_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_unsigned_to_nat(32u);
v___x_3344_ = lean_mk_empty_array_with_capacity(v___x_3343_);
lean_dec_ref(v___x_3344_);
v___x_3345_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3346_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3346_, 0, v___x_3340_);
lean_ctor_set(v___x_3346_, 1, v___x_3341_);
lean_ctor_set(v___x_3346_, 2, v___x_3342_);
lean_ctor_set(v___x_3346_, 3, v___x_3345_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*4, v___x_3299_);
lean_inc(v_fst_3293_);
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_fst_3293_);
v___x_3348_ = 0;
v___x_3349_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3349_, 0, v___x_3340_);
lean_ctor_set(v___x_3349_, 1, v___x_3339_);
lean_ctor_set(v___x_3349_, 2, v___x_3342_);
lean_ctor_set(v___x_3349_, 3, v___x_3345_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*4, v___x_3348_);
v___x_3350_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3347_, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3346_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
lean_ctor_set(v___x_3351_, 2, v_toProcessingContext_3280_);
lean_ctor_set(v___x_3351_, 3, v_fst_3293_);
lean_ctor_set(v___x_3351_, 4, v___x_3342_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3351_);
v___x_3353_ = v___x_3290_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v___f_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v_old_x3f_3282_);
lean_dec_ref(v_setupImports_3281_);
lean_dec_ref(v_toProcessingContext_3280_);
v_a_3357_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3287_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3287_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3365_, lean_object* v_setupImports_3366_, lean_object* v_old_x3f_3367_, lean_object* v___x_3368_, lean_object* v___f_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3365_, v_setupImports_3366_, v_old_x3f_3367_, v___x_3368_, v___f_3369_, v___y_3370_);
lean_dec_ref(v___y_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3373_, lean_object* v_toProcessingContext_3374_, lean_object* v_x_3375_){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3376_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3373_);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3379_, 0, v_x_3375_);
lean_ctor_set(v___x_3379_, 1, v___x_3376_);
lean_ctor_set(v___x_3379_, 2, v_toProcessingContext_3374_);
lean_ctor_set(v___x_3379_, 3, v___x_3377_);
lean_ctor_set(v___x_3379_, 4, v___x_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3380_, lean_object* v_old_x3f_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_toProcessingContext_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___f_3389_; 
v_toProcessingContext_3384_ = lean_ctor_get(v_a_3382_, 0);
v___x_3385_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3386_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3382_);
lean_inc_ref_n(v_toProcessingContext_3384_, 3);
v___f_3387_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3387_, 0, v_toProcessingContext_3384_);
lean_closure_set(v___f_3387_, 1, v_a_3382_);
lean_inc(v_old_x3f_3381_);
v___f_3388_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3388_, 0, v_toProcessingContext_3384_);
lean_closure_set(v___f_3388_, 1, v_setupImports_3380_);
lean_closure_set(v___f_3388_, 2, v_old_x3f_3381_);
lean_closure_set(v___f_3388_, 3, v___x_3386_);
lean_closure_set(v___f_3388_, 4, v___f_3387_);
v___f_3389_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3389_, 0, v___x_3385_);
lean_closure_set(v___f_3389_, 1, v_toProcessingContext_3384_);
if (lean_obj_tag(v_old_x3f_3381_) == 1)
{
lean_object* v_val_3390_; lean_object* v_result_x3f_3391_; 
v_val_3390_ = lean_ctor_get(v_old_x3f_3381_, 0);
lean_inc(v_val_3390_);
lean_dec_ref_known(v_old_x3f_3381_, 1);
v_result_x3f_3391_ = lean_ctor_get(v_val_3390_, 4);
if (lean_obj_tag(v_result_x3f_3391_) == 1)
{
lean_object* v_stx_3392_; lean_object* v_val_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_stx_3392_ = lean_ctor_get(v_val_3390_, 3);
lean_inc(v_stx_3392_);
v_val_3393_ = lean_ctor_get(v_result_x3f_3391_, 0);
lean_inc(v_val_3390_);
v___x_3394_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3390_);
v___x_3395_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3394_);
if (lean_obj_tag(v___x_3395_) == 1)
{
lean_object* v_val_3396_; 
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3396_);
lean_dec_ref_known(v___x_3395_, 1);
if (lean_obj_tag(v_val_3396_) == 1)
{
lean_object* v_val_3397_; lean_object* v_firstCmdSnap_3398_; lean_object* v___x_3399_; 
v_val_3397_ = lean_ctor_get(v_val_3396_, 0);
lean_inc(v_val_3397_);
lean_dec_ref_known(v_val_3396_, 1);
v_firstCmdSnap_3398_ = lean_ctor_get(v_val_3397_, 1);
lean_inc_ref(v_firstCmdSnap_3398_);
lean_dec(v_val_3397_);
v___x_3399_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3398_);
if (lean_obj_tag(v___x_3399_) == 1)
{
lean_object* v_val_3400_; lean_object* v_nextCmdSnap_x3f_3401_; 
v_val_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_val_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v_nextCmdSnap_x3f_3401_ = lean_ctor_get(v_val_3400_, 4);
lean_inc(v_nextCmdSnap_x3f_3401_);
lean_dec(v_val_3400_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3401_) == 0)
{
lean_object* v___x_3402_; 
lean_dec(v_stx_3392_);
lean_dec(v_val_3390_);
v___x_3402_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3402_;
}
else
{
lean_object* v_val_3403_; lean_object* v___x_3404_; 
v_val_3403_ = lean_ctor_get(v_nextCmdSnap_x3f_3401_, 0);
lean_inc(v_val_3403_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3401_, 1);
v___x_3404_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3403_);
if (lean_obj_tag(v___x_3404_) == 1)
{
lean_object* v_val_3405_; lean_object* v_parserState_3406_; lean_object* v_pos_3407_; uint8_t v___x_3408_; 
v_val_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v_parserState_3406_ = lean_ctor_get(v_val_3405_, 2);
lean_inc_ref(v_parserState_3406_);
lean_dec(v_val_3405_);
v_pos_3407_ = lean_ctor_get(v_parserState_3406_, 0);
lean_inc(v_pos_3407_);
lean_dec_ref(v_parserState_3406_);
v___x_3408_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3407_, v_a_3382_);
lean_dec(v_pos_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
lean_dec(v_stx_3392_);
lean_dec(v_val_3390_);
v___x_3409_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3409_;
}
else
{
lean_object* v_parserState_3410_; lean_object* v___x_3411_; 
lean_dec_ref(v___f_3389_);
lean_dec_ref(v___f_3388_);
v_parserState_3410_ = lean_ctor_get(v_val_3393_, 0);
lean_inc_ref(v_parserState_3410_);
lean_inc_ref(v_toProcessingContext_3384_);
v___x_3411_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3384_, v_a_3382_, v_val_3390_, v_stx_3392_, v_parserState_3410_, v_a_3382_);
return v___x_3411_;
}
}
else
{
lean_object* v___x_3412_; 
lean_dec(v___x_3404_);
lean_dec(v_stx_3392_);
lean_dec(v_val_3390_);
v___x_3412_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3412_;
}
}
}
else
{
lean_object* v___x_3413_; 
lean_dec(v___x_3399_);
lean_dec(v_stx_3392_);
lean_dec(v_val_3390_);
v___x_3413_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3413_;
}
}
else
{
lean_object* v___x_3414_; 
lean_dec(v_val_3396_);
lean_dec(v_stx_3392_);
lean_dec(v_val_3390_);
v___x_3414_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3414_;
}
}
else
{
lean_object* v___x_3415_; 
lean_dec(v___x_3395_);
lean_dec(v_stx_3392_);
lean_dec(v_val_3390_);
v___x_3415_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3415_;
}
}
else
{
lean_object* v___x_3416_; 
lean_dec(v_val_3390_);
v___x_3416_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3416_;
}
}
else
{
lean_object* v___x_3417_; 
lean_dec(v_old_x3f_3381_);
v___x_3417_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3389_, v___f_3388_, v_a_3382_);
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3418_, lean_object* v_old_x3f_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3418_, v_old_x3f_3419_, v_a_3420_);
lean_dec_ref(v_a_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3423_, lean_object* v_old_x3f_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v___x_3427_; 
lean_inc(v_old_x3f_3424_);
v___x_3427_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3427_, 0, v_setupImports_3423_);
lean_closure_set(v___x_3427_, 1, v_old_x3f_3424_);
if (lean_obj_tag(v_old_x3f_3424_) == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_box(0);
v___x_3429_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3427_, v___x_3428_, v_a_3425_);
return v___x_3429_;
}
else
{
lean_object* v_val_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3439_; 
v_val_3430_ = lean_ctor_get(v_old_x3f_3424_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_old_x3f_3424_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3432_ = v_old_x3f_3424_;
v_isShared_3433_ = v_isSharedCheck_3439_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_val_3430_);
lean_dec(v_old_x3f_3424_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3439_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_ictx_3434_; lean_object* v___x_3436_; 
v_ictx_3434_ = lean_ctor_get(v_val_3430_, 2);
lean_inc_ref(v_ictx_3434_);
lean_dec(v_val_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v_ictx_3434_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_ictx_3434_);
v___x_3436_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3427_, v___x_3436_, v_a_3425_);
return v___x_3437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3440_, lean_object* v_old_x3f_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Language_Lean_process(v_setupImports_3440_, v_old_x3f_3441_, v_a_3442_);
lean_dec_ref(v_a_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3445_, lean_object* v_parserState_3446_, lean_object* v_commandState_3447_, lean_object* v_old_x3f_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3458_; 
v___x_3450_ = lean_io_promise_new();
v___x_3451_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3448_) == 0)
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_box(0);
v___y_3458_ = v___x_3473_;
goto v___jp_3457_;
}
else
{
lean_object* v_val_3474_; lean_object* v_snd_3475_; lean_object* v___x_3476_; 
v_val_3474_ = lean_ctor_get(v_old_x3f_3448_, 0);
v_snd_3475_ = lean_ctor_get(v_val_3474_, 1);
lean_inc(v_snd_3475_);
v___x_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3476_, 0, v_snd_3475_);
v___y_3458_ = v___x_3476_;
goto v___jp_3457_;
}
v___jp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3453_, v___y_3454_, v_inputCtx_3445_);
lean_dec(v___x_3455_);
v___x_3456_ = l_IO_Promise_result_x21___redArg(v___x_3450_);
lean_dec(v___x_3450_);
return v___x_3456_;
}
v___jp_3457_:
{
uint8_t v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3459_ = 1;
v___x_3460_ = lean_box(0);
v___x_3461_ = lean_box(v___x_3459_);
lean_inc(v___x_3450_);
v___x_3462_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3462_, 0, v___y_3458_);
lean_closure_set(v___x_3462_, 1, v_parserState_3446_);
lean_closure_set(v___x_3462_, 2, v_commandState_3447_);
lean_closure_set(v___x_3462_, 3, v___x_3450_);
lean_closure_set(v___x_3462_, 4, v___x_3461_);
lean_closure_set(v___x_3462_, 5, v___x_3451_);
lean_closure_set(v___x_3462_, 6, v___x_3460_);
if (lean_obj_tag(v_old_x3f_3448_) == 0)
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_box(0);
v___y_3453_ = v___x_3462_;
v___y_3454_ = v___x_3463_;
goto v___jp_3452_;
}
else
{
lean_object* v_val_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3472_; 
v_val_3464_ = lean_ctor_get(v_old_x3f_3448_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_old_x3f_3448_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3466_ = v_old_x3f_3448_;
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_val_3464_);
lean_dec(v_old_x3f_3448_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v_fst_3468_; lean_object* v___x_3470_; 
v_fst_3468_ = lean_ctor_get(v_val_3464_, 0);
lean_inc(v_fst_3468_);
lean_dec(v_val_3464_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v_fst_3468_);
v___x_3470_ = v___x_3466_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_fst_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
v___y_3453_ = v___x_3462_;
v___y_3454_ = v___x_3470_;
goto v___jp_3452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3477_, lean_object* v_parserState_3478_, lean_object* v_commandState_3479_, lean_object* v_old_x3f_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3477_, v_parserState_3478_, v_commandState_3479_, v_old_x3f_3480_);
lean_dec_ref(v_inputCtx_3477_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3483_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3484_; 
v_nextCmdSnap_x3f_3484_ = lean_ctor_get(v_snap_3483_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3484_) == 1)
{
lean_object* v_val_3485_; lean_object* v___x_3486_; 
lean_inc_ref(v_nextCmdSnap_x3f_3484_);
lean_dec_ref(v_snap_3483_);
v_val_3485_ = lean_ctor_get(v_nextCmdSnap_x3f_3484_, 0);
lean_inc(v_val_3485_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3484_, 1);
v___x_3486_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3485_);
v_snap_3483_ = v___x_3486_;
goto _start;
}
else
{
lean_object* v_elabSnap_3488_; lean_object* v_resultSnap_3489_; lean_object* v___x_3490_; lean_object* v_cmdState_3491_; lean_object* v___x_3492_; 
v_elabSnap_3488_ = lean_ctor_get(v_snap_3483_, 3);
lean_inc_ref(v_elabSnap_3488_);
lean_dec_ref(v_snap_3483_);
v_resultSnap_3489_ = lean_ctor_get(v_elabSnap_3488_, 2);
lean_inc_ref(v_resultSnap_3489_);
lean_dec_ref(v_elabSnap_3488_);
v___x_3490_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3489_);
v_cmdState_3491_ = lean_ctor_get(v___x_3490_, 1);
lean_inc_ref(v_cmdState_3491_);
lean_dec(v___x_3490_);
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v_cmdState_3491_);
return v___x_3492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3493_){
_start:
{
lean_object* v_result_x3f_3494_; 
v_result_x3f_3494_ = lean_ctor_get(v_snap_3493_, 4);
lean_inc(v_result_x3f_3494_);
lean_dec_ref(v_snap_3493_);
if (lean_obj_tag(v_result_x3f_3494_) == 0)
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_box(0);
return v___x_3495_;
}
else
{
lean_object* v_val_3496_; lean_object* v_processedSnap_3497_; lean_object* v___x_3498_; lean_object* v_result_x3f_3499_; 
v_val_3496_ = lean_ctor_get(v_result_x3f_3494_, 0);
lean_inc(v_val_3496_);
lean_dec_ref_known(v_result_x3f_3494_, 1);
v_processedSnap_3497_ = lean_ctor_get(v_val_3496_, 1);
lean_inc_ref(v_processedSnap_3497_);
lean_dec(v_val_3496_);
v___x_3498_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3497_);
v_result_x3f_3499_ = lean_ctor_get(v___x_3498_, 2);
lean_inc(v_result_x3f_3499_);
lean_dec(v___x_3498_);
if (lean_obj_tag(v_result_x3f_3499_) == 0)
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_box(0);
return v___x_3500_;
}
else
{
lean_object* v_val_3501_; lean_object* v_firstCmdSnap_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_val_3501_ = lean_ctor_get(v_result_x3f_3499_, 0);
lean_inc(v_val_3501_);
lean_dec_ref_known(v_result_x3f_3499_, 1);
v_firstCmdSnap_3502_ = lean_ctor_get(v_val_3501_, 1);
lean_inc_ref(v_firstCmdSnap_3502_);
lean_dec(v_val_3501_);
v___x_3503_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3502_);
v___x_3504_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3503_);
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3505_, lean_object* v_snap_3506_, lean_object* v_acc_3507_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3508_; lean_object* v_acc_3509_; 
v_nextCmdSnap_x3f_3508_ = lean_ctor_get(v_snap_3506_, 4);
lean_inc(v_nextCmdSnap_x3f_3508_);
lean_inc(v_f_3505_);
v_acc_3509_ = lean_apply_2(v_f_3505_, v_acc_3507_, v_snap_3506_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3508_) == 1)
{
lean_object* v_val_3510_; lean_object* v___x_3511_; 
v_val_3510_ = lean_ctor_get(v_nextCmdSnap_x3f_3508_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3508_, 1);
v___x_3511_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3510_);
v_snap_3506_ = v___x_3511_;
v_acc_3507_ = v_acc_3509_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3508_);
lean_dec(v_f_3505_);
return v_acc_3509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3513_, lean_object* v_f_3514_, lean_object* v_snap_3515_, lean_object* v_acc_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3514_, v_snap_3515_, v_acc_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3518_, lean_object* v_init_3519_, lean_object* v_f_3520_){
_start:
{
lean_object* v_result_x3f_3521_; 
v_result_x3f_3521_ = lean_ctor_get(v_snap_3518_, 4);
lean_inc(v_result_x3f_3521_);
lean_dec_ref(v_snap_3518_);
if (lean_obj_tag(v_result_x3f_3521_) == 0)
{
lean_object* v___x_3522_; 
lean_dec(v_f_3520_);
lean_dec(v_init_3519_);
v___x_3522_ = lean_box(0);
return v___x_3522_;
}
else
{
lean_object* v_val_3523_; lean_object* v_processedSnap_3524_; lean_object* v___x_3525_; lean_object* v_result_x3f_3526_; 
v_val_3523_ = lean_ctor_get(v_result_x3f_3521_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v_result_x3f_3521_, 1);
v_processedSnap_3524_ = lean_ctor_get(v_val_3523_, 1);
lean_inc_ref(v_processedSnap_3524_);
lean_dec(v_val_3523_);
v___x_3525_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3524_);
v_result_x3f_3526_ = lean_ctor_get(v___x_3525_, 2);
lean_inc(v_result_x3f_3526_);
lean_dec(v___x_3525_);
if (lean_obj_tag(v_result_x3f_3526_) == 0)
{
lean_object* v___x_3527_; 
lean_dec(v_f_3520_);
lean_dec(v_init_3519_);
v___x_3527_ = lean_box(0);
return v___x_3527_;
}
else
{
lean_object* v_val_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3538_; 
v_val_3528_ = lean_ctor_get(v_result_x3f_3526_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_result_x3f_3526_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3530_ = v_result_x3f_3526_;
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_val_3528_);
lean_dec(v_result_x3f_3526_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_firstCmdSnap_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v_firstCmdSnap_3532_ = lean_ctor_get(v_val_3528_, 1);
lean_inc_ref(v_firstCmdSnap_3532_);
lean_dec(v_val_3528_);
v___x_3533_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3532_);
v___x_3534_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3520_, v___x_3533_, v_init_3519_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3534_);
v___x_3536_ = v___x_3530_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3539_, lean_object* v_snap_3540_, lean_object* v_init_3541_, lean_object* v_f_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3540_, v_init_3541_, v_f_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = 1;
v___x_3550_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3551_ = l_Lean_Name_toString(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3552_ = 0;
v___x_3553_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3554_ = lean_box(0);
v___x_3555_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3556_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3557_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___x_3555_);
lean_ctor_set(v___x_3557_, 2, v___x_3554_);
lean_ctor_set(v___x_3557_, 3, v___x_3553_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*4, v___x_3552_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3559_ = lean_box(0);
v___x_3560_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3559_, v___x_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3561_){
_start:
{
lean_object* v_result_x3f_3562_; 
v_result_x3f_3562_ = lean_ctor_get(v_snap_3561_, 4);
lean_inc(v_result_x3f_3562_);
if (lean_obj_tag(v_result_x3f_3562_) == 1)
{
lean_object* v_val_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3638_; 
v_val_3563_ = lean_ctor_get(v_result_x3f_3562_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_result_x3f_3562_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3565_ = v_result_x3f_3562_;
v_isShared_3566_ = v_isSharedCheck_3638_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_val_3563_);
lean_dec(v_result_x3f_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3638_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v_toSnapshot_3567_; lean_object* v_metaSnap_3568_; lean_object* v_ictx_3569_; lean_object* v_stx_3570_; lean_object* v_parserState_3571_; lean_object* v_processedSnap_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3637_; 
v_toSnapshot_3567_ = lean_ctor_get(v_snap_3561_, 0);
v_metaSnap_3568_ = lean_ctor_get(v_snap_3561_, 1);
v_ictx_3569_ = lean_ctor_get(v_snap_3561_, 2);
v_stx_3570_ = lean_ctor_get(v_snap_3561_, 3);
v_parserState_3571_ = lean_ctor_get(v_val_3563_, 0);
v_processedSnap_3572_ = lean_ctor_get(v_val_3563_, 1);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_val_3563_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3574_ = v_val_3563_;
v_isShared_3575_ = v_isSharedCheck_3637_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_processedSnap_3572_);
lean_inc(v_parserState_3571_);
lean_dec(v_val_3563_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3637_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_processed_3576_; lean_object* v_result_x3f_3577_; 
v_processed_3576_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3572_);
v_result_x3f_3577_ = lean_ctor_get(v_processed_3576_, 2);
lean_inc(v_result_x3f_3577_);
if (lean_obj_tag(v_result_x3f_3577_) == 1)
{
lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3631_; 
lean_inc(v_stx_3570_);
lean_inc_ref(v_ictx_3569_);
lean_inc_ref(v_metaSnap_3568_);
lean_inc_ref(v_toSnapshot_3567_);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_snap_3561_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; lean_object* v_unused_3633_; lean_object* v_unused_3634_; lean_object* v_unused_3635_; lean_object* v_unused_3636_; 
v_unused_3632_ = lean_ctor_get(v_snap_3561_, 4);
lean_dec(v_unused_3632_);
v_unused_3633_ = lean_ctor_get(v_snap_3561_, 3);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v_snap_3561_, 2);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_snap_3561_, 1);
lean_dec(v_unused_3635_);
v_unused_3636_ = lean_ctor_get(v_snap_3561_, 0);
lean_dec(v_unused_3636_);
v___x_3579_ = v_snap_3561_;
v_isShared_3580_ = v_isSharedCheck_3631_;
goto v_resetjp_3578_;
}
else
{
lean_dec(v_snap_3561_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3631_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_val_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3630_; 
v_val_3581_ = lean_ctor_get(v_result_x3f_3577_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_result_x3f_3577_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3583_ = v_result_x3f_3577_;
v_isShared_3584_ = v_isSharedCheck_3630_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_val_3581_);
lean_dec(v_result_x3f_3577_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3630_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v_toSnapshot_3585_; lean_object* v_metaSnap_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3628_; 
v_toSnapshot_3585_ = lean_ctor_get(v_processed_3576_, 0);
v_metaSnap_3586_ = lean_ctor_get(v_processed_3576_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_processed_3576_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v_processed_3576_, 2);
lean_dec(v_unused_3629_);
v___x_3588_ = v_processed_3576_;
v_isShared_3589_ = v_isSharedCheck_3628_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_metaSnap_3586_);
lean_inc(v_toSnapshot_3585_);
lean_dec(v_processed_3576_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3628_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v_cmdState_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3626_; 
v_cmdState_3590_ = lean_ctor_get(v_val_3581_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_val_3581_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v_val_3581_, 1);
lean_dec(v_unused_3627_);
v___x_3592_ = v_val_3581_;
v_isShared_3593_ = v_isSharedCheck_3626_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_cmdState_3590_);
lean_dec(v_val_3581_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3626_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_resultSnap_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_elabSnap_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v_termCmd_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3594_ = lean_box(0);
v___x_3595_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3596_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3590_);
v_resultSnap_3597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3597_, 0, v___x_3595_);
lean_ctor_set(v_resultSnap_3597_, 1, v_cmdState_3590_);
lean_ctor_set(v_resultSnap_3597_, 2, v___x_3596_);
v___x_3598_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3599_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3594_, v_resultSnap_3597_);
v___x_3600_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3601_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3602_, 0, v___x_3595_);
lean_ctor_set(v_elabSnap_3602_, 1, v___x_3598_);
lean_ctor_set(v_elabSnap_3602_, 2, v___x_3599_);
lean_ctor_set(v_elabSnap_3602_, 3, v___x_3600_);
lean_ctor_set(v_elabSnap_3602_, 4, v___x_3601_);
v___x_3603_ = lean_box(0);
v___x_3604_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3605_, 0, v___x_3595_);
lean_ctor_set(v_termCmd_3605_, 1, v___x_3603_);
lean_ctor_set(v_termCmd_3605_, 2, v___x_3604_);
lean_ctor_set(v_termCmd_3605_, 3, v_elabSnap_3602_);
lean_ctor_set(v_termCmd_3605_, 4, v___x_3594_);
v___x_3606_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3594_, v_termCmd_3605_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 1, v___x_3606_);
v___x_3608_ = v___x_3592_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_cmdState_3590_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3608_);
v___x_3610_ = v___x_3583_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v_newProcessed_3612_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 2, v___x_3610_);
v_newProcessed_3612_ = v___x_3588_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_toSnapshot_3585_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_metaSnap_3586_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v___x_3610_);
v_newProcessed_3612_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3613_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3594_, v_newProcessed_3612_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v___x_3613_);
v___x_3615_ = v___x_3574_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_parserState_3571_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3615_);
v___x_3617_ = v___x_3565_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 4, v___x_3617_);
v___x_3619_ = v___x_3579_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_toSnapshot_3567_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_metaSnap_3568_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_ictx_3569_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_stx_3570_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
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
lean_dec(v_result_x3f_3577_);
lean_dec(v_processed_3576_);
lean_del_object(v___x_3574_);
lean_dec_ref(v_parserState_3571_);
lean_del_object(v___x_3565_);
return v_snap_3561_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3562_);
return v_snap_3561_;
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

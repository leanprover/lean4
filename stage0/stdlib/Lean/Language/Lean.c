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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(lean_object* v_00_u03b1_1_, lean_object* v_act_2_, lean_object* v_ctx_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_2(v_act_2_, v_ctx_3_, lean_box(0));
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_2_ = stack[1].m_obj;
lean_object* v_ctx_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(lean_box(0), v_act_2_, v_ctx_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0___boxed(lean_object* v_00_u03b1_8_, lean_object* v_act_9_, lean_object* v_ctx_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___lam__0(v_00_u03b1_8_, v_act_9_, v_ctx_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___lam__0(lean_object* v_00_u03b1_15_, lean_object* v_act_16_, lean_object* v_ctx_17_){
_start:
{
lean_object* v_toProcessingContext_18_; lean_object* v___x_19_; 
v_toProcessingContext_18_ = lean_ctor_get(v_ctx_17_, 0);
lean_inc_ref(v_toProcessingContext_18_);
lean_dec_ref(v_ctx_17_);
v___x_19_ = lean_apply_1(v_act_16_, v_toProcessingContext_18_);
return v___x_19_;
}
}
lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg(){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = ((lean_object*)(l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0));
return v___f_22_;
}
}
LEAN_EXPORT void l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_23_;
v_res_23_ = l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg();
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___boxed(lean_object* v___dummy_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg();
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(lean_object* v_m_26_){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___redArg___closed__0));
return v___f_27_;
}
}
lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg(lean_object* v_act_28_, lean_object* v_oldInputCtx_x3f_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___y_33_; 
if (lean_obj_tag(v_oldInputCtx_x3f_29_) == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
v___y_33_ = v___x_36_;
goto v___jp_32_;
}
else
{
lean_object* v_val_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_47_; 
v_val_37_ = lean_ctor_get(v_oldInputCtx_x3f_29_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_oldInputCtx_x3f_29_);
if (v_isSharedCheck_47_ == 0)
{
v___x_39_ = v_oldInputCtx_x3f_29_;
v_isShared_40_ = v_isSharedCheck_47_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_val_37_);
lean_dec(v_oldInputCtx_x3f_29_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_47_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_inputString_41_; lean_object* v_inputString_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v_inputString_41_ = lean_ctor_get(v_val_37_, 0);
lean_inc_ref(v_inputString_41_);
lean_dec(v_val_37_);
v_inputString_42_ = lean_ctor_get(v_a_30_, 0);
v___x_43_ = l_String_firstDiffPos(v_inputString_41_, v_inputString_42_);
lean_dec_ref(v_inputString_41_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_43_);
v___x_45_ = v___x_39_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
v___y_33_ = v___x_45_;
goto v___jp_32_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_inc_ref(v_a_30_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v_a_30_);
lean_ctor_set(v___x_34_, 1, v___y_33_);
v___x_35_ = lean_apply_2(v_act_28_, v___x_34_, lean_box(0));
return v___x_35_;
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_LeanProcessingM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_28_ = stack[0].m_obj;
lean_object* v_oldInputCtx_x3f_29_ = stack[1].m_obj;
lean_object* v_a_30_ = stack[2].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_28_, v_oldInputCtx_x3f_29_, v_a_30_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___redArg___boxed(lean_object* v_act_49_, lean_object* v_oldInputCtx_x3f_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_49_, v_oldInputCtx_x3f_50_, v_a_51_);
lean_dec_ref(v_a_51_);
return v_res_53_;
}
}
lean_object* l_Lean_Language_Lean_LeanProcessingM_run(lean_object* v_00_u03b1_54_, lean_object* v_act_55_, lean_object* v_oldInputCtx_x3f_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v_act_55_, v_oldInputCtx_x3f_56_, v_a_57_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Lean_Language_Lean_LeanProcessingM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_55_ = stack[1].m_obj;
lean_object* v_oldInputCtx_x3f_56_ = stack[2].m_obj;
lean_object* v_a_57_ = stack[3].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Language_Lean_LeanProcessingM_run(lean_box(0), v_act_55_, v_oldInputCtx_x3f_56_, v_a_57_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___boxed(lean_object* v_00_u03b1_61_, lean_object* v_act_62_, lean_object* v_oldInputCtx_x3f_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Language_Lean_LeanProcessingM_run(v_00_u03b1_61_, v_act_62_, v_oldInputCtx_x3f_63_, v_a_64_);
lean_dec_ref(v_a_64_);
return v_res_66_;
}
}
uint8_t l_Lean_Language_Lean_isBeforeEditPos(lean_object* v_pos_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_firstDiffPos_x3f_70_; 
v_firstDiffPos_x3f_70_ = lean_ctor_get(v_a_68_, 1);
if (lean_obj_tag(v_firstDiffPos_x3f_70_) == 0)
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_val_72_ = lean_ctor_get(v_firstDiffPos_x3f_70_, 0);
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_pos_67_, v___x_73_);
v___x_75_ = lean_nat_dec_le(v___x_74_, v_val_72_);
lean_dec(v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_isBeforeEditPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_pos_67_ = stack[0].m_obj;
lean_object* v_a_68_ = stack[1].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_67_, v_a_68_);
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object* v_pos_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_77_, v_a_78_);
lean_dec_ref(v_a_78_);
lean_dec(v_pos_77_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13(void){
_start:
{
uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = 1;
v___x_114_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12));
v___x_115_ = l_Lean_Name_toString(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(32u);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15(void){
_start:
{
size_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_119_ = ((size_t)5ULL);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_unsigned_to_nat(32u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_124_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_120_);
lean_ctor_set(v___x_124_, 3, v___x_120_);
lean_ctor_set_usize(v___x_124_, 4, v___x_119_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16(void){
_start:
{
lean_object* v___x_125_; uint64_t v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15);
v___x_126_ = 0ULL;
v___x_127_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set_uint64(v___x_127_, sizeof(void*)*1, v___x_126_);
return v___x_127_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(lean_object* v_ex_128_, lean_object* v_act_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_132_; 
lean_inc_ref(v_a_130_);
v___x_132_ = lean_apply_2(v_act_129_, v_a_130_, lean_box(0));
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; 
lean_dec(v_ex_128_);
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_132_, 1);
return v_a_133_;
}
else
{
lean_object* v_a_134_; lean_object* v_toProcessingContext_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_a_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_132_, 1);
v_toProcessingContext_135_ = lean_ctor_get(v_a_130_, 0);
v___x_136_ = lean_io_error_to_string(v_a_134_);
v___x_137_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_136_, v_toProcessingContext_135_);
v___x_138_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13);
v___x_139_ = lean_box(0);
v___x_140_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_142_, 0, v___x_138_);
lean_ctor_set(v___x_142_, 1, v___x_137_);
lean_ctor_set(v___x_142_, 2, v___x_139_);
lean_ctor_set(v___x_142_, 3, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*4, v___x_141_);
v___x_143_ = lean_apply_1(v_ex_128_, v___x_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_128_ = stack[0].m_obj;
lean_object* v_act_129_ = stack[1].m_obj;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_res_144_;
v_res_144_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_128_, v_act_129_, v_a_130_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___boxed(lean_object* v_ex_145_, lean_object* v_act_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_145_, v_act_146_, v_a_147_);
lean_dec_ref(v_a_147_);
return v_res_149_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object* v_00_u03b1_150_, lean_object* v_ex_151_, lean_object* v_act_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_151_, v_act_152_, v_a_153_);
return v___x_155_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_151_ = stack[1].m_obj;
lean_object* v_act_152_ = stack[2].m_obj;
lean_object* v_a_153_ = stack[3].m_obj;
lean_object* v_res_156_;
v_res_156_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_box(0), v_ex_151_, v_act_152_, v_a_153_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed(lean_object* v_00_u03b1_157_, lean_object* v_ex_158_, lean_object* v_act_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(v_00_u03b1_157_, v_ex_158_, v_act_159_, v_a_160_);
lean_dec_ref(v_a_160_);
return v_res_162_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(lean_object* v_o_166_, lean_object* v_k_167_, uint8_t v_v_168_){
_start:
{
lean_object* v_map_169_; uint8_t v_hasTrace_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_184_; 
v_map_169_ = lean_ctor_get(v_o_166_, 0);
v_hasTrace_170_ = lean_ctor_get_uint8(v_o_166_, sizeof(void*)*1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_o_166_);
if (v_isSharedCheck_184_ == 0)
{
v___x_172_ = v_o_166_;
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_map_169_);
lean_dec(v_o_166_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_174_, 0, v_v_168_);
lean_inc(v_k_167_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_167_, v___x_174_, v_map_169_);
if (v_hasTrace_170_ == 0)
{
lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_179_; 
v___x_176_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_177_ = l_Lean_Name_isPrefixOf(v___x_176_, v_k_167_);
lean_dec(v_k_167_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_179_ = v___x_172_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_175_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_177_);
return v___x_179_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_k_167_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_182_ = v___x_172_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_175_);
lean_ctor_set_uint8(v_reuseFailAlloc_183_, sizeof(void*)*1, v_hasTrace_170_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_166_ = stack[0].m_obj;
lean_object* v_k_167_ = stack[1].m_obj;
uint8_t v_v_168_ = stack[2].m_num;
lean_object* v_res_185_;
v_res_185_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_o_166_, v_k_167_, v_v_168_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___boxed(lean_object* v_o_186_, lean_object* v_k_187_, lean_object* v_v_188_){
_start:
{
uint8_t v_v_boxed_189_; lean_object* v_res_190_; 
v_v_boxed_189_ = lean_unbox(v_v_188_);
v_res_190_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_o_186_, v_k_187_, v_v_boxed_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(lean_object* v_o_191_, lean_object* v_k_192_, lean_object* v_v_193_){
_start:
{
lean_object* v_map_194_; uint8_t v_hasTrace_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_209_; 
v_map_194_ = lean_ctor_get(v_o_191_, 0);
v_hasTrace_195_ = lean_ctor_get_uint8(v_o_191_, sizeof(void*)*1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_o_191_);
if (v_isSharedCheck_209_ == 0)
{
v___x_197_ = v_o_191_;
v_isShared_198_ = v_isSharedCheck_209_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_map_194_);
lean_dec(v_o_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_209_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_199_, 0, v_v_193_);
lean_inc(v_k_192_);
v___x_200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_192_, v___x_199_, v_map_194_);
if (v_hasTrace_195_ == 0)
{
lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_204_; 
v___x_201_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_202_ = l_Lean_Name_isPrefixOf(v___x_201_, v_k_192_);
lean_dec(v_k_192_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_204_ = v___x_197_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_200_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*1, v___x_202_);
return v___x_204_;
}
}
else
{
lean_object* v___x_207_; 
lean_dec(v_k_192_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_207_ = v___x_197_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_208_, sizeof(void*)*1, v_hasTrace_195_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(lean_object* v_o_210_, lean_object* v_k_211_, lean_object* v_v_212_){
_start:
{
lean_object* v_map_213_; uint8_t v_hasTrace_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_228_; 
v_map_213_ = lean_ctor_get(v_o_210_, 0);
v_hasTrace_214_ = lean_ctor_get_uint8(v_o_210_, sizeof(void*)*1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_o_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_216_ = v_o_210_;
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_map_213_);
lean_dec(v_o_210_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v_v_212_);
lean_inc(v_k_211_);
v___x_219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_211_, v___x_218_, v_map_213_);
if (v_hasTrace_214_ == 0)
{
lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_223_; 
v___x_220_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_221_ = l_Lean_Name_isPrefixOf(v___x_220_, v_k_211_);
lean_dec(v_k_211_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_223_ = v___x_216_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_219_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_221_);
return v___x_223_;
}
}
else
{
lean_object* v___x_226_; 
lean_dec(v_k_211_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_226_ = v___x_216_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*1, v_hasTrace_214_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
lean_object* l_Lean_Language_Lean_setOption(lean_object* v_opts_236_, lean_object* v_decl_237_, lean_object* v_name_238_, lean_object* v_val_239_){
_start:
{
lean_object* v_defValue_241_; 
v_defValue_241_ = lean_ctor_get(v_decl_237_, 2);
lean_inc_ref(v_defValue_241_);
lean_dec_ref(v_decl_237_);
switch(lean_obj_tag(v_defValue_241_))
{
case 1:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
lean_dec_ref_known(v_defValue_241_, 0);
v___x_242_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__0));
v___x_243_ = lean_string_dec_eq(v_val_239_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__1));
v___x_245_ = lean_string_dec_eq(v_val_239_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v_name_238_);
lean_dec_ref(v_opts_236_);
v___x_246_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_247_ = lean_string_append(v___x_246_, v_val_239_);
lean_dec_ref(v_val_239_);
v___x_248_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__3));
v___x_249_ = lean_string_append(v___x_247_, v___x_248_);
v___x_250_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v_val_239_);
v___x_252_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_236_, v_name_238_, v___x_243_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref(v_val_239_);
v___x_254_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_236_, v_name_238_, v___x_243_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
case 3:
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_280_; 
v_isSharedCheck_280_ = !lean_is_exclusive(v_defValue_241_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_defValue_241_, 0);
lean_dec(v_unused_281_);
v___x_257_ = v_defValue_241_;
v_isShared_258_ = v_isSharedCheck_280_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_defValue_241_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_280_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_string_utf8_byte_size(v_val_239_);
lean_inc_ref(v_val_239_);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v_val_239_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
v___x_262_ = l_String_Slice_toNat_x3f(v___x_261_);
lean_dec_ref_known(v___x_261_, 3);
if (lean_obj_tag(v___x_262_) == 1)
{
lean_object* v_val_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
lean_del_object(v___x_257_);
lean_dec_ref(v_val_239_);
v_val_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_271_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_val_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(v_opts_236_, v_name_238_, v_val_263_);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 0);
lean_ctor_set(v___x_265_, 0, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec(v___x_262_);
lean_dec(v_name_238_);
lean_dec_ref(v_opts_236_);
v___x_272_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_273_ = lean_string_append(v___x_272_, v_val_239_);
lean_dec_ref(v_val_239_);
v___x_274_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__4));
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 18);
lean_ctor_set(v___x_257_, 0, v___x_275_);
v___x_277_ = v___x_257_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_279_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
}
case 0:
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_isSharedCheck_289_ = !lean_is_exclusive(v_defValue_241_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v_defValue_241_, 0);
lean_dec(v_unused_290_);
v___x_283_ = v_defValue_241_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_defValue_241_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(v_opts_236_, v_name_238_, v_val_239_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
default: 
{
lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_defValue_241_);
lean_dec_ref(v_val_239_);
lean_dec_ref(v_opts_236_);
v___x_291_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__5));
v___x_292_ = 1;
v___x_293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_238_, v___x_292_);
v___x_294_ = lean_string_append(v___x_291_, v___x_293_);
lean_dec_ref(v___x_293_);
v___x_295_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__6));
v___x_296_ = lean_string_append(v___x_294_, v___x_295_);
v___x_297_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_setOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_236_ = stack[0].m_obj;
lean_object* v_decl_237_ = stack[1].m_obj;
lean_object* v_name_238_ = stack[2].m_obj;
lean_object* v_val_239_ = stack[3].m_obj;
lean_object* v_res_299_;
v_res_299_ = l_Lean_Language_Lean_setOption(v_opts_236_, v_decl_237_, v_name_238_, v_val_239_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption___boxed(lean_object* v_opts_300_, lean_object* v_decl_301_, lean_object* v_name_302_, lean_object* v_val_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Language_Lean_setOption(v_opts_300_, v_decl_301_, v_name_302_, v_val_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(lean_object* v_o_306_, lean_object* v_k_307_, lean_object* v_v_308_){
_start:
{
lean_object* v_map_309_; uint8_t v_hasTrace_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_323_; 
v_map_309_ = lean_ctor_get(v_o_306_, 0);
v_hasTrace_310_ = lean_ctor_get_uint8(v_o_306_, sizeof(void*)*1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_o_306_);
if (v_isSharedCheck_323_ == 0)
{
v___x_312_ = v_o_306_;
v_isShared_313_ = v_isSharedCheck_323_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_map_309_);
lean_dec(v_o_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_323_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; 
lean_inc(v_k_307_);
v___x_314_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_307_, v_v_308_, v_map_309_);
if (v_hasTrace_310_ == 0)
{
lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_318_; 
v___x_315_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_316_ = l_Lean_Name_isPrefixOf(v___x_315_, v_k_307_);
lean_dec(v_k_307_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_314_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v___x_316_);
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v_k_307_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_321_ = v___x_312_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_322_, sizeof(void*)*1, v_hasTrace_310_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object* v_a_330_, lean_object* v_init_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_d_335_; 
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v_k_338_; lean_object* v_v_339_; lean_object* v_l_340_; lean_object* v_r_341_; lean_object* v___x_342_; 
v_k_338_ = lean_ctor_get(v_x_332_, 1);
lean_inc(v_k_338_);
v_v_339_ = lean_ctor_get(v_x_332_, 2);
lean_inc(v_v_339_);
v_l_340_ = lean_ctor_get(v_x_332_, 3);
lean_inc(v_l_340_);
v_r_341_ = lean_ctor_get(v_x_332_, 4);
lean_inc(v_r_341_);
lean_dec_ref_known(v_x_332_, 5);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_330_, v_init_331_, v_l_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
if (lean_obj_tag(v_a_343_) == 0)
{
lean_object* v_a_344_; 
lean_dec_ref_known(v___x_342_, 1);
lean_dec(v_r_341_);
lean_dec(v_v_339_);
lean_dec(v_k_338_);
v_a_344_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v_a_343_, 1);
v_d_335_ = v_a_344_;
goto v___jp_334_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_396_; 
v_a_345_ = lean_ctor_get(v_a_343_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_343_);
if (v_isSharedCheck_396_ == 0)
{
v___x_347_ = v_a_343_;
v_isShared_348_ = v_isSharedCheck_396_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v_a_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_396_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_349_ = l_Lean_Name_getRoot(v_k_338_);
v___x_350_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1));
v___x_351_ = lean_box(0);
v___x_352_ = l_Lean_Name_replacePrefix(v_k_338_, v___x_350_, v___x_351_);
v___x_353_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_330_, v___x_352_);
if (lean_obj_tag(v___x_353_) == 1)
{
lean_dec(v___x_349_);
lean_del_object(v___x_347_);
lean_dec_ref_known(v___x_342_, 1);
if (lean_obj_tag(v_v_339_) == 0)
{
lean_object* v_val_354_; lean_object* v_v_355_; lean_object* v___x_356_; 
v_val_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v___x_353_, 1);
v_v_355_ = lean_ctor_get(v_v_339_, 0);
lean_inc_ref(v_v_355_);
lean_dec_ref_known(v_v_339_, 1);
v___x_356_ = l_Lean_Language_Lean_setOption(v_a_345_, v_val_354_, v___x_352_, v_v_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v_init_331_ = v_a_357_;
v_x_332_ = v_r_341_;
goto _start;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_r_341_);
v_a_359_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_356_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_356_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v___x_367_; 
lean_dec_ref_known(v___x_353_, 1);
v___x_367_ = l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(v_a_345_, v___x_352_, v_v_339_);
v_init_331_ = v___x_367_;
v_x_332_ = v_r_341_;
goto _start;
}
}
else
{
uint8_t v___x_369_; 
lean_dec(v___x_353_);
lean_dec(v_a_345_);
lean_dec(v_v_339_);
v___x_369_ = lean_name_eq(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
if (v___x_369_ == 0)
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_r_341_);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_342_, 0);
lean_dec(v_unused_391_);
v___x_371_ = v___x_342_;
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_342_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_373_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2));
v___x_374_ = 1;
lean_inc(v___x_352_);
v___x_375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_352_, v___x_374_);
v___x_376_ = lean_string_append(v___x_373_, v___x_375_);
lean_dec_ref(v___x_375_);
v___x_377_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3));
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
v___x_379_ = l_Lean_Name_append(v___x_350_, v___x_352_);
v___x_380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_379_, v___x_374_);
v___x_381_ = lean_string_append(v___x_378_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 18);
lean_ctor_set(v___x_347_, 0, v___x_383_);
v___x_385_ = v___x_347_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_389_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 1);
lean_ctor_set(v___x_371_, 0, v___x_385_);
v___x_387_ = v___x_371_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_dec(v___x_352_);
lean_del_object(v___x_347_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_392_; 
v_a_392_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_342_, 1);
if (lean_obj_tag(v_a_392_) == 0)
{
lean_object* v_a_393_; 
lean_dec(v_r_341_);
v_a_393_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v_a_392_, 1);
v_d_335_ = v_a_393_;
goto v___jp_334_;
}
else
{
lean_object* v_a_394_; 
v_a_394_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v_a_392_, 1);
v_init_331_ = v_a_394_;
v_x_332_ = v_r_341_;
goto _start;
}
}
else
{
lean_dec(v_r_341_);
return v___x_342_;
}
}
}
}
}
}
else
{
lean_dec(v_r_341_);
lean_dec(v_v_339_);
lean_dec(v_k_338_);
return v___x_342_;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_init_331_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_d_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_330_ = stack[0].m_obj;
lean_object* v_init_331_ = stack[1].m_obj;
lean_object* v_x_332_ = stack[2].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_330_, v_init_331_, v_x_332_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object* v_a_400_, lean_object* v_init_401_, lean_object* v_x_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_400_, v_init_401_, v_x_402_);
lean_dec(v_a_400_);
return v_res_404_;
}
}
lean_object* l_Lean_Language_Lean_reparseOptions(lean_object* v_opts_405_){
_start:
{
lean_object* v_opts_x27_407_; lean_object* v___x_408_; 
v_opts_x27_407_ = l_Lean_Options_empty;
v___x_408_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v_map_410_; lean_object* v___x_411_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_map_410_ = lean_ctor_get(v_opts_405_, 0);
lean_inc(v_map_410_);
lean_dec_ref(v_opts_405_);
v___x_411_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_409_, v_opts_x27_407_, v_map_410_);
lean_dec(v_a_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_a_416_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_a_416_);
lean_dec(v_a_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_a_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_411_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_411_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_opts_405_);
v_a_429_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_408_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_408_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_reparseOptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_405_ = stack[0].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_Language_Lean_reparseOptions(v_opts_405_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object* v_opts_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Language_Lean_reparseOptions(v_opts_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object* v_stx_449_){
_start:
{
lean_object* v_stx_451_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3));
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
v_stx_451_ = v_stx_449_;
goto v___jp_450_;
}
else
{
lean_object* v___x_458_; lean_object* v_stx_459_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v_stx_459_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_458_);
lean_dec(v_stx_449_);
v_stx_451_ = v_stx_459_;
goto v___jp_450_;
}
v___jp_450_:
{
uint8_t v___x_452_; lean_object* v___x_453_; 
v___x_452_ = 0;
v___x_453_ = l_Lean_Syntax_getPos_x3f(v_stx_451_, v___x_452_);
lean_dec(v_stx_451_);
return v___x_453_;
}
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_460_, lean_object* v_decl_461_, lean_object* v_ref_462_){
_start:
{
lean_object* v_defValue_464_; lean_object* v_descr_465_; lean_object* v_deprecation_x3f_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_defValue_464_ = lean_ctor_get(v_decl_461_, 0);
v_descr_465_ = lean_ctor_get(v_decl_461_, 1);
v_deprecation_x3f_466_ = lean_ctor_get(v_decl_461_, 2);
v___x_467_ = lean_alloc_ctor(1, 0, 1);
v___x_468_ = lean_unbox(v_defValue_464_);
lean_ctor_set_uint8(v___x_467_, 0, v___x_468_);
lean_inc(v_deprecation_x3f_466_);
lean_inc_ref(v_descr_465_);
lean_inc_n(v_name_460_, 2);
v___x_469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_469_, 0, v_name_460_);
lean_ctor_set(v___x_469_, 1, v_ref_462_);
lean_ctor_set(v___x_469_, 2, v___x_467_);
lean_ctor_set(v___x_469_, 3, v_descr_465_);
lean_ctor_set(v___x_469_, 4, v_deprecation_x3f_466_);
v___x_470_ = lean_register_option(v_name_460_, v___x_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___x_470_, 0);
lean_dec(v_unused_479_);
v___x_472_ = v___x_470_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_dec(v___x_470_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
lean_inc(v_defValue_464_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_name_460_);
lean_ctor_set(v___x_474_, 1, v_defValue_464_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_name_460_);
v_a_480_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_470_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_470_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_460_ = stack[0].m_obj;
lean_object* v_decl_461_ = stack[1].m_obj;
lean_object* v_ref_462_ = stack[2].m_obj;
lean_object* v_res_488_;
v_res_488_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_460_, v_decl_461_, v_ref_462_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_489_, lean_object* v_decl_490_, lean_object* v_ref_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_489_, v_decl_490_, v_ref_491_);
lean_dec_ref(v_decl_490_);
return v_res_493_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_512_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_513_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_514_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_511_, v___x_512_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_515_;
v_res_515_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_517_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_unsigned_to_nat(32u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_521_ = ((size_t)5ULL);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_unsigned_to_nat(32u);
v___x_524_ = lean_mk_empty_array_with_capacity(v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_526_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
lean_ctor_set(v___x_526_, 2, v___x_522_);
lean_ctor_set(v___x_526_, 3, v___x_522_);
lean_ctor_set_usize(v___x_526_, 4, v___x_521_);
return v___x_526_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_infoState_530_; lean_object* v_trees_531_; lean_object* v___x_532_; lean_object* v_infoState_533_; lean_object* v_env_534_; lean_object* v_messages_535_; lean_object* v_scopes_536_; lean_object* v_usedQuotCtxts_537_; lean_object* v_nextMacroScope_538_; lean_object* v_maxRecDepth_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_traceState_542_; lean_object* v_snapshotTasks_543_; lean_object* v_prevLinterStates_544_; lean_object* v_codeQualityEntryTasks_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_566_; 
v___x_529_ = lean_st_ref_get(v___y_527_);
v_infoState_530_ = lean_ctor_get(v___x_529_, 8);
lean_inc_ref(v_infoState_530_);
lean_dec(v___x_529_);
v_trees_531_ = lean_ctor_get(v_infoState_530_, 2);
lean_inc_ref(v_trees_531_);
lean_dec_ref(v_infoState_530_);
v___x_532_ = lean_st_ref_take(v___y_527_);
v_infoState_533_ = lean_ctor_get(v___x_532_, 8);
v_env_534_ = lean_ctor_get(v___x_532_, 0);
v_messages_535_ = lean_ctor_get(v___x_532_, 1);
v_scopes_536_ = lean_ctor_get(v___x_532_, 2);
v_usedQuotCtxts_537_ = lean_ctor_get(v___x_532_, 3);
v_nextMacroScope_538_ = lean_ctor_get(v___x_532_, 4);
v_maxRecDepth_539_ = lean_ctor_get(v___x_532_, 5);
v_ngen_540_ = lean_ctor_get(v___x_532_, 6);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_532_, 7);
v_traceState_542_ = lean_ctor_get(v___x_532_, 9);
v_snapshotTasks_543_ = lean_ctor_get(v___x_532_, 10);
v_prevLinterStates_544_ = lean_ctor_get(v___x_532_, 11);
v_codeQualityEntryTasks_545_ = lean_ctor_get(v___x_532_, 12);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_566_ == 0)
{
v___x_547_ = v___x_532_;
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_codeQualityEntryTasks_545_);
lean_inc(v_prevLinterStates_544_);
lean_inc(v_snapshotTasks_543_);
lean_inc(v_traceState_542_);
lean_inc(v_infoState_533_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_maxRecDepth_539_);
lean_inc(v_nextMacroScope_538_);
lean_inc(v_usedQuotCtxts_537_);
lean_inc(v_scopes_536_);
lean_inc(v_messages_535_);
lean_inc(v_env_534_);
lean_dec(v___x_532_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v_enabled_549_; lean_object* v_assignment_550_; lean_object* v_lazyAssignment_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_564_; 
v_enabled_549_ = lean_ctor_get_uint8(v_infoState_533_, sizeof(void*)*3);
v_assignment_550_ = lean_ctor_get(v_infoState_533_, 0);
v_lazyAssignment_551_ = lean_ctor_get(v_infoState_533_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_infoState_533_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_infoState_533_, 2);
lean_dec(v_unused_565_);
v___x_553_ = v_infoState_533_;
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_lazyAssignment_551_);
lean_inc(v_assignment_550_);
lean_dec(v_infoState_533_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_564_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_assignment_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_lazyAssignment_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v___x_555_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*3, v_enabled_549_);
v___x_557_ = v_reuseFailAlloc_563_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 8, v___x_557_);
v___x_559_ = v___x_547_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_env_534_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_messages_535_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_scopes_536_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_usedQuotCtxts_537_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_nextMacroScope_538_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_maxRecDepth_539_);
lean_ctor_set(v_reuseFailAlloc_562_, 6, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 7, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_562_, 8, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_562_, 9, v_traceState_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 10, v_snapshotTasks_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 11, v_prevLinterStates_544_);
lean_ctor_set(v_reuseFailAlloc_562_, 12, v_codeQualityEntryTasks_545_);
v___x_559_ = v_reuseFailAlloc_562_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_st_ref_put(v___y_527_, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_trees_531_);
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_527_ = stack[0].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_527_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_568_);
lean_dec(v___y_568_);
return v_res_570_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_572_);
return v___x_574_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_571_ = stack[0].m_obj;
lean_object* v___y_572_ = stack[1].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_571_, v___y_572_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_579_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_580_, lean_object* v_opt_581_){
_start:
{
lean_object* v_name_582_; lean_object* v_defValue_583_; lean_object* v_map_584_; lean_object* v___x_585_; 
v_name_582_ = lean_ctor_get(v_opt_581_, 0);
v_defValue_583_ = lean_ctor_get(v_opt_581_, 1);
v_map_584_ = lean_ctor_get(v_opts_580_, 0);
v___x_585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_584_, v_name_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
uint8_t v___x_586_; 
v___x_586_ = lean_unbox(v_defValue_583_);
return v___x_586_;
}
else
{
lean_object* v_val_587_; 
v_val_587_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_585_, 1);
if (lean_obj_tag(v_val_587_) == 1)
{
uint8_t v_v_588_; 
v_v_588_ = lean_ctor_get_uint8(v_val_587_, 0);
lean_dec_ref_known(v_val_587_, 0);
return v_v_588_;
}
else
{
uint8_t v___x_589_; 
lean_dec(v_val_587_);
v___x_589_ = lean_unbox(v_defValue_583_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_580_ = stack[0].m_obj;
lean_object* v_opt_581_ = stack[1].m_obj;
uint8_t v_res_590_;
v_res_590_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_580_, v_opt_581_);
stack->m_num = v_res_590_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_591_, lean_object* v_opt_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_591_, v_opt_592_);
lean_dec_ref(v_opt_592_);
lean_dec_ref(v_opts_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = l_Lean_Language_Snapshot_transform(v_val_597_, v___y_598_);
v___x_600_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_602_, v___y_603_);
lean_dec_ref(v___y_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_605_, lean_object* v_val_606_){
_start:
{
lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_inc_ref(v_val_606_);
v___f_607_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_607_, 0, v_val_606_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v_inst_605_);
lean_ctor_set(v___x_608_, 1, v_val_606_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___f_607_);
return v___x_609_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_610_, lean_object* v_revCmds_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_613_);
lean_dec_ref(v___x_615_);
lean_inc(v_stx_610_);
v___x_616_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_610_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_616_, 0);
lean_dec(v_unused_629_);
v___x_618_ = v___x_616_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_dec(v___x_616_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_Parser_isTerminalCommand(v_stx_610_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec(v_revCmds_611_);
v___x_621_ = lean_box(0);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_621_);
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_del_object(v___x_618_);
v___x_625_ = l_List_reverse___redArg(v_revCmds_611_);
v___x_626_ = lean_array_mk(v___x_625_);
v___x_627_ = l_Lean_Elab_Command_runModuleLintersAsync(v___x_626_, v___y_612_, v___y_613_);
return v___x_627_;
}
}
}
else
{
lean_dec(v_revCmds_611_);
lean_dec(v_stx_610_);
return v___x_616_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_610_ = stack[0].m_obj;
lean_object* v_revCmds_611_ = stack[1].m_obj;
lean_object* v___y_612_ = stack[2].m_obj;
lean_object* v___y_613_ = stack[3].m_obj;
lean_object* v_res_630_;
v_res_630_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_610_, v_revCmds_611_, v___y_612_, v___y_613_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_631_, lean_object* v_revCmds_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_631_, v_revCmds_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_636_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_637_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_641_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
lean_ctor_set(v___x_643_, 3, v___x_642_);
lean_ctor_set(v___x_643_, 4, v___x_641_);
lean_ctor_set(v___x_643_, 5, v___x_641_);
lean_ctor_set(v___x_643_, 6, v___x_641_);
lean_ctor_set(v___x_643_, 7, v___x_641_);
lean_ctor_set(v___x_643_, 8, v___x_641_);
lean_ctor_set(v___x_643_, 9, v___x_641_);
lean_ctor_set(v___x_643_, 10, v___x_641_);
lean_ctor_set(v___x_643_, 11, v___x_640_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(32u);
v___x_645_ = lean_mk_empty_array_with_capacity(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((size_t)5ULL);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_unsigned_to_nat(32u);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_652_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
lean_ctor_set(v___x_652_, 2, v___x_648_);
lean_ctor_set(v___x_652_, 3, v___x_648_);
lean_ctor_set_usize(v___x_652_, 4, v___x_647_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_box(1);
v___x_654_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_655_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
lean_ctor_set(v___x_656_, 2, v___x_653_);
return v___x_656_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_env_661_; uint8_t v___x_662_; lean_object* v_env_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_scopes_666_; lean_object* v___x_667_; lean_object* v_opts_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_660_ = lean_st_ref_get(v___y_658_);
v_env_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_env_661_);
lean_dec(v___x_660_);
v___x_662_ = 0;
v_env_663_ = l_Lean_Environment_setRecordingDeps(v_env_661_, v___x_662_);
v___x_664_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_665_ = lean_st_ref_get(v___y_658_);
v_scopes_666_ = lean_ctor_get(v___x_665_, 2);
lean_inc(v_scopes_666_);
lean_dec(v___x_665_);
v___x_667_ = l_List_head_x21___redArg(v___x_664_, v_scopes_666_);
lean_dec(v_scopes_666_);
v_opts_668_ = lean_ctor_get(v___x_667_, 1);
lean_inc_ref(v_opts_668_);
lean_dec(v___x_667_);
v___x_669_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_670_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_671_, 0, v_env_663_);
lean_ctor_set(v___x_671_, 1, v___x_669_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
lean_ctor_set(v___x_671_, 3, v_opts_668_);
v___x_672_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_msgData_657_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_657_ = stack[0].m_obj;
lean_object* v___y_658_ = stack[1].m_obj;
lean_object* v_res_674_;
v_res_674_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_657_, v___y_658_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_675_, v___y_676_);
lean_dec(v___y_676_);
return v_res_678_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_679_, uint8_t v___y_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_681_) == 1)
{
lean_object* v_pre_682_; 
v_pre_682_ = lean_ctor_get(v_x_681_, 0);
if (lean_obj_tag(v_pre_682_) == 0)
{
lean_object* v_str_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_str_683_ = lean_ctor_get(v_x_681_, 1);
v___x_684_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_685_ = lean_string_dec_eq(v_str_683_, v___x_684_);
if (v___x_685_ == 0)
{
return v___x_685_;
}
else
{
return v_suppressElabErrors_679_;
}
}
else
{
return v___y_680_;
}
}
else
{
return v___y_680_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_679_ = stack[0].m_num;
uint8_t v___y_680_ = stack[1].m_num;
lean_object* v_x_681_ = stack[2].m_obj;
uint8_t v_res_686_;
v_res_686_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_679_, v___y_680_, v_x_681_);
stack->m_num = v_res_686_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_687_, lean_object* v___y_688_, lean_object* v_x_689_){
_start:
{
uint8_t v_suppressElabErrors_boxed_690_; uint8_t v___y_9489__boxed_691_; uint8_t v_res_692_; lean_object* v_r_693_; 
v_suppressElabErrors_boxed_690_ = lean_unbox(v_suppressElabErrors_687_);
v___y_9489__boxed_691_ = lean_unbox(v___y_688_);
v_res_692_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_690_, v___y_9489__boxed_691_, v_x_689_);
lean_dec(v_x_689_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_695_, lean_object* v_msgData_696_, uint8_t v_severity_697_, uint8_t v_isSilent_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; lean_object* v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; uint8_t v___y_768_; uint8_t v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; lean_object* v___y_772_; uint8_t v___y_796_; uint8_t v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; uint8_t v___y_804_; uint8_t v___y_805_; uint8_t v___y_806_; uint8_t v___x_821_; uint8_t v___y_823_; uint8_t v___y_824_; uint8_t v___y_825_; uint8_t v___y_827_; uint8_t v___x_839_; 
v___x_821_ = 2;
v___x_839_ = l_Lean_instBEqMessageSeverity_beq(v_severity_697_, v___x_821_);
if (v___x_839_ == 0)
{
v___y_827_ = v___x_839_;
goto v___jp_826_;
}
else
{
uint8_t v___x_840_; 
lean_inc_ref(v_msgData_696_);
v___x_840_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_696_);
v___y_827_ = v___x_840_;
goto v___jp_826_;
}
v___jp_702_:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Elab_Command_getScope___redArg(v___y_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v_currNamespace_713_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v_currNamespace_713_ = lean_ctor_get(v_a_712_, 2);
lean_inc(v_currNamespace_713_);
lean_dec(v_a_712_);
v___x_714_ = l_Lean_Elab_Command_getScope___redArg(v___y_710_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_750_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_750_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_openDecls_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_env_724_; lean_object* v_messages_725_; lean_object* v_scopes_726_; lean_object* v_usedQuotCtxts_727_; lean_object* v_nextMacroScope_728_; lean_object* v_maxRecDepth_729_; lean_object* v_ngen_730_; lean_object* v_auxDeclNGen_731_; lean_object* v_infoState_732_; lean_object* v_traceState_733_; lean_object* v_snapshotTasks_734_; lean_object* v_prevLinterStates_735_; lean_object* v_codeQualityEntryTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_749_; 
v_openDecls_719_ = lean_ctor_get(v_a_715_, 3);
lean_inc(v_openDecls_719_);
lean_dec(v_a_715_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_currNamespace_713_);
lean_ctor_set(v___x_720_, 1, v_openDecls_719_);
v___x_721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___y_703_);
lean_inc_ref(v___y_704_);
lean_inc_ref(v___y_708_);
v___x_722_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_722_, 0, v___y_708_);
lean_ctor_set(v___x_722_, 1, v___y_706_);
lean_ctor_set(v___x_722_, 2, v___y_709_);
lean_ctor_set(v___x_722_, 3, v___y_704_);
lean_ctor_set(v___x_722_, 4, v___x_721_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*5, v___y_707_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*5 + 1, v___y_705_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*5 + 2, v_isSilent_698_);
v___x_723_ = lean_st_ref_take(v___y_710_);
v_env_724_ = lean_ctor_get(v___x_723_, 0);
v_messages_725_ = lean_ctor_get(v___x_723_, 1);
v_scopes_726_ = lean_ctor_get(v___x_723_, 2);
v_usedQuotCtxts_727_ = lean_ctor_get(v___x_723_, 3);
v_nextMacroScope_728_ = lean_ctor_get(v___x_723_, 4);
v_maxRecDepth_729_ = lean_ctor_get(v___x_723_, 5);
v_ngen_730_ = lean_ctor_get(v___x_723_, 6);
v_auxDeclNGen_731_ = lean_ctor_get(v___x_723_, 7);
v_infoState_732_ = lean_ctor_get(v___x_723_, 8);
v_traceState_733_ = lean_ctor_get(v___x_723_, 9);
v_snapshotTasks_734_ = lean_ctor_get(v___x_723_, 10);
v_prevLinterStates_735_ = lean_ctor_get(v___x_723_, 11);
v_codeQualityEntryTasks_736_ = lean_ctor_get(v___x_723_, 12);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_749_ == 0)
{
v___x_738_ = v___x_723_;
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_codeQualityEntryTasks_736_);
lean_inc(v_prevLinterStates_735_);
lean_inc(v_snapshotTasks_734_);
lean_inc(v_traceState_733_);
lean_inc(v_infoState_732_);
lean_inc(v_auxDeclNGen_731_);
lean_inc(v_ngen_730_);
lean_inc(v_maxRecDepth_729_);
lean_inc(v_nextMacroScope_728_);
lean_inc(v_usedQuotCtxts_727_);
lean_inc(v_scopes_726_);
lean_inc(v_messages_725_);
lean_inc(v_env_724_);
lean_dec(v___x_723_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_Lean_MessageLog_add(v___x_722_, v_messages_725_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_env_724_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_scopes_726_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_usedQuotCtxts_727_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_nextMacroScope_728_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v_maxRecDepth_729_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_ngen_730_);
lean_ctor_set(v_reuseFailAlloc_748_, 7, v_auxDeclNGen_731_);
lean_ctor_set(v_reuseFailAlloc_748_, 8, v_infoState_732_);
lean_ctor_set(v_reuseFailAlloc_748_, 9, v_traceState_733_);
lean_ctor_set(v_reuseFailAlloc_748_, 10, v_snapshotTasks_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 11, v_prevLinterStates_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 12, v_codeQualityEntryTasks_736_);
v___x_743_ = v_reuseFailAlloc_748_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_st_ref_put(v___y_710_, v___x_743_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_740_);
v___x_746_ = v___x_717_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_740_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_currNamespace_713_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_703_);
v_a_751_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_714_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_714_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v___y_709_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v___y_703_);
v_a_759_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_711_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_711_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
v___jp_767_:
{
lean_object* v_fileName_773_; lean_object* v_fileMap_774_; uint8_t v_suppressElabErrors_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_794_; 
v_fileName_773_ = lean_ctor_get(v___y_699_, 0);
v_fileMap_774_ = lean_ctor_get(v___y_699_, 1);
v_suppressElabErrors_775_ = lean_ctor_get_uint8(v___y_699_, sizeof(void*)*10);
v___x_776_ = lean_box(v_suppressElabErrors_775_);
v___x_777_ = lean_box(v___y_768_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_778_, 0, v___x_776_);
lean_closure_set(v___f_778_, 1, v___x_777_);
v___x_779_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_696_);
v___x_780_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_779_, v___y_700_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_794_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_794_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_794_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc_ref_n(v_fileMap_774_, 2);
v___x_785_ = l_Lean_FileMap_toPosition(v_fileMap_774_, v___y_770_);
lean_dec(v___y_770_);
v___x_786_ = l_Lean_FileMap_toPosition(v_fileMap_774_, v___y_772_);
lean_dec(v___y_772_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___x_788_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_775_ == 0)
{
lean_del_object(v___x_783_);
lean_dec_ref(v___f_778_);
v___y_703_ = v_a_781_;
v___y_704_ = v___x_788_;
v___y_705_ = v___y_769_;
v___y_706_ = v___x_785_;
v___y_707_ = v___y_771_;
v___y_708_ = v_fileName_773_;
v___y_709_ = v___x_787_;
v___y_710_ = v___y_700_;
goto v___jp_702_;
}
else
{
uint8_t v___x_789_; 
lean_inc(v_a_781_);
v___x_789_ = l_Lean_MessageData_hasTag(v___f_778_, v_a_781_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec_ref_known(v___x_787_, 1);
lean_dec_ref(v___x_785_);
lean_dec(v_a_781_);
v___x_790_ = lean_box(0);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_790_);
v___x_792_ = v___x_783_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_del_object(v___x_783_);
v___y_703_ = v_a_781_;
v___y_704_ = v___x_788_;
v___y_705_ = v___y_769_;
v___y_706_ = v___x_785_;
v___y_707_ = v___y_771_;
v___y_708_ = v_fileName_773_;
v___y_709_ = v___x_787_;
v___y_710_ = v___y_700_;
goto v___jp_702_;
}
}
}
}
v___jp_795_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Syntax_getTailPos_x3f(v___y_798_, v___y_799_);
lean_dec(v___y_798_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_inc(v___y_800_);
v___y_768_ = v___y_796_;
v___y_769_ = v___y_797_;
v___y_770_ = v___y_800_;
v___y_771_ = v___y_799_;
v___y_772_ = v___y_800_;
goto v___jp_767_;
}
else
{
lean_object* v_val_802_; 
v_val_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v___x_801_, 1);
v___y_768_ = v___y_796_;
v___y_769_ = v___y_797_;
v___y_770_ = v___y_800_;
v___y_771_ = v___y_799_;
v___y_772_ = v_val_802_;
goto v___jp_767_;
}
}
v___jp_803_:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Elab_Command_getRef___redArg(v___y_699_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v_ref_809_; lean_object* v___x_810_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_ref_809_ = l_Lean_replaceRef(v_ref_695_, v_a_808_);
lean_dec(v_a_808_);
v___x_810_ = l_Lean_Syntax_getPos_x3f(v_ref_809_, v___y_805_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_unsigned_to_nat(0u);
v___y_796_ = v___y_804_;
v___y_797_ = v___y_806_;
v___y_798_ = v_ref_809_;
v___y_799_ = v___y_805_;
v___y_800_ = v___x_811_;
goto v___jp_795_;
}
else
{
lean_object* v_val_812_; 
v_val_812_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___x_810_, 1);
v___y_796_ = v___y_804_;
v___y_797_ = v___y_806_;
v___y_798_ = v_ref_809_;
v___y_799_ = v___y_805_;
v___y_800_ = v_val_812_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_msgData_696_);
v_a_813_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_807_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_807_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
v___jp_822_:
{
if (v___y_825_ == 0)
{
v___y_804_ = v___y_823_;
v___y_805_ = v___y_824_;
v___y_806_ = v_severity_697_;
goto v___jp_803_;
}
else
{
v___y_804_ = v___y_823_;
v___y_805_ = v___y_824_;
v___y_806_ = v___x_821_;
goto v___jp_803_;
}
}
v___jp_826_:
{
if (v___y_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_scopes_830_; lean_object* v___x_831_; lean_object* v_opts_832_; uint8_t v___x_833_; uint8_t v___x_834_; 
v___x_828_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_829_ = lean_st_ref_get(v___y_700_);
v_scopes_830_ = lean_ctor_get(v___x_829_, 2);
lean_inc(v_scopes_830_);
lean_dec(v___x_829_);
v___x_831_ = l_List_head_x21___redArg(v___x_828_, v_scopes_830_);
lean_dec(v_scopes_830_);
v_opts_832_ = lean_ctor_get(v___x_831_, 1);
lean_inc_ref(v_opts_832_);
lean_dec(v___x_831_);
v___x_833_ = 1;
v___x_834_ = l_Lean_instBEqMessageSeverity_beq(v_severity_697_, v___x_833_);
if (v___x_834_ == 0)
{
lean_dec_ref(v_opts_832_);
v___y_823_ = v___y_827_;
v___y_824_ = v___y_827_;
v___y_825_ = v___x_834_;
goto v___jp_822_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = l_Lean_warningAsError;
v___x_836_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_832_, v___x_835_);
lean_dec_ref(v_opts_832_);
v___y_823_ = v___y_827_;
v___y_824_ = v___y_827_;
v___y_825_ = v___x_836_;
goto v___jp_822_;
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_msgData_696_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_695_ = stack[0].m_obj;
lean_object* v_msgData_696_ = stack[1].m_obj;
uint8_t v_severity_697_ = stack[2].m_num;
uint8_t v_isSilent_698_ = stack[3].m_num;
lean_object* v___y_699_ = stack[4].m_obj;
lean_object* v___y_700_ = stack[5].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_695_, v_msgData_696_, v_severity_697_, v_isSilent_698_, v___y_699_, v___y_700_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_842_, lean_object* v_msgData_843_, lean_object* v_severity_844_, lean_object* v_isSilent_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v_severity_boxed_849_; uint8_t v_isSilent_boxed_850_; lean_object* v_res_851_; 
v_severity_boxed_849_ = lean_unbox(v_severity_844_);
v_isSilent_boxed_850_ = lean_unbox(v_isSilent_845_);
v_res_851_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_842_, v_msgData_843_, v_severity_boxed_849_, v_isSilent_boxed_850_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v_ref_842_);
return v_res_851_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_852_, uint8_t v_severity_853_, uint8_t v_isSilent_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Elab_Command_getRef___redArg(v___y_855_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_859_, v_msgData_852_, v_severity_853_, v_isSilent_854_, v___y_855_, v___y_856_);
lean_dec(v_a_859_);
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v_msgData_852_);
v_a_861_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_858_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_852_ = stack[0].m_obj;
uint8_t v_severity_853_ = stack[1].m_num;
uint8_t v_isSilent_854_ = stack[2].m_num;
lean_object* v___y_855_ = stack[3].m_obj;
lean_object* v___y_856_ = stack[4].m_obj;
lean_object* v_res_869_;
v_res_869_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_852_, v_severity_853_, v_isSilent_854_, v___y_855_, v___y_856_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_870_, lean_object* v_severity_871_, lean_object* v_isSilent_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v_severity_boxed_876_; uint8_t v_isSilent_boxed_877_; lean_object* v_res_878_; 
v_severity_boxed_876_ = lean_unbox(v_severity_871_);
v_isSilent_boxed_877_ = lean_unbox(v_isSilent_872_);
v_res_878_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_870_, v_severity_boxed_876_, v_isSilent_boxed_877_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_878_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = 2;
v___x_884_ = 0;
v___x_885_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_879_, v___x_883_, v___x_884_, v___y_880_, v___y_881_);
return v___x_885_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_879_ = stack[0].m_obj;
lean_object* v___y_880_ = stack[1].m_obj;
lean_object* v___y_881_ = stack[2].m_obj;
lean_object* v_res_886_;
v_res_886_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_879_, v___y_880_, v___y_881_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_891_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_892_, lean_object* v_msgData_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = 2;
v___x_898_ = 0;
v___x_899_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_892_, v_msgData_893_, v___x_897_, v___x_898_, v___y_894_, v___y_895_);
return v___x_899_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_892_ = stack[0].m_obj;
lean_object* v_msgData_893_ = stack[1].m_obj;
lean_object* v___y_894_ = stack[2].m_obj;
lean_object* v___y_895_ = stack[3].m_obj;
lean_object* v_res_900_;
v_res_900_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_892_, v_msgData_893_, v___y_894_, v___y_895_);
stack->m_obj
 = v_res_900_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_901_, lean_object* v_msgData_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_901_, v_msgData_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v_ref_901_);
return v_res_906_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
if (lean_obj_tag(v_ex_910_) == 0)
{
lean_object* v_ref_914_; lean_object* v_msg_915_; lean_object* v___x_916_; 
v_ref_914_ = lean_ctor_get(v_ex_910_, 0);
lean_inc(v_ref_914_);
v_msg_915_ = lean_ctor_get(v_ex_910_, 1);
lean_inc_ref(v_msg_915_);
lean_dec_ref_known(v_ex_910_, 2);
v___x_916_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_914_, v_msg_915_, v___y_911_, v___y_912_);
lean_dec(v_ref_914_);
return v___x_916_;
}
else
{
lean_object* v_id_917_; uint8_t v___y_919_; uint8_t v___x_941_; 
v_id_917_ = lean_ctor_get(v_ex_910_, 0);
lean_inc(v_id_917_);
v___x_941_ = l_Lean_Elab_isAbortExceptionId(v_id_917_);
if (v___x_941_ == 0)
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_Exception_isInterrupt(v_ex_910_);
lean_dec_ref_known(v_ex_910_, 2);
v___y_919_ = v___x_942_;
goto v___jp_918_;
}
else
{
lean_dec_ref_known(v_ex_910_, 2);
v___y_919_ = v___x_941_;
goto v___jp_918_;
}
v___jp_918_:
{
if (v___y_919_ == 0)
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_InternalExceptionId_getName(v_id_917_);
lean_dec(v_id_917_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_923_ = l_Lean_MessageData_ofName(v_a_921_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_924_, v___y_911_, v___y_912_);
return v___x_925_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_938_; 
v_a_926_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_938_ == 0)
{
v___x_928_ = v___x_920_;
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_920_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_938_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_ref_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v_ref_930_ = lean_ctor_get(v___y_911_, 7);
v___x_931_ = lean_io_error_to_string(v_a_926_);
v___x_932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
v___x_933_ = l_Lean_MessageData_ofFormat(v___x_932_);
lean_inc(v_ref_930_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_ref_930_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_934_);
v___x_936_ = v___x_928_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_id_917_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_910_ = stack[0].m_obj;
lean_object* v___y_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_910_, v___y_911_, v___y_912_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_948_;
}
}
lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
lean_inc(v___y_951_);
lean_inc_ref(v___y_950_);
v___x_953_ = lean_apply_3(v_x_949_, v___y_950_, v___y_951_, lean_box(0));
if (lean_obj_tag(v___x_953_) == 0)
{
return v___x_953_;
}
else
{
lean_object* v_a_954_; uint8_t v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
v___x_955_ = l_Lean_Exception_isInterrupt(v_a_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref_known(v___x_953_, 1);
v___x_956_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_954_, v___y_950_, v___y_951_);
return v___x_956_;
}
else
{
lean_dec(v_a_954_);
return v___x_953_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_949_ = stack[0].m_obj;
lean_object* v___y_950_ = stack[1].m_obj;
lean_object* v___y_951_ = stack[2].m_obj;
lean_object* v_res_957_;
v_res_957_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_949_, v___y_950_, v___y_951_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_962_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_963_, lean_object* v___x_964_, lean_object* v_val_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_a_969_; lean_object* v___x_971_; 
v___x_971_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_963_, v___x_964_, v_val_965_);
if (lean_obj_tag(v___x_971_) == 0)
{
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v_a_969_ = v_a_972_;
goto v___jp_968_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_971_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_971_);
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
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
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
lean_dec_ref_known(v___x_971_, 1);
v___x_981_ = lean_box(0);
v_a_969_ = v___x_981_;
goto v___jp_968_;
}
v___jp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_a_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_963_ = stack[0].m_obj;
lean_object* v___x_964_ = stack[1].m_obj;
lean_object* v_val_965_ = stack[2].m_obj;
lean_object* v___y_966_ = stack[3].m_obj;
lean_object* v_res_982_;
v_res_982_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_963_, v___x_964_, v_val_965_, v___y_966_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_983_, lean_object* v___x_984_, lean_object* v_val_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_983_, v___x_984_, v_val_985_, v___y_986_);
lean_dec_ref(v___y_986_);
lean_dec(v_val_985_);
lean_dec_ref(v___x_984_);
return v_res_988_;
}
}
lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_989_, lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_get_set_stderr(v_h_989_);
lean_inc_ref(v___y_991_);
v___x_994_ = lean_apply_2(v_x_990_, v___y_991_, lean_box(0));
v___x_995_ = lean_get_set_stderr(v___x_993_);
lean_dec_ref(v___x_995_);
return v___x_994_;
}
}
LEAN_EXPORT void l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_989_ = stack[0].m_obj;
lean_object* v_x_990_ = stack[1].m_obj;
lean_object* v___y_991_ = stack[2].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_989_, v_x_990_, v___y_991_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_997_, v_x_998_, v___y_999_);
lean_dec_ref(v___y_999_);
return v_res_1001_;
}
}
lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_1002_, lean_object* v_h_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_1003_, v_x_1004_, v___y_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT void l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1003_ = stack[1].m_obj;
lean_object* v_x_1004_ = stack[2].m_obj;
lean_object* v___y_1005_ = stack[3].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_box(0), v_h_1003_, v_x_1004_, v___y_1005_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_h_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_1009_, v_h_1010_, v_x_1011_, v___y_1012_);
lean_dec_ref(v___y_1012_);
return v_res_1014_;
}
}
lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_1015_, lean_object* v_x_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_get_set_stdin(v_h_1015_);
lean_inc_ref(v___y_1017_);
v___x_1020_ = lean_apply_2(v_x_1016_, v___y_1017_, lean_box(0));
v___x_1021_ = lean_get_set_stdin(v___x_1019_);
lean_dec_ref(v___x_1021_);
return v___x_1020_;
}
}
LEAN_EXPORT void l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1015_ = stack[0].m_obj;
lean_object* v_x_1016_ = stack[1].m_obj;
lean_object* v___y_1017_ = stack[2].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1015_, v_x_1016_, v___y_1017_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1023_, v_x_1024_, v___y_1025_);
lean_dec_ref(v___y_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1030_ = lean_panic_fn_borrowed(v___x_1029_, v_msg_1028_);
return v___x_1030_;
}
}
lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_get_set_stdout(v_h_1031_);
lean_inc_ref(v___y_1033_);
v___x_1036_ = lean_apply_2(v_x_1032_, v___y_1033_, lean_box(0));
v___x_1037_ = lean_get_set_stdout(v___x_1035_);
lean_dec_ref(v___x_1037_);
return v___x_1036_;
}
}
LEAN_EXPORT void l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1031_ = stack[0].m_obj;
lean_object* v_x_1032_ = stack[1].m_obj;
lean_object* v___y_1033_ = stack[2].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1031_, v_x_1032_, v___y_1033_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1039_, v_x_1040_, v___y_1041_);
lean_dec_ref(v___y_1041_);
return v_res_1043_;
}
}
lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_1044_, lean_object* v_h_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1045_, v_x_1046_, v___y_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT void l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1045_ = stack[1].m_obj;
lean_object* v_x_1046_ = stack[2].m_obj;
lean_object* v___y_1047_ = stack[3].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_box(0), v_h_1045_, v_x_1046_, v___y_1047_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_h_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1051_, v_h_1052_, v_x_1053_, v___y_1054_);
lean_dec_ref(v___y_1054_);
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
lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1069_, uint8_t v_isolateStderr_1070_, lean_object* v___y_1071_){
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
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1069_ = stack[0].m_obj;
uint8_t v_isolateStderr_1070_ = stack[1].m_num;
lean_object* v___y_1071_ = stack[2].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1069_, v_isolateStderr_1070_, v___y_1071_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1094_, lean_object* v_isolateStderr_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_isolateStderr_boxed_1098_; lean_object* v_res_1099_; 
v_isolateStderr_boxed_1098_ = lean_unbox(v_isolateStderr_1095_);
v_res_1099_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1094_, v_isolateStderr_boxed_1098_, v___y_1096_);
lean_dec_ref(v___y_1096_);
return v_res_1099_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = 1;
v___x_1109_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1110_ = l_Lean_Name_toString(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1111_, lean_object* v_revCmds_1112_, lean_object* v_cmdState_1113_, lean_object* v_beginPos_1114_, lean_object* v_snap_1115_, lean_object* v_cancelTk_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_env_1119_; lean_object* v_scopes_1120_; lean_object* v_usedQuotCtxts_1121_; lean_object* v_nextMacroScope_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_ngen_1124_; lean_object* v_auxDeclNGen_1125_; lean_object* v_infoState_1126_; lean_object* v_prevLinterStates_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1209_; 
v_env_1119_ = lean_ctor_get(v_cmdState_1113_, 0);
v_scopes_1120_ = lean_ctor_get(v_cmdState_1113_, 2);
v_usedQuotCtxts_1121_ = lean_ctor_get(v_cmdState_1113_, 3);
v_nextMacroScope_1122_ = lean_ctor_get(v_cmdState_1113_, 4);
v_maxRecDepth_1123_ = lean_ctor_get(v_cmdState_1113_, 5);
v_ngen_1124_ = lean_ctor_get(v_cmdState_1113_, 6);
v_auxDeclNGen_1125_ = lean_ctor_get(v_cmdState_1113_, 7);
v_infoState_1126_ = lean_ctor_get(v_cmdState_1113_, 8);
v_prevLinterStates_1127_ = lean_ctor_get(v_cmdState_1113_, 11);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_cmdState_1113_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; lean_object* v_unused_1213_; 
v_unused_1210_ = lean_ctor_get(v_cmdState_1113_, 12);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_cmdState_1113_, 10);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_cmdState_1113_, 9);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_cmdState_1113_, 1);
lean_dec(v_unused_1213_);
v___x_1129_ = v_cmdState_1113_;
v_isShared_1130_ = v_isSharedCheck_1209_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_prevLinterStates_1127_);
lean_inc(v_infoState_1126_);
lean_inc(v_auxDeclNGen_1125_);
lean_inc(v_ngen_1124_);
lean_inc(v_maxRecDepth_1123_);
lean_inc(v_nextMacroScope_1122_);
lean_inc(v_usedQuotCtxts_1121_);
lean_inc(v_scopes_1120_);
lean_inc(v_env_1119_);
lean_dec(v_cmdState_1113_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1209_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___f_1131_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1131_, 0, v_stx_1111_);
lean_closure_set(v___f_1131_, 1, v_revCmds_1112_);
v___x_1132_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1133_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1134_ = l_List_head_x21___redArg(v___x_1132_, v_scopes_1120_);
v___x_1135_ = l_Lean_MessageLog_empty;
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1138_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 12, v___x_1138_);
lean_ctor_set(v___x_1129_, 10, v___x_1138_);
lean_ctor_set(v___x_1129_, 9, v___x_1137_);
lean_ctor_set(v___x_1129_, 1, v___x_1135_);
v___x_1140_ = v___x_1129_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_env_1119_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_scopes_1120_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_usedQuotCtxts_1121_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_nextMacroScope_1122_);
lean_ctor_set(v_reuseFailAlloc_1208_, 5, v_maxRecDepth_1123_);
lean_ctor_set(v_reuseFailAlloc_1208_, 6, v_ngen_1124_);
lean_ctor_set(v_reuseFailAlloc_1208_, 7, v_auxDeclNGen_1125_);
lean_ctor_set(v_reuseFailAlloc_1208_, 8, v_infoState_1126_);
lean_ctor_set(v_reuseFailAlloc_1208_, 9, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1208_, 10, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1208_, 11, v_prevLinterStates_1127_);
lean_ctor_set(v_reuseFailAlloc_1208_, 12, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v_toProcessingContext_1142_; lean_object* v_fileName_1143_; lean_object* v_fileMap_1144_; lean_object* v_opts_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v_env_1153_; lean_object* v_scopes_1154_; lean_object* v_usedQuotCtxts_1155_; lean_object* v_nextMacroScope_1156_; lean_object* v_maxRecDepth_1157_; lean_object* v_ngen_1158_; lean_object* v_auxDeclNGen_1159_; lean_object* v_infoState_1160_; lean_object* v_traceState_1161_; lean_object* v_snapshotTasks_1162_; lean_object* v_prevLinterStates_1163_; lean_object* v_codeQualityEntryTasks_1164_; uint8_t v___y_1165_; lean_object* v_messages_1166_; lean_object* v___y_1175_; 
v___x_1141_ = lean_st_mk_ref(v___x_1140_);
v_toProcessingContext_1142_ = lean_ctor_get(v_a_1117_, 0);
v_fileName_1143_ = lean_ctor_get(v_toProcessingContext_1142_, 1);
v_fileMap_1144_ = lean_ctor_get(v_toProcessingContext_1142_, 2);
v_opts_1145_ = lean_ctor_get(v___x_1134_, 1);
lean_inc_ref(v_opts_1145_);
lean_dec(v___x_1134_);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Lean_firstFrontendMacroScope;
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Lean_internal_cmdlineSnapshots;
v___x_1151_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1145_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1207_; 
lean_inc_ref(v_snap_1115_);
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_snap_1115_);
v___y_1175_ = v___x_1207_;
goto v___jp_1174_;
}
else
{
v___y_1175_ = v___x_1147_;
goto v___jp_1174_;
}
v___jp_1152_:
{
lean_object* v_new_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_new_1167_ = lean_ctor_get(v_snap_1115_, 1);
lean_inc(v_new_1167_);
lean_dec_ref(v_snap_1115_);
v___x_1168_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1168_, 0, v_env_1153_);
lean_ctor_set(v___x_1168_, 1, v_messages_1166_);
lean_ctor_set(v___x_1168_, 2, v_scopes_1154_);
lean_ctor_set(v___x_1168_, 3, v_usedQuotCtxts_1155_);
lean_ctor_set(v___x_1168_, 4, v_nextMacroScope_1156_);
lean_ctor_set(v___x_1168_, 5, v_maxRecDepth_1157_);
lean_ctor_set(v___x_1168_, 6, v_ngen_1158_);
lean_ctor_set(v___x_1168_, 7, v_auxDeclNGen_1159_);
lean_ctor_set(v___x_1168_, 8, v_infoState_1160_);
lean_ctor_set(v___x_1168_, 9, v_traceState_1161_);
lean_ctor_set(v___x_1168_, 10, v_snapshotTasks_1162_);
lean_ctor_set(v___x_1168_, 11, v_prevLinterStates_1163_);
lean_ctor_set(v___x_1168_, 12, v_codeQualityEntryTasks_1164_);
v___x_1169_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1170_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1171_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
lean_ctor_set(v___x_1171_, 2, v___x_1147_);
lean_ctor_set(v___x_1171_, 3, v___x_1137_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*4, v___y_1165_);
v___x_1172_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1133_, v___x_1171_);
v___x_1173_ = lean_io_promise_resolve(v___x_1172_, v_new_1167_);
lean_dec(v_new_1167_);
return v___x_1168_;
}
v___jp_1174_:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v_fst_1183_; lean_object* v___x_1184_; lean_object* v_env_1185_; lean_object* v_messages_1186_; lean_object* v_scopes_1187_; lean_object* v_usedQuotCtxts_1188_; lean_object* v_nextMacroScope_1189_; lean_object* v_maxRecDepth_1190_; lean_object* v_ngen_1191_; lean_object* v_auxDeclNGen_1192_; lean_object* v_infoState_1193_; lean_object* v_traceState_1194_; lean_object* v_snapshotTasks_1195_; lean_object* v_prevLinterStates_1196_; lean_object* v_codeQualityEntryTasks_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_cancelTk_1116_);
v___x_1177_ = 0;
lean_inc(v_beginPos_1114_);
lean_inc_ref(v_fileMap_1144_);
lean_inc_ref(v_fileName_1143_);
v___x_1178_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1178_, 0, v_fileName_1143_);
lean_ctor_set(v___x_1178_, 1, v_fileMap_1144_);
lean_ctor_set(v___x_1178_, 2, v___x_1136_);
lean_ctor_set(v___x_1178_, 3, v_beginPos_1114_);
lean_ctor_set(v___x_1178_, 4, v___x_1146_);
lean_ctor_set(v___x_1178_, 5, v___x_1147_);
lean_ctor_set(v___x_1178_, 6, v___x_1148_);
lean_ctor_set(v___x_1178_, 7, v___x_1149_);
lean_ctor_set(v___x_1178_, 8, v___y_1175_);
lean_ctor_set(v___x_1178_, 9, v___x_1176_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*10, v___x_1177_);
lean_inc(v___x_1141_);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1179_, 0, v___f_1131_);
lean_closure_set(v___f_1179_, 1, v___x_1178_);
lean_closure_set(v___f_1179_, 2, v___x_1141_);
v___x_1180_ = l_Lean_Core_stderrAsMessages;
v___x_1181_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1145_, v___x_1180_);
lean_dec_ref(v_opts_1145_);
v___x_1182_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1179_, v___x_1181_, v_a_1117_);
v_fst_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_fst_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = lean_st_ref_get(v___x_1141_);
lean_dec(v___x_1141_);
v_env_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc_ref(v_env_1185_);
v_messages_1186_ = lean_ctor_get(v___x_1184_, 1);
lean_inc_ref(v_messages_1186_);
v_scopes_1187_ = lean_ctor_get(v___x_1184_, 2);
lean_inc(v_scopes_1187_);
v_usedQuotCtxts_1188_ = lean_ctor_get(v___x_1184_, 3);
lean_inc(v_usedQuotCtxts_1188_);
v_nextMacroScope_1189_ = lean_ctor_get(v___x_1184_, 4);
lean_inc(v_nextMacroScope_1189_);
v_maxRecDepth_1190_ = lean_ctor_get(v___x_1184_, 5);
lean_inc(v_maxRecDepth_1190_);
v_ngen_1191_ = lean_ctor_get(v___x_1184_, 6);
lean_inc_ref(v_ngen_1191_);
v_auxDeclNGen_1192_ = lean_ctor_get(v___x_1184_, 7);
lean_inc_ref(v_auxDeclNGen_1192_);
v_infoState_1193_ = lean_ctor_get(v___x_1184_, 8);
lean_inc_ref(v_infoState_1193_);
v_traceState_1194_ = lean_ctor_get(v___x_1184_, 9);
lean_inc_ref(v_traceState_1194_);
v_snapshotTasks_1195_ = lean_ctor_get(v___x_1184_, 10);
lean_inc_ref(v_snapshotTasks_1195_);
v_prevLinterStates_1196_ = lean_ctor_get(v___x_1184_, 11);
lean_inc(v_prevLinterStates_1196_);
v_codeQualityEntryTasks_1197_ = lean_ctor_get(v___x_1184_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1197_);
lean_dec(v___x_1184_);
v___x_1198_ = lean_string_utf8_byte_size(v_fst_1183_);
v___x_1199_ = lean_nat_dec_eq(v___x_1198_, v___x_1136_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref(v_fileMap_1144_);
v___x_1200_ = l_Lean_FileMap_toPosition(v_fileMap_1144_, v_beginPos_1114_);
lean_dec(v_beginPos_1114_);
v___x_1201_ = 0;
v___x_1202_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_fst_1183_);
v___x_1204_ = l_Lean_MessageData_ofFormat(v___x_1203_);
lean_inc_ref(v_fileName_1143_);
v___x_1205_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1205_, 0, v_fileName_1143_);
lean_ctor_set(v___x_1205_, 1, v___x_1200_);
lean_ctor_set(v___x_1205_, 2, v___x_1147_);
lean_ctor_set(v___x_1205_, 3, v___x_1202_);
lean_ctor_set(v___x_1205_, 4, v___x_1204_);
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*5, v___x_1177_);
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*5 + 1, v___x_1201_);
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*5 + 2, v___x_1177_);
v___x_1206_ = l_Lean_MessageLog_add(v___x_1205_, v_messages_1186_);
v_env_1153_ = v_env_1185_;
v_scopes_1154_ = v_scopes_1187_;
v_usedQuotCtxts_1155_ = v_usedQuotCtxts_1188_;
v_nextMacroScope_1156_ = v_nextMacroScope_1189_;
v_maxRecDepth_1157_ = v_maxRecDepth_1190_;
v_ngen_1158_ = v_ngen_1191_;
v_auxDeclNGen_1159_ = v_auxDeclNGen_1192_;
v_infoState_1160_ = v_infoState_1193_;
v_traceState_1161_ = v_traceState_1194_;
v_snapshotTasks_1162_ = v_snapshotTasks_1195_;
v_prevLinterStates_1163_ = v_prevLinterStates_1196_;
v_codeQualityEntryTasks_1164_ = v_codeQualityEntryTasks_1197_;
v___y_1165_ = v___x_1177_;
v_messages_1166_ = v___x_1206_;
goto v___jp_1152_;
}
else
{
lean_dec(v_fst_1183_);
lean_dec(v_beginPos_1114_);
v_env_1153_ = v_env_1185_;
v_scopes_1154_ = v_scopes_1187_;
v_usedQuotCtxts_1155_ = v_usedQuotCtxts_1188_;
v_nextMacroScope_1156_ = v_nextMacroScope_1189_;
v_maxRecDepth_1157_ = v_maxRecDepth_1190_;
v_ngen_1158_ = v_ngen_1191_;
v_auxDeclNGen_1159_ = v_auxDeclNGen_1192_;
v_infoState_1160_ = v_infoState_1193_;
v_traceState_1161_ = v_traceState_1194_;
v_snapshotTasks_1162_ = v_snapshotTasks_1195_;
v_prevLinterStates_1163_ = v_prevLinterStates_1196_;
v_codeQualityEntryTasks_1164_ = v_codeQualityEntryTasks_1197_;
v___y_1165_ = v___x_1177_;
v_messages_1166_ = v_messages_1186_;
goto v___jp_1152_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1111_ = stack[0].m_obj;
lean_object* v_revCmds_1112_ = stack[1].m_obj;
lean_object* v_cmdState_1113_ = stack[2].m_obj;
lean_object* v_beginPos_1114_ = stack[3].m_obj;
lean_object* v_snap_1115_ = stack[4].m_obj;
lean_object* v_cancelTk_1116_ = stack[5].m_obj;
lean_object* v_a_1117_ = stack[6].m_obj;
lean_object* v_res_1214_;
v_res_1214_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1111_, v_revCmds_1112_, v_cmdState_1113_, v_beginPos_1114_, v_snap_1115_, v_cancelTk_1116_, v_a_1117_);
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1215_, lean_object* v_revCmds_1216_, lean_object* v_cmdState_1217_, lean_object* v_beginPos_1218_, lean_object* v_snap_1219_, lean_object* v_cancelTk_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1215_, v_revCmds_1216_, v_cmdState_1217_, v_beginPos_1218_, v_snap_1219_, v_cancelTk_1220_, v_a_1221_);
lean_dec_ref(v_a_1221_);
return v_res_1223_;
}
}
lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1224_, lean_object* v_h_1225_, lean_object* v_x_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1225_, v_x_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT void l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1225_ = stack[1].m_obj;
lean_object* v_x_1226_ = stack[2].m_obj;
lean_object* v___y_1227_ = stack[3].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_box(0), v_h_1225_, v_x_1226_, v___y_1227_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_h_1232_, lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1231_, v_h_1232_, v_x_1233_, v___y_1234_);
lean_dec_ref(v___y_1234_);
return v_res_1236_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1237_, lean_object* v_x_1238_, uint8_t v_isolateStderr_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1238_, v_isolateStderr_1239_, v___y_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1238_ = stack[1].m_obj;
uint8_t v_isolateStderr_1239_ = stack[2].m_num;
lean_object* v___y_1240_ = stack[3].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_box(0), v_x_1238_, v_isolateStderr_1239_, v___y_1240_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_x_1245_, lean_object* v_isolateStderr_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v_isolateStderr_boxed_1249_; lean_object* v_res_1250_; 
v_isolateStderr_boxed_1249_ = lean_unbox(v_isolateStderr_1246_);
v_res_1250_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1244_, v_x_1245_, v_isolateStderr_boxed_1249_, v___y_1247_);
lean_dec_ref(v___y_1247_);
return v_res_1250_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1251_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1251_ = stack[0].m_obj;
lean_object* v___y_1252_ = stack[1].m_obj;
lean_object* v___y_1253_ = stack[2].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1251_, v___y_1252_, v___y_1253_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1262_){
_start:
{
lean_object* v_toSnapshotTreeM_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_toSnapshotTreeM_1263_ = lean_ctor_get(v_a_1262_, 1);
lean_inc_ref(v_toSnapshotTreeM_1263_);
lean_dec_ref(v_a_1262_);
v___x_1264_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1265_ = lean_apply_1(v_toSnapshotTreeM_1263_, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1266_){
_start:
{
lean_object* v_toSnapshot_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_toSnapshot_1267_ = lean_ctor_get(v_a_1266_, 0);
lean_inc_ref(v_toSnapshot_1267_);
lean_dec_ref(v_a_1266_);
v___x_1268_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1269_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1267_, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1274_ = l_Lean_Language_Snapshot_transform(v_a_1272_, v___x_1273_);
v___x_1275_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1277_, lean_object* v_opt_1278_){
_start:
{
lean_object* v_name_1279_; lean_object* v_defValue_1280_; lean_object* v_map_1281_; lean_object* v___x_1282_; 
v_name_1279_ = lean_ctor_get(v_opt_1278_, 0);
v_defValue_1280_ = lean_ctor_get(v_opt_1278_, 1);
v_map_1281_ = lean_ctor_get(v_opts_1277_, 0);
v___x_1282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1281_, v_name_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_inc(v_defValue_1280_);
return v_defValue_1280_;
}
else
{
lean_object* v_val_1283_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v___x_1282_, 1);
if (lean_obj_tag(v_val_1283_) == 3)
{
lean_object* v_v_1284_; 
v_v_1284_ = lean_ctor_get(v_val_1283_, 0);
lean_inc(v_v_1284_);
lean_dec_ref_known(v_val_1283_, 1);
return v_v_1284_;
}
else
{
lean_dec(v_val_1283_);
lean_inc(v_defValue_1280_);
return v_defValue_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1285_, lean_object* v_opt_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1285_, v_opt_1286_);
lean_dec_ref(v_opt_1286_);
lean_dec_ref(v_opts_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1290_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1288_, v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1297_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1298_ = l_Lean_Name_append(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1299_, lean_object* v___x_1300_, uint8_t v_val_1301_, lean_object* v_val_1302_, lean_object* v_val_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, uint8_t v___x_1306_, lean_object* v_a_1307_, lean_object* v_pos_1308_, lean_object* v___x_1309_, lean_object* v_infoSt_1310_){
_start:
{
lean_object* v___y_1313_; lean_object* v_msgLog_1314_; lean_object* v___y_1320_; lean_object* v_trees_1352_; lean_object* v_size_1353_; uint8_t v___x_1354_; 
v_trees_1352_ = lean_ctor_get(v_infoSt_1310_, 2);
v_size_1353_ = lean_ctor_get(v_trees_1352_, 2);
v___x_1354_ = lean_nat_dec_lt(v___x_1305_, v_size_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = l_outOfBounds___redArg(v___x_1309_);
v___y_1320_ = v___x_1355_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1309_, v_trees_1352_, v___x_1305_);
v___y_1320_ = v___x_1356_;
goto v___jp_1319_;
}
v___jp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1314_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1313_);
v___x_1317_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1317_, 0, v___x_1299_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_ctor_set(v___x_1317_, 2, v___x_1316_);
lean_ctor_set(v___x_1317_, 3, v___x_1300_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*4, v_val_1301_);
v___x_1318_ = lean_io_promise_resolve(v___x_1317_, v_val_1302_);
return v___x_1318_;
}
v___jp_1319_:
{
lean_object* v_scopes_1321_; lean_object* v___x_1322_; lean_object* v_opts_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v_hasTrace_1327_; 
v_scopes_1321_ = lean_ctor_get(v_val_1303_, 2);
v___x_1322_ = l_List_head_x21___redArg(v___x_1304_, v_scopes_1321_);
v_opts_1323_ = lean_ctor_get(v___x_1322_, 1);
lean_inc_ref(v_opts_1323_);
lean_dec(v___x_1322_);
v___x_1324_ = l_Lean_MessageLog_empty;
v___x_1325_ = l_Lean_inheritedTraceOptions;
v___x_1326_ = lean_st_ref_get(v___x_1325_);
v_hasTrace_1327_ = lean_ctor_get_uint8(v_opts_1323_, sizeof(void*)*1);
if (v_hasTrace_1327_ == 0)
{
lean_dec(v___x_1326_);
lean_dec_ref(v_opts_1323_);
lean_dec(v___x_1305_);
v___y_1313_ = v___y_1320_;
v_msgLog_1314_ = v___x_1324_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1329_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1330_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1331_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1326_, v_opts_1323_, v___x_1330_);
lean_dec_ref(v_opts_1323_);
lean_dec(v___x_1326_);
if (v___x_1331_ == 0)
{
lean_dec(v___x_1305_);
v___y_1313_ = v___y_1320_;
v_msgLog_1314_ = v___x_1324_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_box(0);
lean_inc_ref(v___y_1320_);
v___x_1333_ = l_Lean_Elab_InfoTree_format(v___y_1320_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; double v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_toProcessingContext_1338_; lean_object* v_fileName_1339_; lean_object* v_fileMap_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = lean_float_of_nat(v___x_1305_);
v___x_1336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1337_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1337_, 0, v___x_1328_);
lean_ctor_set(v___x_1337_, 1, v___x_1332_);
lean_ctor_set(v___x_1337_, 2, v___x_1336_);
lean_ctor_set_float(v___x_1337_, sizeof(void*)*3, v___x_1335_);
lean_ctor_set_float(v___x_1337_, sizeof(void*)*3 + 8, v___x_1335_);
lean_ctor_set_uint8(v___x_1337_, sizeof(void*)*3 + 16, v___x_1306_);
v_toProcessingContext_1338_ = lean_ctor_get(v_a_1307_, 0);
v_fileName_1339_ = lean_ctor_get(v_toProcessingContext_1338_, 1);
v_fileMap_1340_ = lean_ctor_get(v_toProcessingContext_1338_, 2);
v___x_1341_ = l_Lean_MessageData_nil;
v___x_1342_ = l_Lean_MessageData_ofFormat(v_a_1334_);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_mk_empty_array_with_capacity(v___x_1343_);
v___x_1345_ = lean_array_push(v___x_1344_, v___x_1342_);
v___x_1346_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1337_);
lean_ctor_set(v___x_1346_, 1, v___x_1341_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1329_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
lean_inc_ref(v_fileMap_1340_);
v___x_1348_ = l_Lean_FileMap_toPosition(v_fileMap_1340_, v_pos_1308_);
v___x_1349_ = 0;
lean_inc_ref(v_fileName_1339_);
v___x_1350_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1350_, 0, v_fileName_1339_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1332_);
lean_ctor_set(v___x_1350_, 3, v___x_1336_);
lean_ctor_set(v___x_1350_, 4, v___x_1347_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*5, v_val_1301_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*5 + 1, v___x_1349_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*5 + 2, v_val_1301_);
v___x_1351_ = l_Lean_MessageLog_add(v___x_1350_, v___x_1324_);
v___y_1313_ = v___y_1320_;
v_msgLog_1314_ = v___x_1351_;
goto v___jp_1312_;
}
else
{
lean_dec_ref_known(v___x_1333_, 1);
lean_dec(v___x_1305_);
v___y_1313_ = v___y_1320_;
v_msgLog_1314_ = v___x_1324_;
goto v___jp_1312_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1299_ = stack[0].m_obj;
lean_object* v___x_1300_ = stack[1].m_obj;
uint8_t v_val_1301_ = stack[2].m_num;
lean_object* v_val_1302_ = stack[3].m_obj;
lean_object* v_val_1303_ = stack[4].m_obj;
lean_object* v___x_1304_ = stack[5].m_obj;
lean_object* v___x_1305_ = stack[6].m_obj;
uint8_t v___x_1306_ = stack[7].m_num;
lean_object* v_a_1307_ = stack[8].m_obj;
lean_object* v_pos_1308_ = stack[9].m_obj;
lean_object* v___x_1309_ = stack[10].m_obj;
lean_object* v_infoSt_1310_ = stack[11].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1299_, v___x_1300_, v_val_1301_, v_val_1302_, v_val_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v_a_1307_, v_pos_1308_, v___x_1309_, v_infoSt_1310_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v_val_1360_, lean_object* v_val_1361_, lean_object* v_val_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v___x_1365_, lean_object* v_a_1366_, lean_object* v_pos_1367_, lean_object* v___x_1368_, lean_object* v_infoSt_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_val_36502__boxed_1371_; uint8_t v___x_36507__boxed_1372_; lean_object* v_res_1373_; 
v_val_36502__boxed_1371_ = lean_unbox(v_val_1360_);
v___x_36507__boxed_1372_ = lean_unbox(v___x_1365_);
v_res_1373_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1358_, v___x_1359_, v_val_36502__boxed_1371_, v_val_1361_, v_val_1362_, v___x_1363_, v___x_1364_, v___x_36507__boxed_1372_, v_a_1366_, v_pos_1367_, v___x_1368_, v_infoSt_1369_);
lean_dec_ref(v_infoSt_1369_);
lean_dec_ref(v___x_1368_);
lean_dec(v_pos_1367_);
lean_dec_ref(v_a_1366_);
lean_dec_ref(v___x_1363_);
lean_dec_ref(v_val_1362_);
lean_dec(v_val_1361_);
return v_res_1373_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v___x_1376_, uint8_t v_val_1377_, lean_object* v_as_1378_, size_t v_sz_1379_, size_t v_i_1380_, lean_object* v_b_1381_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_usize_dec_lt(v_i_1380_, v_sz_1379_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v___x_1376_);
lean_dec_ref(v___x_1374_);
return v_b_1381_;
}
else
{
lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1402_; 
v_snd_1384_ = lean_ctor_get(v_b_1381_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_b_1381_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_b_1381_, 0);
lean_dec(v_unused_1403_);
v___x_1386_ = v_b_1381_;
v_isShared_1387_ = v_isSharedCheck_1402_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_dec(v_b_1381_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1402_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_a_1388_; lean_object* v_msg_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v_a_1388_ = lean_array_uget_borrowed(v_as_1378_, v_i_1380_);
v_msg_1389_ = lean_ctor_get(v_a_1388_, 1);
v___x_1390_ = lean_box(0);
lean_inc_ref(v___x_1374_);
v___x_1391_ = l_Lean_FileMap_toPosition(v___x_1374_, v___x_1375_);
v___x_1392_ = 0;
v___x_1393_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1389_);
lean_inc_ref(v___x_1376_);
v___x_1394_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1394_, 0, v___x_1376_);
lean_ctor_set(v___x_1394_, 1, v___x_1391_);
lean_ctor_set(v___x_1394_, 2, v___x_1390_);
lean_ctor_set(v___x_1394_, 3, v___x_1393_);
lean_ctor_set(v___x_1394_, 4, v_msg_1389_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*5, v_val_1377_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*5 + 1, v___x_1392_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*5 + 2, v_val_1377_);
v___x_1395_ = l_Lean_MessageLog_add(v___x_1394_, v_snd_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1395_);
lean_ctor_set(v___x_1386_, 0, v___x_1390_);
v___x_1397_ = v___x_1386_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
size_t v___x_1398_; size_t v___x_1399_; 
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1380_, v___x_1398_);
v_i_1380_ = v___x_1399_;
v_b_1381_ = v___x_1397_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1374_ = stack[0].m_obj;
lean_object* v___x_1375_ = stack[1].m_obj;
lean_object* v___x_1376_ = stack[2].m_obj;
uint8_t v_val_1377_ = stack[3].m_num;
lean_object* v_as_1378_ = stack[4].m_obj;
size_t v_sz_1379_ = stack[5].m_num;
size_t v_i_1380_ = stack[6].m_num;
lean_object* v_b_1381_ = stack[7].m_obj;
lean_object* v_res_1404_;
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1374_, v___x_1375_, v___x_1376_, v_val_1377_, v_as_1378_, v_sz_1379_, v_i_1380_, v_b_1381_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v_val_1408_, lean_object* v_as_1409_, lean_object* v_sz_1410_, lean_object* v_i_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v_val_36679__boxed_1414_; size_t v_sz_boxed_1415_; size_t v_i_boxed_1416_; lean_object* v_res_1417_; 
v_val_36679__boxed_1414_ = lean_unbox(v_val_1408_);
v_sz_boxed_1415_ = lean_unbox_usize(v_sz_1410_);
lean_dec(v_sz_1410_);
v_i_boxed_1416_ = lean_unbox_usize(v_i_1411_);
lean_dec(v_i_1411_);
v_res_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1405_, v___x_1406_, v___x_1407_, v_val_36679__boxed_1414_, v_as_1409_, v_sz_boxed_1415_, v_i_boxed_1416_, v_b_1412_);
lean_dec_ref(v_as_1409_);
lean_dec(v___x_1406_);
return v_res_1417_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, uint8_t v_val_1421_, lean_object* v_as_1422_, size_t v_sz_1423_, size_t v_i_1424_, lean_object* v_b_1425_){
_start:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_lt(v_i_1424_, v_sz_1423_);
if (v___x_1427_ == 0)
{
lean_dec_ref(v___x_1420_);
lean_dec_ref(v___x_1418_);
return v_b_1425_;
}
else
{
lean_object* v_snd_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1446_; 
v_snd_1428_ = lean_ctor_get(v_b_1425_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_b_1425_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_b_1425_, 0);
lean_dec(v_unused_1447_);
v___x_1430_ = v_b_1425_;
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snd_1428_);
lean_dec(v_b_1425_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1446_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_a_1432_; lean_object* v_msg_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v_a_1432_ = lean_array_uget_borrowed(v_as_1422_, v_i_1424_);
v_msg_1433_ = lean_ctor_get(v_a_1432_, 1);
v___x_1434_ = lean_box(0);
lean_inc_ref(v___x_1418_);
v___x_1435_ = l_Lean_FileMap_toPosition(v___x_1418_, v___x_1419_);
v___x_1436_ = 0;
v___x_1437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1433_);
lean_inc_ref(v___x_1420_);
v___x_1438_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1438_, 0, v___x_1420_);
lean_ctor_set(v___x_1438_, 1, v___x_1435_);
lean_ctor_set(v___x_1438_, 2, v___x_1434_);
lean_ctor_set(v___x_1438_, 3, v___x_1437_);
lean_ctor_set(v___x_1438_, 4, v_msg_1433_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*5, v_val_1421_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*5 + 1, v___x_1436_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*5 + 2, v_val_1421_);
v___x_1439_ = l_Lean_MessageLog_add(v___x_1438_, v_snd_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1439_);
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1441_ = v___x_1430_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
size_t v___x_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_add(v_i_1424_, v___x_1442_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1418_, v___x_1419_, v___x_1420_, v_val_1421_, v_as_1422_, v_sz_1423_, v___x_1443_, v___x_1441_);
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1418_ = stack[0].m_obj;
lean_object* v___x_1419_ = stack[1].m_obj;
lean_object* v___x_1420_ = stack[2].m_obj;
uint8_t v_val_1421_ = stack[3].m_num;
lean_object* v_as_1422_ = stack[4].m_obj;
size_t v_sz_1423_ = stack[5].m_num;
size_t v_i_1424_ = stack[6].m_num;
lean_object* v_b_1425_ = stack[7].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1418_, v___x_1419_, v___x_1420_, v_val_1421_, v_as_1422_, v_sz_1423_, v_i_1424_, v_b_1425_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1449_, lean_object* v___x_1450_, lean_object* v___x_1451_, lean_object* v_val_1452_, lean_object* v_as_1453_, lean_object* v_sz_1454_, lean_object* v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v_val_36759__boxed_1458_; size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_val_36759__boxed_1458_ = lean_unbox(v_val_1452_);
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1454_);
lean_dec(v_sz_1454_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1449_, v___x_1450_, v___x_1451_, v_val_36759__boxed_1458_, v_as_1453_, v_sz_boxed_1459_, v_i_boxed_1460_, v_b_1456_);
lean_dec_ref(v_as_1453_);
lean_dec(v___x_1450_);
return v_res_1461_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1462_, lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v___x_1465_, uint8_t v_val_1466_, lean_object* v_n_1467_, lean_object* v_b_1468_){
_start:
{
if (lean_obj_tag(v_n_1467_) == 0)
{
lean_object* v_cs_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v_fst_1476_; 
v_cs_1470_ = lean_ctor_get(v_n_1467_, 0);
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v_b_1468_);
v_sz_1473_ = lean_array_size(v_cs_1470_);
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1462_, v___x_1463_, v___x_1464_, v___x_1465_, v_val_1466_, v_cs_1470_, v_sz_1473_, v___x_1474_, v___x_1472_);
v_fst_1476_ = lean_ctor_get(v___x_1475_, 0);
if (lean_obj_tag(v_fst_1476_) == 0)
{
lean_object* v_snd_1477_; lean_object* v___x_1478_; 
v_snd_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_snd_1477_);
lean_dec_ref(v___x_1475_);
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_snd_1477_);
return v___x_1478_;
}
else
{
lean_object* v_val_1479_; 
lean_inc_ref(v_fst_1476_);
lean_dec_ref(v___x_1475_);
v_val_1479_ = lean_ctor_get(v_fst_1476_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v_fst_1476_, 1);
return v_val_1479_;
}
}
else
{
lean_object* v_vs_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v_fst_1486_; 
v_vs_1480_ = lean_ctor_get(v_n_1467_, 0);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_b_1468_);
v_sz_1483_ = lean_array_size(v_vs_1480_);
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1463_, v___x_1464_, v___x_1465_, v_val_1466_, v_vs_1480_, v_sz_1483_, v___x_1484_, v___x_1482_);
v_fst_1486_ = lean_ctor_get(v___x_1485_, 0);
if (lean_obj_tag(v_fst_1486_) == 0)
{
lean_object* v_snd_1487_; lean_object* v___x_1488_; 
v_snd_1487_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_snd_1487_);
lean_dec_ref(v___x_1485_);
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_snd_1487_);
return v___x_1488_;
}
else
{
lean_object* v_val_1489_; 
lean_inc_ref(v_fst_1486_);
lean_dec_ref(v___x_1485_);
v_val_1489_ = lean_ctor_get(v_fst_1486_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v_fst_1486_, 1);
return v_val_1489_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1462_ = stack[0].m_obj;
lean_object* v___x_1463_ = stack[1].m_obj;
lean_object* v___x_1464_ = stack[2].m_obj;
lean_object* v___x_1465_ = stack[3].m_obj;
uint8_t v_val_1466_ = stack[4].m_num;
lean_object* v_n_1467_ = stack[5].m_obj;
lean_object* v_b_1468_ = stack[6].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1462_, v___x_1463_, v___x_1464_, v___x_1465_, v_val_1466_, v_n_1467_, v_b_1468_);
stack->m_obj
 = v_res_1490_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1491_, lean_object* v___x_1492_, lean_object* v___x_1493_, lean_object* v___x_1494_, uint8_t v_val_1495_, lean_object* v_as_1496_, size_t v_sz_1497_, size_t v_i_1498_, lean_object* v_b_1499_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_lt(v_i_1498_, v_sz_1497_);
if (v___x_1501_ == 0)
{
lean_dec_ref(v___x_1494_);
lean_dec_ref(v___x_1492_);
return v_b_1499_;
}
else
{
lean_object* v_snd_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1520_; 
v_snd_1502_ = lean_ctor_get(v_b_1499_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_b_1499_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v_b_1499_, 0);
lean_dec(v_unused_1521_);
v___x_1504_ = v_b_1499_;
v_isShared_1505_ = v_isSharedCheck_1520_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_snd_1502_);
lean_dec(v_b_1499_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1520_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v_a_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v_a_1507_ = lean_array_uget_borrowed(v_as_1496_, v_i_1498_);
lean_inc(v_snd_1502_);
lean_inc_ref(v___x_1494_);
lean_inc_ref(v___x_1492_);
v___x_1508_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1491_, v___x_1492_, v___x_1493_, v___x_1494_, v_val_1495_, v_a_1507_, v_snd_1502_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_dec_ref(v___x_1494_);
lean_dec_ref(v___x_1492_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1509_);
v___x_1511_ = v___x_1504_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_snd_1502_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; 
lean_dec(v_snd_1502_);
v_a_1513_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1508_, 1);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 1, v_a_1513_);
lean_ctor_set(v___x_1504_, 0, v___x_1506_);
v___x_1515_ = v___x_1504_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_a_1513_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
size_t v___x_1516_; size_t v___x_1517_; 
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1498_, v___x_1516_);
v_i_1498_ = v___x_1517_;
v_b_1499_ = v___x_1515_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1491_ = stack[0].m_obj;
lean_object* v___x_1492_ = stack[1].m_obj;
lean_object* v___x_1493_ = stack[2].m_obj;
lean_object* v___x_1494_ = stack[3].m_obj;
uint8_t v_val_1495_ = stack[4].m_num;
lean_object* v_as_1496_ = stack[5].m_obj;
size_t v_sz_1497_ = stack[6].m_num;
size_t v_i_1498_ = stack[7].m_num;
lean_object* v_b_1499_ = stack[8].m_obj;
lean_object* v_res_1522_;
v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1491_, v___x_1492_, v___x_1493_, v___x_1494_, v_val_1495_, v_as_1496_, v_sz_1497_, v_i_1498_, v_b_1499_);
stack->m_obj
 = v_res_1522_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_val_1527_, lean_object* v_as_1528_, lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_val_36838__boxed_1533_; size_t v_sz_boxed_1534_; size_t v_i_boxed_1535_; lean_object* v_res_1536_; 
v_val_36838__boxed_1533_ = lean_unbox(v_val_1527_);
v_sz_boxed_1534_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1535_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1523_, v___x_1524_, v___x_1525_, v___x_1526_, v_val_36838__boxed_1533_, v_as_1528_, v_sz_boxed_1534_, v_i_boxed_1535_, v_b_1531_);
lean_dec_ref(v_as_1528_);
lean_dec(v___x_1525_);
lean_dec_ref(v_init_1523_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1537_, lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v___x_1540_, lean_object* v_val_1541_, lean_object* v_n_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v_val_36854__boxed_1545_; lean_object* v_res_1546_; 
v_val_36854__boxed_1545_ = lean_unbox(v_val_1541_);
v_res_1546_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1537_, v___x_1538_, v___x_1539_, v___x_1540_, v_val_36854__boxed_1545_, v_n_1542_, v_b_1543_);
lean_dec_ref(v_n_1542_);
lean_dec(v___x_1539_);
lean_dec_ref(v_init_1537_);
return v_res_1546_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1547_, lean_object* v___x_1548_, lean_object* v___x_1549_, uint8_t v_val_1550_, lean_object* v_as_1551_, size_t v_sz_1552_, size_t v_i_1553_, lean_object* v_b_1554_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_usize_dec_lt(v_i_1553_, v_sz_1552_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v___x_1549_);
lean_dec_ref(v___x_1547_);
return v_b_1554_;
}
else
{
lean_object* v_snd_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1575_; 
v_snd_1557_ = lean_ctor_get(v_b_1554_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_b_1554_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_b_1554_, 0);
lean_dec(v_unused_1576_);
v___x_1559_ = v_b_1554_;
v_isShared_1560_ = v_isSharedCheck_1575_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snd_1557_);
lean_dec(v_b_1554_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1575_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_a_1561_; lean_object* v_msg_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v_a_1561_ = lean_array_uget_borrowed(v_as_1551_, v_i_1553_);
v_msg_1562_ = lean_ctor_get(v_a_1561_, 1);
v___x_1563_ = lean_box(0);
lean_inc_ref(v___x_1547_);
v___x_1564_ = l_Lean_FileMap_toPosition(v___x_1547_, v___x_1548_);
v___x_1565_ = 0;
v___x_1566_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1562_);
lean_inc_ref(v___x_1549_);
v___x_1567_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1567_, 0, v___x_1549_);
lean_ctor_set(v___x_1567_, 1, v___x_1564_);
lean_ctor_set(v___x_1567_, 2, v___x_1563_);
lean_ctor_set(v___x_1567_, 3, v___x_1566_);
lean_ctor_set(v___x_1567_, 4, v_msg_1562_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*5, v_val_1550_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*5 + 1, v___x_1565_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*5 + 2, v_val_1550_);
v___x_1568_ = l_Lean_MessageLog_add(v___x_1567_, v_snd_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v___x_1568_);
lean_ctor_set(v___x_1559_, 0, v___x_1563_);
v___x_1570_ = v___x_1559_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
size_t v___x_1571_; size_t v___x_1572_; 
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1553_, v___x_1571_);
v_i_1553_ = v___x_1572_;
v_b_1554_ = v___x_1570_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1547_ = stack[0].m_obj;
lean_object* v___x_1548_ = stack[1].m_obj;
lean_object* v___x_1549_ = stack[2].m_obj;
uint8_t v_val_1550_ = stack[3].m_num;
lean_object* v_as_1551_ = stack[4].m_obj;
size_t v_sz_1552_ = stack[5].m_num;
size_t v_i_1553_ = stack[6].m_num;
lean_object* v_b_1554_ = stack[7].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1547_, v___x_1548_, v___x_1549_, v_val_1550_, v_as_1551_, v_sz_1552_, v_i_1553_, v_b_1554_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1578_, lean_object* v___x_1579_, lean_object* v___x_1580_, lean_object* v_val_1581_, lean_object* v_as_1582_, lean_object* v_sz_1583_, lean_object* v_i_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_val_36989__boxed_1587_; size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v_val_36989__boxed_1587_ = lean_unbox(v_val_1581_);
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1583_);
lean_dec(v_sz_1583_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1578_, v___x_1579_, v___x_1580_, v_val_36989__boxed_1587_, v_as_1582_, v_sz_boxed_1588_, v_i_boxed_1589_, v_b_1585_);
lean_dec_ref(v_as_1582_);
lean_dec(v___x_1579_);
return v_res_1590_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, uint8_t v_val_1594_, lean_object* v_as_1595_, size_t v_sz_1596_, size_t v_i_1597_, lean_object* v_b_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_lt(v_i_1597_, v_sz_1596_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v___x_1593_);
lean_dec_ref(v___x_1591_);
return v_b_1598_;
}
else
{
lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1619_; 
v_snd_1601_ = lean_ctor_get(v_b_1598_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_b_1598_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; 
v_unused_1620_ = lean_ctor_get(v_b_1598_, 0);
lean_dec(v_unused_1620_);
v___x_1603_ = v_b_1598_;
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_dec(v_b_1598_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_a_1605_; lean_object* v_msg_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v_a_1605_ = lean_array_uget_borrowed(v_as_1595_, v_i_1597_);
v_msg_1606_ = lean_ctor_get(v_a_1605_, 1);
v___x_1607_ = lean_box(0);
lean_inc_ref(v___x_1591_);
v___x_1608_ = l_Lean_FileMap_toPosition(v___x_1591_, v___x_1592_);
v___x_1609_ = 0;
v___x_1610_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1606_);
lean_inc_ref(v___x_1593_);
v___x_1611_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1611_, 0, v___x_1593_);
lean_ctor_set(v___x_1611_, 1, v___x_1608_);
lean_ctor_set(v___x_1611_, 2, v___x_1607_);
lean_ctor_set(v___x_1611_, 3, v___x_1610_);
lean_ctor_set(v___x_1611_, 4, v_msg_1606_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*5, v_val_1594_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*5 + 1, v___x_1609_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*5 + 2, v_val_1594_);
v___x_1612_ = l_Lean_MessageLog_add(v___x_1611_, v_snd_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1612_);
lean_ctor_set(v___x_1603_, 0, v___x_1607_);
v___x_1614_ = v___x_1603_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1597_, v___x_1615_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1591_, v___x_1592_, v___x_1593_, v_val_1594_, v_as_1595_, v_sz_1596_, v___x_1616_, v___x_1614_);
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1591_ = stack[0].m_obj;
lean_object* v___x_1592_ = stack[1].m_obj;
lean_object* v___x_1593_ = stack[2].m_obj;
uint8_t v_val_1594_ = stack[3].m_num;
lean_object* v_as_1595_ = stack[4].m_obj;
size_t v_sz_1596_ = stack[5].m_num;
size_t v_i_1597_ = stack[6].m_num;
lean_object* v_b_1598_ = stack[7].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1591_, v___x_1592_, v___x_1593_, v_val_1594_, v_as_1595_, v_sz_1596_, v_i_1597_, v_b_1598_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v_val_1625_, lean_object* v_as_1626_, lean_object* v_sz_1627_, lean_object* v_i_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v_val_37069__boxed_1631_; size_t v_sz_boxed_1632_; size_t v_i_boxed_1633_; lean_object* v_res_1634_; 
v_val_37069__boxed_1631_ = lean_unbox(v_val_1625_);
v_sz_boxed_1632_ = lean_unbox_usize(v_sz_1627_);
lean_dec(v_sz_1627_);
v_i_boxed_1633_ = lean_unbox_usize(v_i_1628_);
lean_dec(v_i_1628_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1622_, v___x_1623_, v___x_1624_, v_val_37069__boxed_1631_, v_as_1626_, v_sz_boxed_1632_, v_i_boxed_1633_, v_b_1629_);
lean_dec_ref(v_as_1626_);
lean_dec(v___x_1623_);
return v_res_1634_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1635_, lean_object* v___x_1636_, lean_object* v___x_1637_, uint8_t v_val_1638_, lean_object* v_t_1639_, lean_object* v_init_1640_){
_start:
{
lean_object* v_root_1642_; lean_object* v_tail_1643_; lean_object* v___x_1644_; 
v_root_1642_ = lean_ctor_get(v_t_1639_, 0);
v_tail_1643_ = lean_ctor_get(v_t_1639_, 1);
lean_inc_ref(v___x_1637_);
lean_inc_ref(v___x_1635_);
lean_inc_ref(v_init_1640_);
v___x_1644_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1640_, v___x_1635_, v___x_1636_, v___x_1637_, v_val_1638_, v_root_1642_, v_init_1640_);
lean_dec_ref(v_init_1640_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; 
lean_dec_ref(v___x_1637_);
lean_dec_ref(v___x_1635_);
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
return v_a_1645_;
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v_fst_1652_; 
v_a_1646_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_a_1646_);
v_sz_1649_ = lean_array_size(v_tail_1643_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1635_, v___x_1636_, v___x_1637_, v_val_1638_, v_tail_1643_, v_sz_1649_, v___x_1650_, v___x_1648_);
v_fst_1652_ = lean_ctor_get(v___x_1651_, 0);
if (lean_obj_tag(v_fst_1652_) == 0)
{
lean_object* v_snd_1653_; 
v_snd_1653_ = lean_ctor_get(v___x_1651_, 1);
lean_inc(v_snd_1653_);
lean_dec_ref(v___x_1651_);
return v_snd_1653_;
}
else
{
lean_object* v_val_1654_; 
lean_inc_ref(v_fst_1652_);
lean_dec_ref(v___x_1651_);
v_val_1654_ = lean_ctor_get(v_fst_1652_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v_fst_1652_, 1);
return v_val_1654_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1635_ = stack[0].m_obj;
lean_object* v___x_1636_ = stack[1].m_obj;
lean_object* v___x_1637_ = stack[2].m_obj;
uint8_t v_val_1638_ = stack[3].m_num;
lean_object* v_t_1639_ = stack[4].m_obj;
lean_object* v_init_1640_ = stack[5].m_obj;
lean_object* v_res_1655_;
v_res_1655_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1635_, v___x_1636_, v___x_1637_, v_val_1638_, v_t_1639_, v_init_1640_);
stack->m_obj
 = v_res_1655_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1656_, lean_object* v___x_1657_, lean_object* v___x_1658_, lean_object* v_val_1659_, lean_object* v_t_1660_, lean_object* v_init_1661_, lean_object* v___y_1662_){
_start:
{
uint8_t v_val_37148__boxed_1663_; lean_object* v_res_1664_; 
v_val_37148__boxed_1663_ = lean_unbox(v_val_1659_);
v_res_1664_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1656_, v___x_1657_, v___x_1658_, v_val_37148__boxed_1663_, v_t_1660_, v_init_1661_);
lean_dec_ref(v_t_1660_);
lean_dec(v___x_1657_);
return v_res_1664_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = l_Lean_firstFrontendMacroScope;
v___x_1667_ = lean_nat_add(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
return v___x_1677_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1678_, lean_object* v_opts_1679_, lean_object* v___x_1680_, lean_object* v___x_1681_, lean_object* v___x_1682_, size_t v___x_1683_, uint8_t v___x_1684_, lean_object* v_env_1685_, lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v_pos_1688_, uint8_t v_val_1689_, lean_object* v___x_1690_, lean_object* v___x_1691_, lean_object* v___x_1692_, lean_object* v___x_1693_, lean_object* v___x_1694_, uint8_t v___x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_toProcessingContext_1698_; lean_object* v_fileName_1699_; lean_object* v_fileMap_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint16_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_fileName_1724_; lean_object* v_fileMap_1725_; lean_object* v_currNamespace_1726_; lean_object* v_openDecls_1727_; lean_object* v_initHeartbeats_1728_; lean_object* v_maxHeartbeats_1729_; lean_object* v_quotContext_1730_; lean_object* v_currMacroScope_1731_; lean_object* v_cancelTk_x3f_1732_; lean_object* v_inheritedTraceOptions_1733_; lean_object* v_currRecDepth_1734_; lean_object* v_ref_1735_; uint8_t v_suppressElabErrors_1736_; uint8_t v_isRecordingDeps_1737_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___y_1757_; uint8_t v___y_1779_; uint8_t v___y_1780_; lean_object* v_env_1781_; uint8_t v___x_1782_; uint8_t v___y_1784_; uint16_t v___x_1785_; uint16_t v___x_1786_; uint16_t v___x_1787_; uint8_t v___x_1788_; 
v_toProcessingContext_1698_ = lean_ctor_get(v_a_1678_, 0);
v_fileName_1699_ = lean_ctor_get(v_toProcessingContext_1698_, 1);
v_fileMap_1700_ = lean_ctor_get(v_toProcessingContext_1698_, 2);
v___x_1701_ = lean_box(0);
v___x_1702_ = l_Lean_Core_getMaxHeartbeats(v_opts_1679_);
v___x_1703_ = l_Lean_firstFrontendMacroScope;
v___x_1704_ = lean_box(0);
v___x_1705_ = l_Lean_OptionFlags_ofOptions(v_opts_1679_);
v___x_1706_ = lean_unsigned_to_nat(1u);
v___x_1707_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1708_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1680_);
v___x_1709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1680_);
lean_ctor_set(v___x_1709_, 1, v___x_1706_);
lean_ctor_set(v___x_1709_, 2, v___x_1701_);
v___x_1710_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1711_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1712_ = lean_mk_empty_array_with_capacity(v___x_1681_);
v___x_1713_ = l_Lean_Options_empty;
lean_inc_n(v___x_1681_, 5);
lean_inc_ref_n(v___x_1712_, 3);
v___x_1714_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
lean_ctor_set(v___x_1714_, 2, v___x_1712_);
lean_ctor_set(v___x_1714_, 3, v___x_1681_);
lean_ctor_set(v___x_1714_, 4, v___x_1681_);
lean_ctor_set(v___x_1714_, 5, v___x_1681_);
v___x_1715_ = lean_mk_empty_array_with_capacity(v___x_1682_);
lean_inc_ref(v___x_1715_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v___x_1715_);
lean_ctor_set(v___x_1717_, 2, v___x_1681_);
lean_ctor_set(v___x_1717_, 3, v___x_1681_);
lean_ctor_set_usize(v___x_1717_, 4, v___x_1683_);
v___x_1718_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1717_, 2);
v___x_1719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1717_);
lean_ctor_set(v___x_1719_, 2, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1720_, 0, v___x_1710_);
lean_ctor_set(v___x_1720_, 1, v___x_1710_);
lean_ctor_set(v___x_1720_, 2, v___x_1717_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*3, v___x_1684_);
lean_inc_ref(v___x_1686_);
v___x_1721_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1721_, 0, v_env_1685_);
lean_ctor_set(v___x_1721_, 1, v___x_1707_);
lean_ctor_set(v___x_1721_, 2, v___x_1708_);
lean_ctor_set(v___x_1721_, 3, v___x_1709_);
lean_ctor_set(v___x_1721_, 4, v___x_1686_);
lean_ctor_set(v___x_1721_, 5, v___x_1711_);
lean_ctor_set(v___x_1721_, 6, v___x_1714_);
lean_ctor_set(v___x_1721_, 7, v___x_1719_);
lean_ctor_set(v___x_1721_, 8, v___x_1720_);
lean_ctor_set(v___x_1721_, 9, v___x_1712_);
v___x_1722_ = lean_st_mk_ref(v___x_1721_);
v___x_1754_ = lean_st_ref_get(v___x_1693_);
v___x_1755_ = lean_st_ref_get(v___x_1722_);
v_env_1781_ = lean_ctor_get(v___x_1755_, 0);
lean_inc_ref(v_env_1781_);
lean_dec(v___x_1755_);
v___x_1782_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1781_);
lean_dec_ref(v_env_1781_);
v___x_1785_ = 512;
v___x_1786_ = lean_uint16_land(v___x_1705_, v___x_1785_);
v___x_1787_ = 0;
v___x_1788_ = lean_uint16_dec_eq(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
if (v___x_1695_ == 0)
{
v___y_1784_ = v___x_1695_;
goto v___jp_1783_;
}
else
{
v___y_1779_ = v___x_1695_;
v___y_1780_ = v___x_1782_;
goto v___jp_1778_;
}
}
else
{
v___y_1784_ = v_val_1689_;
goto v___jp_1783_;
}
v___jp_1723_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1738_ = l_Lean_maxRecDepth;
v___x_1739_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1679_, v___x_1738_);
lean_inc(v_currMacroScope_1731_);
lean_inc(v_openDecls_1727_);
v___x_1740_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1740_, 0, v_fileName_1724_);
lean_ctor_set(v___x_1740_, 1, v_fileMap_1725_);
lean_ctor_set(v___x_1740_, 2, v_opts_1679_);
lean_ctor_set(v___x_1740_, 3, v___x_1739_);
lean_ctor_set(v___x_1740_, 4, v_currNamespace_1726_);
lean_ctor_set(v___x_1740_, 5, v_openDecls_1727_);
lean_ctor_set(v___x_1740_, 6, v_initHeartbeats_1728_);
lean_ctor_set(v___x_1740_, 7, v_maxHeartbeats_1729_);
lean_ctor_set(v___x_1740_, 8, v_quotContext_1730_);
lean_ctor_set(v___x_1740_, 9, v_currMacroScope_1731_);
lean_ctor_set(v___x_1740_, 10, v_cancelTk_x3f_1732_);
lean_ctor_set(v___x_1740_, 11, v_inheritedTraceOptions_1733_);
lean_inc(v_ref_1735_);
v___x_1741_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v_currRecDepth_1734_);
lean_ctor_set(v___x_1741_, 2, v_ref_1735_);
lean_ctor_set_uint16(v___x_1741_, sizeof(void*)*3, v___x_1705_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*3 + 2, v_suppressElabErrors_1736_);
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*3 + 3, v_isRecordingDeps_1737_);
v___x_1742_ = l_Lean_Language_SnapshotTree_trace(v___x_1687_, v___x_1741_, v___x_1722_);
lean_dec_ref_known(v___x_1741_, 3);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1743_; lean_object* v_traceState_1744_; lean_object* v_traces_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec_ref_known(v___x_1742_, 1);
lean_dec_ref(v___x_1692_);
v___x_1743_ = lean_st_ref_get(v___x_1722_);
lean_dec(v___x_1722_);
v_traceState_1744_ = lean_ctor_get(v___x_1743_, 4);
lean_inc_ref(v_traceState_1744_);
lean_dec(v___x_1743_);
v_traces_1745_ = lean_ctor_get(v_traceState_1744_, 0);
lean_inc_ref(v_traces_1745_);
lean_dec_ref(v_traceState_1744_);
v___x_1746_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1699_);
lean_inc_ref(v_fileMap_1700_);
v___x_1747_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1700_, v_pos_1688_, v_fileName_1699_, v_val_1689_, v_traces_1745_, v___x_1746_);
lean_dec_ref(v_traces_1745_);
v___x_1748_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1749_, 0, v___x_1690_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
lean_ctor_set(v___x_1749_, 2, v___x_1691_);
lean_ctor_set(v___x_1749_, 3, v___x_1686_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*4, v_val_1689_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1712_);
v___x_1751_ = lean_task_pure(v___x_1750_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref_known(v___x_1742_, 1);
lean_dec(v___x_1722_);
lean_dec(v___x_1691_);
lean_dec_ref(v___x_1690_);
lean_dec_ref(v___x_1686_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1692_);
lean_ctor_set(v___x_1752_, 1, v___x_1712_);
v___x_1753_ = lean_task_pure(v___x_1752_);
return v___x_1753_;
}
}
v___jp_1756_:
{
lean_object* v___x_1758_; lean_object* v_env_1759_; lean_object* v_nextMacroScope_1760_; lean_object* v_ngen_1761_; lean_object* v_auxDeclNGen_1762_; lean_object* v_traceState_1763_; lean_object* v_recordedDeps_1764_; lean_object* v_messages_1765_; lean_object* v_infoState_1766_; lean_object* v_snapshotTasks_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1776_; 
v___x_1758_ = lean_st_ref_take(v___x_1722_);
v_env_1759_ = lean_ctor_get(v___x_1758_, 0);
v_nextMacroScope_1760_ = lean_ctor_get(v___x_1758_, 1);
v_ngen_1761_ = lean_ctor_get(v___x_1758_, 2);
v_auxDeclNGen_1762_ = lean_ctor_get(v___x_1758_, 3);
v_traceState_1763_ = lean_ctor_get(v___x_1758_, 4);
v_recordedDeps_1764_ = lean_ctor_get(v___x_1758_, 6);
v_messages_1765_ = lean_ctor_get(v___x_1758_, 7);
v_infoState_1766_ = lean_ctor_get(v___x_1758_, 8);
v_snapshotTasks_1767_ = lean_ctor_get(v___x_1758_, 9);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1758_, 5);
lean_dec(v_unused_1777_);
v___x_1769_ = v___x_1758_;
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_snapshotTasks_1767_);
lean_inc(v_infoState_1766_);
lean_inc(v_messages_1765_);
lean_inc(v_recordedDeps_1764_);
lean_inc(v_traceState_1763_);
lean_inc(v_auxDeclNGen_1762_);
lean_inc(v_ngen_1761_);
lean_inc(v_nextMacroScope_1760_);
lean_inc(v_env_1759_);
lean_dec(v___x_1758_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = l_Lean_Kernel_enableDiag(v_env_1759_, v___y_1757_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 5, v___x_1711_);
lean_ctor_set(v___x_1769_, 0, v___x_1771_);
v___x_1773_ = v___x_1769_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_nextMacroScope_1760_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_ngen_1761_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_auxDeclNGen_1762_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_traceState_1763_);
lean_ctor_set(v_reuseFailAlloc_1775_, 5, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1775_, 6, v_recordedDeps_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 7, v_messages_1765_);
lean_ctor_set(v_reuseFailAlloc_1775_, 8, v_infoState_1766_);
lean_ctor_set(v_reuseFailAlloc_1775_, 9, v_snapshotTasks_1767_);
v___x_1773_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_st_ref_put(v___x_1722_, v___x_1773_);
lean_inc(v___x_1681_);
lean_inc(v___x_1680_);
lean_inc_ref(v_fileMap_1700_);
lean_inc_ref(v_fileName_1699_);
v_fileName_1724_ = v_fileName_1699_;
v_fileMap_1725_ = v_fileMap_1700_;
v_currNamespace_1726_ = v___x_1680_;
v_openDecls_1727_ = v___x_1701_;
v_initHeartbeats_1728_ = v___x_1681_;
v_maxHeartbeats_1729_ = v___x_1702_;
v_quotContext_1730_ = v___x_1680_;
v_currMacroScope_1731_ = v___x_1703_;
v_cancelTk_x3f_1732_ = v___x_1694_;
v_inheritedTraceOptions_1733_ = v___x_1754_;
v_currRecDepth_1734_ = v___x_1681_;
v_ref_1735_ = v___x_1704_;
v_suppressElabErrors_1736_ = v_val_1689_;
v_isRecordingDeps_1737_ = v_val_1689_;
goto v___jp_1723_;
}
}
}
v___jp_1778_:
{
if (v___y_1780_ == 0)
{
v___y_1757_ = v___y_1779_;
goto v___jp_1756_;
}
else
{
lean_inc(v___x_1681_);
lean_inc(v___x_1680_);
lean_inc_ref(v_fileMap_1700_);
lean_inc_ref(v_fileName_1699_);
v_fileName_1724_ = v_fileName_1699_;
v_fileMap_1725_ = v_fileMap_1700_;
v_currNamespace_1726_ = v___x_1680_;
v_openDecls_1727_ = v___x_1701_;
v_initHeartbeats_1728_ = v___x_1681_;
v_maxHeartbeats_1729_ = v___x_1702_;
v_quotContext_1730_ = v___x_1680_;
v_currMacroScope_1731_ = v___x_1703_;
v_cancelTk_x3f_1732_ = v___x_1694_;
v_inheritedTraceOptions_1733_ = v___x_1754_;
v_currRecDepth_1734_ = v___x_1681_;
v_ref_1735_ = v___x_1704_;
v_suppressElabErrors_1736_ = v_val_1689_;
v_isRecordingDeps_1737_ = v_val_1689_;
goto v___jp_1723_;
}
}
v___jp_1783_:
{
if (v___x_1782_ == 0)
{
v___y_1779_ = v___y_1784_;
v___y_1780_ = v___x_1695_;
goto v___jp_1778_;
}
else
{
v___y_1757_ = v___y_1784_;
goto v___jp_1756_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1678_ = stack[0].m_obj;
lean_object* v_opts_1679_ = stack[1].m_obj;
lean_object* v___x_1680_ = stack[2].m_obj;
lean_object* v___x_1681_ = stack[3].m_obj;
lean_object* v___x_1682_ = stack[4].m_obj;
size_t v___x_1683_ = stack[5].m_num;
uint8_t v___x_1684_ = stack[6].m_num;
lean_object* v_env_1685_ = stack[7].m_obj;
lean_object* v___x_1686_ = stack[8].m_obj;
lean_object* v___x_1687_ = stack[9].m_obj;
lean_object* v_pos_1688_ = stack[10].m_obj;
uint8_t v_val_1689_ = stack[11].m_num;
lean_object* v___x_1690_ = stack[12].m_obj;
lean_object* v___x_1691_ = stack[13].m_obj;
lean_object* v___x_1692_ = stack[14].m_obj;
lean_object* v___x_1693_ = stack[15].m_obj;
lean_object* v___x_1694_ = stack[16].m_obj;
uint8_t v___x_1695_ = stack[17].m_num;
lean_object* v_x_1696_ = stack[18].m_obj;
lean_object* v_res_1789_;
v_res_1789_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1678_, v_opts_1679_, v___x_1680_, v___x_1681_, v___x_1682_, v___x_1683_, v___x_1684_, v_env_1685_, v___x_1686_, v___x_1687_, v_pos_1688_, v_val_1689_, v___x_1690_, v___x_1691_, v___x_1692_, v___x_1693_, v___x_1694_, v___x_1695_, v_x_1696_);
stack->m_obj
 = v_res_1789_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1790_ = _args[0];
lean_object* v_opts_1791_ = _args[1];
lean_object* v___x_1792_ = _args[2];
lean_object* v___x_1793_ = _args[3];
lean_object* v___x_1794_ = _args[4];
lean_object* v___x_1795_ = _args[5];
lean_object* v___x_1796_ = _args[6];
lean_object* v_env_1797_ = _args[7];
lean_object* v___x_1798_ = _args[8];
lean_object* v___x_1799_ = _args[9];
lean_object* v_pos_1800_ = _args[10];
lean_object* v_val_1801_ = _args[11];
lean_object* v___x_1802_ = _args[12];
lean_object* v___x_1803_ = _args[13];
lean_object* v___x_1804_ = _args[14];
lean_object* v___x_1805_ = _args[15];
lean_object* v___x_1806_ = _args[16];
lean_object* v___x_1807_ = _args[17];
lean_object* v_x_1808_ = _args[18];
lean_object* v___y_1809_ = _args[19];
_start:
{
size_t v___x_37226__boxed_1810_; uint8_t v___x_37227__boxed_1811_; uint8_t v_val_37230__boxed_1812_; uint8_t v___x_37236__boxed_1813_; lean_object* v_res_1814_; 
v___x_37226__boxed_1810_ = lean_unbox_usize(v___x_1795_);
lean_dec(v___x_1795_);
v___x_37227__boxed_1811_ = lean_unbox(v___x_1796_);
v_val_37230__boxed_1812_ = lean_unbox(v_val_1801_);
v___x_37236__boxed_1813_ = lean_unbox(v___x_1807_);
v_res_1814_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1790_, v_opts_1791_, v___x_1792_, v___x_1793_, v___x_1794_, v___x_37226__boxed_1810_, v___x_37227__boxed_1811_, v_env_1797_, v___x_1798_, v___x_1799_, v_pos_1800_, v_val_37230__boxed_1812_, v___x_1802_, v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v___x_37236__boxed_1813_, v_x_1808_);
lean_dec(v___x_1805_);
lean_dec(v_pos_1800_);
lean_dec(v___x_1794_);
lean_dec_ref(v_a_1790_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1815_, lean_object* v___x_1816_, lean_object* v_parserState_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v_toProcessingContext_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_toProcessingContext_1819_ = lean_ctor_get(v_a_1815_, 0);
v___x_1820_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1819_);
v___x_1821_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1819_, v___x_1816_, v_parserState_1817_, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1822_, lean_object* v___x_1823_, lean_object* v_parserState_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1822_, v___x_1823_, v_parserState_1824_, v_x_1825_);
lean_dec_ref(v_a_1822_);
return v_res_1826_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1828_, size_t v_i_1829_, size_t v_stop_1830_, lean_object* v_b_1831_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_eq(v_i_1829_, v_stop_1830_);
if (v___x_1833_ == 0)
{
lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; size_t v___x_1837_; size_t v___x_1838_; 
v___f_1834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1835_ = lean_array_uget_borrowed(v_as_1828_, v_i_1829_);
lean_inc(v___x_1835_);
v___x_1836_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1834_, v___x_1835_);
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1829_, v___x_1837_);
v_i_1829_ = v___x_1838_;
v_b_1831_ = v___x_1836_;
goto _start;
}
else
{
return v_b_1831_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1828_ = stack[0].m_obj;
size_t v_i_1829_ = stack[1].m_num;
size_t v_stop_1830_ = stack[2].m_num;
lean_object* v_b_1831_ = stack[3].m_obj;
lean_object* v_res_1840_;
v_res_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1828_, v_i_1829_, v_stop_1830_, v_b_1831_);
stack->m_obj
 = v_res_1840_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1841_, lean_object* v_i_1842_, lean_object* v_stop_1843_, lean_object* v_b_1844_, lean_object* v___y_1845_){
_start:
{
size_t v_i_boxed_1846_; size_t v_stop_boxed_1847_; lean_object* v_res_1848_; 
v_i_boxed_1846_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_stop_boxed_1847_ = lean_unbox_usize(v_stop_1843_);
lean_dec(v_stop_1843_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1841_, v_i_boxed_1846_, v_stop_boxed_1847_, v_b_1844_);
lean_dec_ref(v_as_1841_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1849_, lean_object* v_stx_1850_, lean_object* v_revCmds_1851_, lean_object* v_newParserState_1852_, lean_object* v_val_1853_, lean_object* v_sync_1854_, lean_object* v_val_1855_, lean_object* v_a_1856_, lean_object* v_oldNext_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v_sync_boxed_1859_; lean_object* v_res_1860_; 
v_sync_boxed_1859_ = lean_unbox(v_sync_1854_);
v_res_1860_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1849_, v_stx_1850_, v_revCmds_1851_, v_newParserState_1852_, v_val_1853_, v_sync_boxed_1859_, v_val_1855_, v_a_1856_, v_oldNext_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1860_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1861_, lean_object* v_stx_1862_, lean_object* v_revCmds_1863_, lean_object* v_newParserState_1864_, lean_object* v_val_1865_, uint8_t v_sync_1866_, lean_object* v_val_1867_, lean_object* v_a_1868_, lean_object* v_oldResult_1869_){
_start:
{
lean_object* v_task_1871_; lean_object* v___x_1872_; lean_object* v___f_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; 
v_task_1871_ = lean_ctor_get(v_val_1861_, 3);
lean_inc_ref(v_task_1871_);
lean_dec_ref(v_val_1861_);
v___x_1872_ = lean_box(v_sync_1866_);
lean_inc_ref(v_a_1868_);
v___f_1873_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1873_, 0, v_oldResult_1869_);
lean_closure_set(v___f_1873_, 1, v_stx_1862_);
lean_closure_set(v___f_1873_, 2, v_revCmds_1863_);
lean_closure_set(v___f_1873_, 3, v_newParserState_1864_);
lean_closure_set(v___f_1873_, 4, v_val_1865_);
lean_closure_set(v___f_1873_, 5, v___x_1872_);
lean_closure_set(v___f_1873_, 6, v_val_1867_);
lean_closure_set(v___f_1873_, 7, v_a_1868_);
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = 1;
v___x_1876_ = l_BaseIO_chainTask___redArg(v_task_1871_, v___f_1873_, v___x_1874_, v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1861_ = stack[0].m_obj;
lean_object* v_stx_1862_ = stack[1].m_obj;
lean_object* v_revCmds_1863_ = stack[2].m_obj;
lean_object* v_newParserState_1864_ = stack[3].m_obj;
lean_object* v_val_1865_ = stack[4].m_obj;
uint8_t v_sync_1866_ = stack[5].m_num;
lean_object* v_val_1867_ = stack[6].m_obj;
lean_object* v_a_1868_ = stack[7].m_obj;
lean_object* v_oldResult_1869_ = stack[8].m_obj;
lean_object* v_res_1877_;
v_res_1877_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1861_, v_stx_1862_, v_revCmds_1863_, v_newParserState_1864_, v_val_1865_, v_sync_1866_, v_val_1867_, v_a_1868_, v_oldResult_1869_);
stack->m_obj
 = v_res_1877_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1878_, lean_object* v_stx_1879_, lean_object* v_revCmds_1880_, lean_object* v_newParserState_1881_, lean_object* v_val_1882_, lean_object* v_sync_1883_, lean_object* v_val_1884_, lean_object* v_a_1885_, lean_object* v_oldResult_1886_, lean_object* v___y_1887_){
_start:
{
uint8_t v_sync_boxed_1888_; lean_object* v_res_1889_; 
v_sync_boxed_1888_ = lean_unbox(v_sync_1883_);
v_res_1889_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1878_, v_stx_1879_, v_revCmds_1880_, v_newParserState_1881_, v_val_1882_, v_sync_boxed_1888_, v_val_1884_, v_a_1885_, v_oldResult_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1889_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1898_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1899_ = l_Lean_Name_append(v___x_1898_, v___x_1897_);
return v___x_1899_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1903_, lean_object* v_val_1904_, lean_object* v_fst_1905_, lean_object* v_revCmds_1906_, lean_object* v_fst_1907_, uint8_t v_val_1908_, lean_object* v_a_1909_, lean_object* v_snd_1910_, lean_object* v___x_1911_, uint8_t v___x_1912_, lean_object* v_fst_1913_, lean_object* v_val_1914_, lean_object* v_val_1915_, lean_object* v___x_1916_, lean_object* v___f_1917_, lean_object* v___f_1918_, lean_object* v___f_1919_, lean_object* v_pos_1920_, lean_object* v_cmdState_1921_, lean_object* v_val_1922_, lean_object* v___x_1923_, lean_object* v_opts_1924_, lean_object* v___x_1925_, lean_object* v_snd_1926_, lean_object* v_prom_1927_, lean_object* v_old_x3f_1928_, lean_object* v_parseCancelTk_1929_, lean_object* v_next_x3f_1930_){
_start:
{
lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v_snapshotTasks_1938_; lean_object* v_traceTask_1939_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1961_; size_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v_env_1977_; lean_object* v_messages_1978_; lean_object* v_scopes_1979_; lean_object* v_infoState_1980_; lean_object* v_traceState_1981_; lean_object* v_snapshotTasks_1982_; lean_object* v_codeQualityEntryTasks_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v_reportedCmdState_1990_; lean_object* v___y_2025_; size_t v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v_reportedCmdState_2047_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; size_t v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2105_; 
if (lean_obj_tag(v_next_x3f_1930_) == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v_parseCancelTk_1929_);
v___x_2158_ = lean_box(0);
v___y_2105_ = v___x_2158_;
goto v___jp_2104_;
}
else
{
lean_object* v_toProcessingContext_2159_; lean_object* v_val_2160_; lean_object* v_pos_2161_; lean_object* v_endPos_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_toProcessingContext_2159_ = lean_ctor_get(v_a_1909_, 0);
v_val_2160_ = lean_ctor_get(v_next_x3f_1930_, 0);
v_pos_2161_ = lean_ctor_get(v_fst_1907_, 0);
v_endPos_2162_ = lean_ctor_get(v_toProcessingContext_2159_, 3);
v___x_2163_ = lean_box(0);
lean_inc(v_endPos_2162_);
lean_inc(v_pos_2161_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_pos_2161_);
lean_ctor_set(v___x_2164_, 1, v_endPos_2162_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_parseCancelTk_1929_);
v___x_2167_ = l_IO_Promise_result_x21___redArg(v_val_2160_);
v___x_2168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2163_);
lean_ctor_set(v___x_2168_, 1, v___x_2165_);
lean_ctor_set(v___x_2168_, 2, v___x_2166_);
lean_ctor_set(v___x_2168_, 3, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
v___y_2105_ = v___x_2169_;
goto v___jp_2104_;
}
v___jp_1932_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1940_, 0, v___y_1936_);
lean_ctor_set(v___x_1940_, 1, v___x_1903_);
lean_ctor_set(v___x_1940_, 2, v___y_1934_);
lean_ctor_set(v___x_1940_, 3, v_traceTask_1939_);
v___x_1941_ = lean_array_push(v_snapshotTasks_1938_, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___y_1933_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_io_promise_resolve(v___x_1942_, v_val_1904_);
if (lean_obj_tag(v_next_x3f_1930_) == 1)
{
lean_object* v_val_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_val_1944_ = lean_ctor_get(v_next_x3f_1930_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v_next_x3f_1930_, 1);
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_fst_1905_);
lean_ctor_set(v___x_1946_, 1, v_revCmds_1906_);
v___x_1947_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1945_, v_fst_1907_, v___y_1937_, v_val_1944_, v_val_1908_, v___y_1935_, v___x_1946_, v_a_1909_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; 
lean_dec_ref(v___y_1937_);
lean_dec_ref(v___y_1935_);
lean_dec(v_next_x3f_1930_);
lean_dec_ref(v_fst_1907_);
lean_dec(v_revCmds_1906_);
lean_dec(v_fst_1905_);
v___x_1948_ = lean_box(0);
return v___x_1948_;
}
}
v___jp_1949_:
{
lean_object* v_snapshotTasks_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_snapshotTasks_1956_ = lean_ctor_get(v___y_1955_, 10);
lean_inc_ref(v_snapshotTasks_1956_);
v___x_1957_ = lean_mk_empty_array_with_capacity(v___y_1950_);
lean_dec(v___y_1950_);
lean_inc_ref(v___y_1951_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___y_1951_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = lean_task_pure(v___x_1958_);
v___y_1933_ = v___y_1951_;
v___y_1934_ = v___y_1952_;
v___y_1935_ = v___y_1954_;
v___y_1936_ = v___y_1953_;
v___y_1937_ = v___y_1955_;
v_snapshotTasks_1938_ = v_snapshotTasks_1956_;
v_traceTask_1939_ = v___x_1959_;
goto v___jp_1932_;
}
v___jp_1960_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v_opts_2000_; uint8_t v_hasTrace_2001_; 
v___x_1991_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1978_);
v___x_1992_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1992_, 0, v___y_1975_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
lean_ctor_set(v___x_1992_, 2, v___y_1987_);
lean_ctor_set(v___x_1992_, 3, v_traceState_1981_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*4, v_val_1908_);
v___x_1993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v_reportedCmdState_1990_);
lean_ctor_set(v___x_1993_, 2, v_codeQualityEntryTasks_1983_);
v___x_1994_ = lean_io_promise_resolve(v___x_1993_, v_val_1915_);
v___x_1995_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1980_);
lean_inc(v___y_1984_);
v___x_1996_ = l_BaseIO_chainTask___redArg(v___x_1995_, v___y_1972_, v___y_1984_, v___x_1912_);
v___x_1997_ = l_Lean_inheritedTraceOptions;
v___x_1998_ = lean_st_ref_get(v___x_1997_);
v___x_1999_ = l_List_head_x21___redArg(v___x_1916_, v_scopes_1979_);
lean_dec(v_scopes_1979_);
lean_dec_ref(v___x_1916_);
v_opts_2000_ = lean_ctor_get(v___x_1999_, 1);
lean_inc_ref(v_opts_2000_);
lean_dec(v___x_1999_);
v_hasTrace_2001_ = lean_ctor_get_uint8(v_opts_2000_, sizeof(void*)*1);
if (v_hasTrace_2001_ == 0)
{
lean_dec_ref(v_opts_2000_);
lean_dec(v___x_1998_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v_snapshotTasks_1982_);
lean_dec_ref(v_env_1977_);
lean_dec(v___y_1971_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1961_);
lean_dec(v_pos_1920_);
lean_dec_ref(v___f_1919_);
lean_dec_ref(v___f_1918_);
lean_dec_ref(v___f_1917_);
lean_dec(v___x_1911_);
v___y_1950_ = v___y_1984_;
v___y_1951_ = v___y_1970_;
v___y_1952_ = v___y_1986_;
v___y_1953_ = v___y_1973_;
v___y_1954_ = v___y_1974_;
v___y_1955_ = v___y_1976_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1998_, v_opts_2000_, v___x_2002_);
lean_dec(v___x_1998_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v_opts_2000_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v_snapshotTasks_1982_);
lean_dec_ref(v_env_1977_);
lean_dec(v___y_1971_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1961_);
lean_dec(v_pos_1920_);
lean_dec_ref(v___f_1919_);
lean_dec_ref(v___f_1918_);
lean_dec_ref(v___f_1917_);
lean_dec(v___x_1911_);
v___y_1950_ = v___y_1984_;
v___y_1951_ = v___y_1970_;
v___y_1952_ = v___y_1986_;
v___y_1953_ = v___y_1973_;
v___y_1954_ = v___y_1974_;
v___y_1955_ = v___y_1976_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_inc_n(v___y_1984_, 3);
v___x_2004_ = lean_task_map(v___f_1917_, v___y_1989_, v___y_1984_, v___x_1912_);
lean_inc_n(v___y_1986_, 3);
lean_inc_n(v___y_1971_, 2);
lean_inc_n(v___y_1969_, 2);
v___x_2005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2005_, 0, v___y_1969_);
lean_ctor_set(v___x_2005_, 1, v___y_1971_);
lean_ctor_set(v___x_2005_, 2, v___y_1986_);
lean_ctor_set(v___x_2005_, 3, v___x_2004_);
v___x_2006_ = lean_task_map(v___f_1918_, v___y_1988_, v___y_1984_, v___x_1912_);
v___x_2007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2007_, 0, v___y_1969_);
lean_ctor_set(v___x_2007_, 1, v___y_1971_);
lean_ctor_set(v___x_2007_, 2, v___y_1986_);
lean_ctor_set(v___x_2007_, 3, v___x_2006_);
v___x_2008_ = lean_task_map(v___f_1919_, v___y_1985_, v___y_1984_, v___x_1912_);
v___x_2009_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2009_, 0, v___y_1969_);
lean_ctor_set(v___x_2009_, 1, v___y_1971_);
lean_ctor_set(v___x_2009_, 2, v___y_1986_);
lean_ctor_set(v___x_2009_, 3, v___x_2008_);
v___x_2010_ = lean_unsigned_to_nat(3u);
v___x_2011_ = lean_mk_empty_array_with_capacity(v___x_2010_);
v___x_2012_ = lean_array_push(v___x_2011_, v___x_2005_);
v___x_2013_ = lean_array_push(v___x_2012_, v___x_2007_);
v___x_2014_ = lean_array_push(v___x_2013_, v___x_2009_);
v___x_2015_ = l_Array_append___redArg(v___x_2014_, v_snapshotTasks_1982_);
lean_inc_ref(v___y_1970_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___y_1970_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_box_usize(v___y_1962_);
v___x_2018_ = lean_box(v___x_1912_);
v___x_2019_ = lean_box(v_val_1908_);
v___x_2020_ = lean_box(v___x_2003_);
lean_inc_ref(v___x_2016_);
lean_inc_ref(v___y_1965_);
lean_inc_ref(v_a_1909_);
v___f_2021_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2021_, 0, v_a_1909_);
lean_closure_set(v___f_2021_, 1, v_opts_2000_);
lean_closure_set(v___f_2021_, 2, v___x_1911_);
lean_closure_set(v___f_2021_, 3, v___y_1961_);
lean_closure_set(v___f_2021_, 4, v___y_1967_);
lean_closure_set(v___f_2021_, 5, v___x_2017_);
lean_closure_set(v___f_2021_, 6, v___x_2018_);
lean_closure_set(v___f_2021_, 7, v_env_1977_);
lean_closure_set(v___f_2021_, 8, v___y_1965_);
lean_closure_set(v___f_2021_, 9, v___x_2016_);
lean_closure_set(v___f_2021_, 10, v_pos_1920_);
lean_closure_set(v___f_2021_, 11, v___x_2019_);
lean_closure_set(v___f_2021_, 12, v___y_1966_);
lean_closure_set(v___f_2021_, 13, v___y_1963_);
lean_closure_set(v___f_2021_, 14, v___y_1964_);
lean_closure_set(v___f_2021_, 15, v___x_1997_);
lean_closure_set(v___f_2021_, 16, v___y_1968_);
lean_closure_set(v___f_2021_, 17, v___x_2020_);
v___x_2022_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2016_);
v___x_2023_ = lean_io_bind_task(v___x_2022_, v___f_2021_, v___y_1984_, v_val_1908_);
v___y_1933_ = v___y_1970_;
v___y_1934_ = v___y_1986_;
v___y_1935_ = v___y_1974_;
v___y_1936_ = v___y_1973_;
v___y_1937_ = v___y_1976_;
v_snapshotTasks_1938_ = v_snapshotTasks_1982_;
v_traceTask_1939_ = v___x_2023_;
goto v___jp_1932_;
}
}
}
v___jp_2024_:
{
lean_object* v_env_2048_; lean_object* v_messages_2049_; lean_object* v_scopes_2050_; lean_object* v_infoState_2051_; lean_object* v_traceState_2052_; lean_object* v_snapshotTasks_2053_; lean_object* v_codeQualityEntryTasks_2054_; 
v_env_2048_ = lean_ctor_get(v___y_2040_, 0);
lean_inc_ref(v_env_2048_);
v_messages_2049_ = lean_ctor_get(v___y_2040_, 1);
lean_inc_ref(v_messages_2049_);
v_scopes_2050_ = lean_ctor_get(v___y_2040_, 2);
lean_inc(v_scopes_2050_);
v_infoState_2051_ = lean_ctor_get(v___y_2040_, 8);
lean_inc_ref(v_infoState_2051_);
v_traceState_2052_ = lean_ctor_get(v___y_2040_, 9);
lean_inc_ref(v_traceState_2052_);
v_snapshotTasks_2053_ = lean_ctor_get(v___y_2040_, 10);
lean_inc_ref(v_snapshotTasks_2053_);
v_codeQualityEntryTasks_2054_ = lean_ctor_get(v___y_2040_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2054_);
v___y_1961_ = v___y_2025_;
v___y_1962_ = v___y_2026_;
v___y_1963_ = v___y_2027_;
v___y_1964_ = v___y_2029_;
v___y_1965_ = v___y_2028_;
v___y_1966_ = v___y_2031_;
v___y_1967_ = v___y_2030_;
v___y_1968_ = v___y_2032_;
v___y_1969_ = v___y_2033_;
v___y_1970_ = v___y_2034_;
v___y_1971_ = v___y_2035_;
v___y_1972_ = v___y_2036_;
v___y_1973_ = v___y_2037_;
v___y_1974_ = v___y_2038_;
v___y_1975_ = v___y_2039_;
v___y_1976_ = v___y_2040_;
v_env_1977_ = v_env_2048_;
v_messages_1978_ = v_messages_2049_;
v_scopes_1979_ = v_scopes_2050_;
v_infoState_1980_ = v_infoState_2051_;
v_traceState_1981_ = v_traceState_2052_;
v_snapshotTasks_1982_ = v_snapshotTasks_2053_;
v_codeQualityEntryTasks_1983_ = v_codeQualityEntryTasks_2054_;
v___y_1984_ = v___y_2041_;
v___y_1985_ = v___y_2042_;
v___y_1986_ = v___y_2043_;
v___y_1987_ = v___y_2044_;
v___y_1988_ = v___y_2045_;
v___y_1989_ = v___y_2046_;
v_reportedCmdState_1990_ = v_reportedCmdState_2047_;
goto v___jp_1960_;
}
v___jp_2055_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___f_2076_; uint8_t v___x_2077_; 
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___y_2071_);
lean_ctor_set(v___x_2072_, 1, v_val_1914_);
lean_inc_ref(v___y_2060_);
lean_inc_n(v_pos_1920_, 2);
lean_inc(v_revCmds_1906_);
lean_inc(v_fst_1905_);
v___x_2073_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1905_, v_revCmds_1906_, v_cmdState_1921_, v_pos_1920_, v___x_2072_, v___y_2060_, v_a_1909_);
v___x_2074_ = lean_box(v_val_1908_);
v___x_2075_ = lean_box(v___x_1912_);
lean_inc_ref(v_a_1909_);
lean_inc(v___y_2057_);
lean_inc_ref(v___x_1916_);
lean_inc_ref(v___x_2073_);
lean_inc_ref(v___y_2063_);
lean_inc_ref(v___y_2065_);
v___f_2076_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2076_, 0, v___y_2065_);
lean_closure_set(v___f_2076_, 1, v___y_2063_);
lean_closure_set(v___f_2076_, 2, v___x_2074_);
lean_closure_set(v___f_2076_, 3, v_val_1922_);
lean_closure_set(v___f_2076_, 4, v___x_2073_);
lean_closure_set(v___f_2076_, 5, v___x_1916_);
lean_closure_set(v___f_2076_, 6, v___y_2057_);
lean_closure_set(v___f_2076_, 7, v___x_2075_);
lean_closure_set(v___f_2076_, 8, v_a_1909_);
lean_closure_set(v___f_2076_, 9, v_pos_1920_);
lean_closure_set(v___f_2076_, 10, v___x_1923_);
v___x_2077_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1924_, v___x_1925_);
if (v___x_2077_ == 0)
{
lean_inc_ref(v___x_2073_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2062_);
lean_inc(v___y_2061_);
lean_inc(v___y_2057_);
v___y_2025_ = v___y_2057_;
v___y_2026_ = v___y_2059_;
v___y_2027_ = v___y_2061_;
v___y_2028_ = v___y_2063_;
v___y_2029_ = v___y_2062_;
v___y_2030_ = v___y_2064_;
v___y_2031_ = v___y_2065_;
v___y_2032_ = v___y_2067_;
v___y_2033_ = v___y_2058_;
v___y_2034_ = v___y_2062_;
v___y_2035_ = v___y_2056_;
v___y_2036_ = v___f_2076_;
v___y_2037_ = v___y_2068_;
v___y_2038_ = v___y_2060_;
v___y_2039_ = v___y_2065_;
v___y_2040_ = v___x_2073_;
v___y_2041_ = v___y_2057_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2061_;
v___y_2045_ = v___y_2070_;
v___y_2046_ = v___y_2066_;
v_reportedCmdState_2047_ = v___x_2073_;
goto v___jp_2024_;
}
else
{
uint8_t v___x_2078_; 
lean_inc(v_fst_1905_);
v___x_2078_ = l_Lean_Parser_isTerminalCommand(v_fst_1905_);
if (v___x_2078_ == 0)
{
if (v___x_2077_ == 0)
{
lean_inc_ref(v___x_2073_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2062_);
lean_inc(v___y_2061_);
lean_inc(v___y_2057_);
v___y_2025_ = v___y_2057_;
v___y_2026_ = v___y_2059_;
v___y_2027_ = v___y_2061_;
v___y_2028_ = v___y_2063_;
v___y_2029_ = v___y_2062_;
v___y_2030_ = v___y_2064_;
v___y_2031_ = v___y_2065_;
v___y_2032_ = v___y_2067_;
v___y_2033_ = v___y_2058_;
v___y_2034_ = v___y_2062_;
v___y_2035_ = v___y_2056_;
v___y_2036_ = v___f_2076_;
v___y_2037_ = v___y_2068_;
v___y_2038_ = v___y_2060_;
v___y_2039_ = v___y_2065_;
v___y_2040_ = v___x_2073_;
v___y_2041_ = v___y_2057_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2061_;
v___y_2045_ = v___y_2070_;
v___y_2046_ = v___y_2066_;
v_reportedCmdState_2047_ = v___x_2073_;
goto v___jp_2024_;
}
else
{
lean_object* v_env_2079_; lean_object* v_messages_2080_; lean_object* v_scopes_2081_; lean_object* v_infoState_2082_; lean_object* v_traceState_2083_; lean_object* v_snapshotTasks_2084_; lean_object* v_codeQualityEntryTasks_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_env_2079_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_ref_n(v_env_2079_, 2);
v_messages_2080_ = lean_ctor_get(v___x_2073_, 1);
lean_inc_ref(v_messages_2080_);
v_scopes_2081_ = lean_ctor_get(v___x_2073_, 2);
lean_inc(v_scopes_2081_);
v_infoState_2082_ = lean_ctor_get(v___x_2073_, 8);
lean_inc_ref(v_infoState_2082_);
v_traceState_2083_ = lean_ctor_get(v___x_2073_, 9);
lean_inc_ref(v_traceState_2083_);
v_snapshotTasks_2084_ = lean_ctor_get(v___x_2073_, 10);
lean_inc_ref(v_snapshotTasks_2084_);
v_codeQualityEntryTasks_2085_ = lean_ctor_get(v___x_2073_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2085_);
v___x_2086_ = lean_mk_empty_array_with_capacity(v___y_2064_);
lean_inc_ref(v___x_2086_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_inc_n(v___y_2057_, 4);
v___x_2088_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
lean_ctor_set(v___x_2088_, 2, v___y_2057_);
lean_ctor_set(v___x_2088_, 3, v___y_2057_);
lean_ctor_set_usize(v___x_2088_, 4, v___y_2059_);
v___x_2089_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2088_, 2);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2088_);
lean_ctor_set(v___x_2090_, 2, v___x_2089_);
v___x_2091_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2092_ = l_Lean_Options_empty;
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_mk_empty_array_with_capacity(v___y_2057_);
lean_inc_ref_n(v___x_2094_, 3);
lean_inc_n(v___x_1911_, 2);
v___x_2095_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2095_, 0, v___x_2091_);
lean_ctor_set(v___x_2095_, 1, v___x_2092_);
lean_ctor_set(v___x_2095_, 2, v___x_1911_);
lean_ctor_set(v___x_2095_, 3, v___x_2093_);
lean_ctor_set(v___x_2095_, 4, v___x_2093_);
lean_ctor_set(v___x_2095_, 5, v___x_2094_);
lean_ctor_set(v___x_2095_, 6, v___x_2094_);
lean_ctor_set(v___x_2095_, 7, v___x_2093_);
lean_ctor_set(v___x_2095_, 8, v___x_2093_);
lean_ctor_set(v___x_2095_, 9, v___x_2093_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*10, v_val_1908_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*10 + 1, v_val_1908_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*10 + 2, v_val_1908_);
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___x_2093_);
v___x_2097_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2098_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2099_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1911_);
v___x_2100_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2101_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
lean_ctor_set(v___x_2101_, 2, v___x_2088_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*3, v___x_1912_);
v___x_2102_ = lean_box(0);
lean_inc_ref(v___y_2063_);
v___x_2103_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2103_, 0, v_env_2079_);
lean_ctor_set(v___x_2103_, 1, v___x_2090_);
lean_ctor_set(v___x_2103_, 2, v___x_2096_);
lean_ctor_set(v___x_2103_, 3, v___x_2089_);
lean_ctor_set(v___x_2103_, 4, v___x_2097_);
lean_ctor_set(v___x_2103_, 5, v___y_2057_);
lean_ctor_set(v___x_2103_, 6, v___x_2098_);
lean_ctor_set(v___x_2103_, 7, v___x_2099_);
lean_ctor_set(v___x_2103_, 8, v___x_2101_);
lean_ctor_set(v___x_2103_, 9, v___y_2063_);
lean_ctor_set(v___x_2103_, 10, v___x_2094_);
lean_ctor_set(v___x_2103_, 11, v___x_2102_);
lean_ctor_set(v___x_2103_, 12, v___x_2094_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2062_);
lean_inc(v___y_2061_);
v___y_1961_ = v___y_2057_;
v___y_1962_ = v___y_2059_;
v___y_1963_ = v___y_2061_;
v___y_1964_ = v___y_2062_;
v___y_1965_ = v___y_2063_;
v___y_1966_ = v___y_2065_;
v___y_1967_ = v___y_2064_;
v___y_1968_ = v___y_2067_;
v___y_1969_ = v___y_2058_;
v___y_1970_ = v___y_2062_;
v___y_1971_ = v___y_2056_;
v___y_1972_ = v___f_2076_;
v___y_1973_ = v___y_2068_;
v___y_1974_ = v___y_2060_;
v___y_1975_ = v___y_2065_;
v___y_1976_ = v___x_2073_;
v_env_1977_ = v_env_2079_;
v_messages_1978_ = v_messages_2080_;
v_scopes_1979_ = v_scopes_2081_;
v_infoState_1980_ = v_infoState_2082_;
v_traceState_1981_ = v_traceState_2083_;
v_snapshotTasks_1982_ = v_snapshotTasks_2084_;
v_codeQualityEntryTasks_1983_ = v_codeQualityEntryTasks_2085_;
v___y_1984_ = v___y_2057_;
v___y_1985_ = v___y_2069_;
v___y_1986_ = v___y_2067_;
v___y_1987_ = v___y_2061_;
v___y_1988_ = v___y_2070_;
v___y_1989_ = v___y_2066_;
v_reportedCmdState_1990_ = v___x_2103_;
goto v___jp_1960_;
}
}
else
{
lean_inc_ref(v___x_2073_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2062_);
lean_inc(v___y_2061_);
lean_inc(v___y_2057_);
v___y_2025_ = v___y_2057_;
v___y_2026_ = v___y_2059_;
v___y_2027_ = v___y_2061_;
v___y_2028_ = v___y_2063_;
v___y_2029_ = v___y_2062_;
v___y_2030_ = v___y_2064_;
v___y_2031_ = v___y_2065_;
v___y_2032_ = v___y_2067_;
v___y_2033_ = v___y_2058_;
v___y_2034_ = v___y_2062_;
v___y_2035_ = v___y_2056_;
v___y_2036_ = v___f_2076_;
v___y_2037_ = v___y_2068_;
v___y_2038_ = v___y_2060_;
v___y_2039_ = v___y_2065_;
v___y_2040_ = v___x_2073_;
v___y_2041_ = v___y_2057_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2061_;
v___y_2045_ = v___y_2070_;
v___y_2046_ = v___y_2066_;
v_reportedCmdState_2047_ = v___x_2073_;
goto v___jp_2024_;
}
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2106_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1910_);
v___x_2107_ = l_IO_CancelToken_new();
v___x_2108_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1911_);
v___x_2109_ = l_Lean_Name_str___override(v___x_1911_, v___x_2108_);
v___x_2110_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2111_ = l_Lean_Name_str___override(v___x_2109_, v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2113_ = l_Lean_Name_str___override(v___x_2111_, v___x_2112_);
v___x_2114_ = l_Lean_Name_str___override(v___x_2113_, v___x_2110_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = l_Lean_Name_num___override(v___x_2114_, v___x_2115_);
v___x_2117_ = l_Lean_Name_str___override(v___x_2116_, v___x_2110_);
v___x_2118_ = l_Lean_Name_str___override(v___x_2117_, v___x_2112_);
v___x_2119_ = l_Lean_Name_str___override(v___x_2118_, v___x_2110_);
v___x_2120_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2121_ = l_Lean_Name_str___override(v___x_2119_, v___x_2120_);
v___x_2122_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2123_ = l_Lean_Name_str___override(v___x_2121_, v___x_2122_);
v___x_2124_ = l_Lean_Name_toString(v___x_2123_, v___x_1912_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_unsigned_to_nat(32u);
v___x_2127_ = ((size_t)5ULL);
v___x_2128_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2124_, 2);
v___x_2129_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2129_, 0, v___x_2124_);
lean_ctor_set(v___x_2129_, 1, v___x_2106_);
lean_ctor_set(v___x_2129_, 2, v___x_2125_);
lean_ctor_set(v___x_2129_, 3, v___x_2128_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*4, v_val_1908_);
v___x_2130_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2131_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2131_, 0, v___x_2124_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
lean_ctor_set(v___x_2131_, 2, v___x_2125_);
lean_ctor_set(v___x_2131_, 3, v___x_2128_);
lean_ctor_set_uint8(v___x_2131_, sizeof(void*)*4, v_val_1908_);
lean_inc(v_fst_1913_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_fst_1913_);
v___x_2133_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2132_);
lean_inc_ref(v___x_2107_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2107_);
v___x_2135_ = l_IO_Promise_result_x21___redArg(v_val_1914_);
lean_inc_ref(v___x_2135_);
lean_inc(v___x_2133_);
lean_inc_ref_n(v___x_2132_, 3);
v___x_2136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2132_);
lean_ctor_set(v___x_2136_, 1, v___x_2133_);
lean_ctor_set(v___x_2136_, 2, v___x_2134_);
lean_ctor_set(v___x_2136_, 3, v___x_2135_);
v___x_2137_ = l_IO_Promise_result_x21___redArg(v_val_1915_);
lean_inc_ref(v___x_2137_);
lean_inc_n(v___x_1903_, 3);
v___x_2138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2132_);
lean_ctor_set(v___x_2138_, 1, v___x_1903_);
lean_ctor_set(v___x_2138_, 2, v___x_2125_);
lean_ctor_set(v___x_2138_, 3, v___x_2137_);
v___x_2139_ = l_IO_Promise_result_x21___redArg(v_val_1922_);
lean_inc_ref(v___x_2139_);
v___x_2140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2132_);
lean_ctor_set(v___x_2140_, 1, v___x_1903_);
lean_ctor_set(v___x_2140_, 2, v___x_2125_);
lean_ctor_set(v___x_2140_, 3, v___x_2139_);
v___x_2141_ = l_IO_Promise_result_x21___redArg(v_val_1904_);
v___x_2142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2125_);
lean_ctor_set(v___x_2142_, 1, v___x_1903_);
lean_ctor_set(v___x_2142_, 2, v___x_2125_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
lean_inc_ref(v___x_2131_);
v___x_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2131_);
lean_ctor_set(v___x_2143_, 1, v___x_2136_);
lean_ctor_set(v___x_2143_, 2, v___x_2138_);
lean_ctor_set(v___x_2143_, 3, v___x_2140_);
lean_ctor_set(v___x_2143_, 4, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2129_);
lean_ctor_set(v___x_2144_, 1, v_fst_1913_);
lean_ctor_set(v___x_2144_, 2, v_snd_1926_);
lean_ctor_set(v___x_2144_, 3, v___x_2143_);
lean_ctor_set(v___x_2144_, 4, v___y_2105_);
v___x_2145_ = lean_io_promise_resolve(v___x_2144_, v_prom_1927_);
if (lean_obj_tag(v_old_x3f_1928_) == 0)
{
v___y_2056_ = v___x_2133_;
v___y_2057_ = v___x_2115_;
v___y_2058_ = v___x_2132_;
v___y_2059_ = v___x_2127_;
v___y_2060_ = v___x_2107_;
v___y_2061_ = v___x_2125_;
v___y_2062_ = v___x_2131_;
v___y_2063_ = v___x_2128_;
v___y_2064_ = v___x_2126_;
v___y_2065_ = v___x_2124_;
v___y_2066_ = v___x_2135_;
v___y_2067_ = v___x_2125_;
v___y_2068_ = v___x_2125_;
v___y_2069_ = v___x_2139_;
v___y_2070_ = v___x_2137_;
v___y_2071_ = v___x_2125_;
goto v___jp_2055_;
}
else
{
lean_object* v_val_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2157_; 
v_val_2146_ = lean_ctor_get(v_old_x3f_1928_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_old_x3f_1928_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2148_ = v_old_x3f_1928_;
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_val_2146_);
lean_dec(v_old_x3f_1928_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_elabSnap_2150_; lean_object* v_stx_2151_; lean_object* v_elabSnap_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v_elabSnap_2150_ = lean_ctor_get(v_val_2146_, 3);
lean_inc_ref(v_elabSnap_2150_);
v_stx_2151_ = lean_ctor_get(v_val_2146_, 1);
lean_inc(v_stx_2151_);
lean_dec(v_val_2146_);
v_elabSnap_2152_ = lean_ctor_get(v_elabSnap_2150_, 1);
lean_inc_ref(v_elabSnap_2152_);
lean_dec_ref(v_elabSnap_2150_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_stx_2151_);
lean_ctor_set(v___x_2153_, 1, v_elabSnap_2152_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2153_);
v___x_2155_ = v___x_2148_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
v___y_2056_ = v___x_2133_;
v___y_2057_ = v___x_2115_;
v___y_2058_ = v___x_2132_;
v___y_2059_ = v___x_2127_;
v___y_2060_ = v___x_2107_;
v___y_2061_ = v___x_2125_;
v___y_2062_ = v___x_2131_;
v___y_2063_ = v___x_2128_;
v___y_2064_ = v___x_2126_;
v___y_2065_ = v___x_2124_;
v___y_2066_ = v___x_2135_;
v___y_2067_ = v___x_2125_;
v___y_2068_ = v___x_2125_;
v___y_2069_ = v___x_2139_;
v___y_2070_ = v___x_2137_;
v___y_2071_ = v___x_2155_;
goto v___jp_2055_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1903_ = stack[0].m_obj;
lean_object* v_val_1904_ = stack[1].m_obj;
lean_object* v_fst_1905_ = stack[2].m_obj;
lean_object* v_revCmds_1906_ = stack[3].m_obj;
lean_object* v_fst_1907_ = stack[4].m_obj;
uint8_t v_val_1908_ = stack[5].m_num;
lean_object* v_a_1909_ = stack[6].m_obj;
lean_object* v_snd_1910_ = stack[7].m_obj;
lean_object* v___x_1911_ = stack[8].m_obj;
uint8_t v___x_1912_ = stack[9].m_num;
lean_object* v_fst_1913_ = stack[10].m_obj;
lean_object* v_val_1914_ = stack[11].m_obj;
lean_object* v_val_1915_ = stack[12].m_obj;
lean_object* v___x_1916_ = stack[13].m_obj;
lean_object* v___f_1917_ = stack[14].m_obj;
lean_object* v___f_1918_ = stack[15].m_obj;
lean_object* v___f_1919_ = stack[16].m_obj;
lean_object* v_pos_1920_ = stack[17].m_obj;
lean_object* v_cmdState_1921_ = stack[18].m_obj;
lean_object* v_val_1922_ = stack[19].m_obj;
lean_object* v___x_1923_ = stack[20].m_obj;
lean_object* v_opts_1924_ = stack[21].m_obj;
lean_object* v___x_1925_ = stack[22].m_obj;
lean_object* v_snd_1926_ = stack[23].m_obj;
lean_object* v_prom_1927_ = stack[24].m_obj;
lean_object* v_old_x3f_1928_ = stack[25].m_obj;
lean_object* v_parseCancelTk_1929_ = stack[26].m_obj;
lean_object* v_next_x3f_1930_ = stack[27].m_obj;
lean_object* v_res_2170_;
v_res_2170_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_1903_, v_val_1904_, v_fst_1905_, v_revCmds_1906_, v_fst_1907_, v_val_1908_, v_a_1909_, v_snd_1910_, v___x_1911_, v___x_1912_, v_fst_1913_, v_val_1914_, v_val_1915_, v___x_1916_, v___f_1917_, v___f_1918_, v___f_1919_, v_pos_1920_, v_cmdState_1921_, v_val_1922_, v___x_1923_, v_opts_1924_, v___x_1925_, v_snd_1926_, v_prom_1927_, v_old_x3f_1928_, v_parseCancelTk_1929_, v_next_x3f_1930_);
stack->m_obj
 = v_res_2170_;
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2172_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2176_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2175_);
return v___x_2176_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2177_, lean_object* v_revCmds_2178_, lean_object* v_fst_2179_, uint8_t v_val_2180_, lean_object* v_a_2181_, lean_object* v_snd_2182_, lean_object* v___x_2183_, uint8_t v___x_2184_, lean_object* v___x_2185_, lean_object* v___f_2186_, lean_object* v___f_2187_, lean_object* v___f_2188_, lean_object* v_pos_2189_, lean_object* v_cmdState_2190_, lean_object* v___x_2191_, lean_object* v_opts_2192_, lean_object* v_prom_2193_, lean_object* v_old_x3f_2194_, lean_object* v_parseCancelTk_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v_snapshotTasks_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v_traceTask_2210_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; size_t v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v_env_2255_; lean_object* v_messages_2256_; lean_object* v_scopes_2257_; lean_object* v_infoState_2258_; lean_object* v_traceState_2259_; lean_object* v_snapshotTasks_2260_; lean_object* v_codeQualityEntryTasks_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v_reportedCmdState_2265_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; size_t v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v_reportedCmdState_2324_; lean_object* v___x_2332_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; size_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v_fst_2463_; lean_object* v_snd_2464_; uint8_t v___x_2476_; 
v___x_2197_ = lean_io_promise_new();
v___x_2198_ = lean_io_promise_new();
v___x_2199_ = lean_io_promise_new();
v___x_2200_ = lean_io_promise_new();
v___x_2332_ = l_Lean_internal_cmdlineSnapshots;
v___x_2476_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2192_, v___x_2332_);
if (v___x_2476_ == 0)
{
lean_inc_ref(v_fst_2179_);
lean_inc(v_fst_2177_);
v_fst_2463_ = v_fst_2177_;
v_snd_2464_ = v_fst_2179_;
goto v___jp_2462_;
}
else
{
uint8_t v___x_2477_; 
lean_inc(v_fst_2177_);
v___x_2477_ = l_Lean_Parser_isTerminalCommand(v_fst_2177_);
if (v___x_2477_ == 0)
{
if (v___x_2476_ == 0)
{
lean_inc_ref(v_fst_2179_);
lean_inc(v_fst_2177_);
v_fst_2463_ = v_fst_2177_;
v_snd_2464_ = v_fst_2179_;
goto v___jp_2462_;
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_box(0);
v___x_2479_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2463_ = v___x_2478_;
v_snd_2464_ = v___x_2479_;
goto v___jp_2462_;
}
}
else
{
lean_inc_ref(v_fst_2179_);
lean_inc(v_fst_2177_);
v_fst_2463_ = v_fst_2177_;
v_snd_2464_ = v_fst_2179_;
goto v___jp_2462_;
}
}
v___jp_2201_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2205_);
lean_ctor_set(v___x_2211_, 1, v___y_2208_);
lean_ctor_set(v___x_2211_, 2, v___y_2206_);
lean_ctor_set(v___x_2211_, 3, v_traceTask_2210_);
v___x_2212_ = lean_array_push(v_snapshotTasks_2204_, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___y_2209_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_io_promise_resolve(v___x_2213_, v___x_2200_);
lean_dec(v___x_2200_);
if (lean_obj_tag(v___y_2202_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_val_2215_ = lean_ctor_get(v___y_2202_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___y_2202_, 1);
v___x_2216_ = lean_box(0);
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_fst_2177_);
lean_ctor_set(v___x_2217_, 1, v_revCmds_2178_);
v___x_2218_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2216_, v_fst_2179_, v___y_2203_, v_val_2215_, v_val_2180_, v___y_2207_, v___x_2217_, v_a_2181_);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; 
lean_dec_ref(v___y_2207_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v_fst_2179_);
lean_dec(v_revCmds_2178_);
lean_dec(v_fst_2177_);
v___x_2219_ = lean_box(0);
return v___x_2219_;
}
}
v___jp_2220_:
{
lean_object* v_snapshotTasks_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_snapshotTasks_2229_ = lean_ctor_get(v___y_2223_, 10);
lean_inc_ref(v_snapshotTasks_2229_);
v___x_2230_ = lean_mk_empty_array_with_capacity(v___y_2221_);
lean_dec(v___y_2221_);
lean_inc_ref(v___y_2228_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___y_2228_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_task_pure(v___x_2231_);
v___y_2202_ = v___y_2222_;
v___y_2203_ = v___y_2223_;
v_snapshotTasks_2204_ = v_snapshotTasks_2229_;
v___y_2205_ = v___y_2224_;
v___y_2206_ = v___y_2225_;
v___y_2207_ = v___y_2226_;
v___y_2208_ = v___y_2227_;
v___y_2209_ = v___y_2228_;
v_traceTask_2210_ = v___x_2232_;
goto v___jp_2201_;
}
v___jp_2233_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_opts_2275_; uint8_t v_hasTrace_2276_; 
v___x_2266_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2256_);
v___x_2267_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2267_, 0, v___y_2242_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
lean_ctor_set(v___x_2267_, 2, v___y_2246_);
lean_ctor_set(v___x_2267_, 3, v_traceState_2259_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*4, v_val_2180_);
v___x_2268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_reportedCmdState_2265_);
lean_ctor_set(v___x_2268_, 2, v_codeQualityEntryTasks_2261_);
v___x_2269_ = lean_io_promise_resolve(v___x_2268_, v___x_2198_);
lean_dec(v___x_2198_);
v___x_2270_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2258_);
lean_inc(v___y_2243_);
v___x_2271_ = l_BaseIO_chainTask___redArg(v___x_2270_, v___y_2247_, v___y_2243_, v___x_2184_);
v___x_2272_ = l_Lean_inheritedTraceOptions;
v___x_2273_ = lean_st_ref_get(v___x_2272_);
v___x_2274_ = l_List_head_x21___redArg(v___x_2185_, v_scopes_2257_);
lean_dec(v_scopes_2257_);
lean_dec_ref(v___x_2185_);
v_opts_2275_ = lean_ctor_get(v___x_2274_, 1);
lean_inc_ref(v_opts_2275_);
lean_dec(v___x_2274_);
v_hasTrace_2276_ = lean_ctor_get_uint8(v_opts_2275_, sizeof(void*)*1);
if (v_hasTrace_2276_ == 0)
{
lean_dec_ref(v_opts_2275_);
lean_dec(v___x_2273_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_snapshotTasks_2260_);
lean_dec_ref(v_env_2255_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2244_);
lean_dec(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v_pos_2189_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___f_2187_);
lean_dec_ref(v___f_2186_);
lean_dec(v___x_2183_);
v___y_2221_ = v___y_2243_;
v___y_2222_ = v___y_2253_;
v___y_2223_ = v___y_2254_;
v___y_2224_ = v___y_2245_;
v___y_2225_ = v___y_2248_;
v___y_2226_ = v___y_2263_;
v___y_2227_ = v___y_2250_;
v___y_2228_ = v___y_2251_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2273_, v_opts_2275_, v___x_2277_);
lean_dec(v___x_2273_);
if (v___x_2278_ == 0)
{
lean_dec_ref(v_opts_2275_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_snapshotTasks_2260_);
lean_dec_ref(v_env_2255_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2244_);
lean_dec(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v_pos_2189_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___f_2187_);
lean_dec_ref(v___f_2186_);
lean_dec(v___x_2183_);
v___y_2221_ = v___y_2243_;
v___y_2222_ = v___y_2253_;
v___y_2223_ = v___y_2254_;
v___y_2224_ = v___y_2245_;
v___y_2225_ = v___y_2248_;
v___y_2226_ = v___y_2263_;
v___y_2227_ = v___y_2250_;
v___y_2228_ = v___y_2251_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_inc_n(v___y_2243_, 3);
v___x_2279_ = lean_task_map(v___f_2186_, v___y_2249_, v___y_2243_, v___x_2184_);
lean_inc_n(v___y_2248_, 3);
lean_inc_n(v___y_2244_, 2);
lean_inc_n(v___y_2252_, 2);
v___x_2280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2280_, 0, v___y_2252_);
lean_ctor_set(v___x_2280_, 1, v___y_2244_);
lean_ctor_set(v___x_2280_, 2, v___y_2248_);
lean_ctor_set(v___x_2280_, 3, v___x_2279_);
v___x_2281_ = lean_task_map(v___f_2187_, v___y_2264_, v___y_2243_, v___x_2184_);
v___x_2282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2282_, 0, v___y_2252_);
lean_ctor_set(v___x_2282_, 1, v___y_2244_);
lean_ctor_set(v___x_2282_, 2, v___y_2248_);
lean_ctor_set(v___x_2282_, 3, v___x_2281_);
v___x_2283_ = lean_task_map(v___f_2188_, v___y_2262_, v___y_2243_, v___x_2184_);
v___x_2284_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2284_, 0, v___y_2252_);
lean_ctor_set(v___x_2284_, 1, v___y_2244_);
lean_ctor_set(v___x_2284_, 2, v___y_2248_);
lean_ctor_set(v___x_2284_, 3, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(3u);
v___x_2286_ = lean_mk_empty_array_with_capacity(v___x_2285_);
v___x_2287_ = lean_array_push(v___x_2286_, v___x_2280_);
v___x_2288_ = lean_array_push(v___x_2287_, v___x_2282_);
v___x_2289_ = lean_array_push(v___x_2288_, v___x_2284_);
v___x_2290_ = l_Array_append___redArg(v___x_2289_, v_snapshotTasks_2260_);
lean_inc_ref(v___y_2251_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___y_2251_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_box_usize(v___y_2240_);
v___x_2293_ = lean_box(v___x_2184_);
v___x_2294_ = lean_box(v_val_2180_);
v___x_2295_ = lean_box(v___x_2278_);
lean_inc_ref(v___x_2291_);
lean_inc_ref(v___y_2241_);
lean_inc_ref(v_a_2181_);
v___f_2296_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2296_, 0, v_a_2181_);
lean_closure_set(v___f_2296_, 1, v_opts_2275_);
lean_closure_set(v___f_2296_, 2, v___x_2183_);
lean_closure_set(v___f_2296_, 3, v___y_2236_);
lean_closure_set(v___f_2296_, 4, v___y_2235_);
lean_closure_set(v___f_2296_, 5, v___x_2292_);
lean_closure_set(v___f_2296_, 6, v___x_2293_);
lean_closure_set(v___f_2296_, 7, v_env_2255_);
lean_closure_set(v___f_2296_, 8, v___y_2241_);
lean_closure_set(v___f_2296_, 9, v___x_2291_);
lean_closure_set(v___f_2296_, 10, v_pos_2189_);
lean_closure_set(v___f_2296_, 11, v___x_2294_);
lean_closure_set(v___f_2296_, 12, v___y_2234_);
lean_closure_set(v___f_2296_, 13, v___y_2238_);
lean_closure_set(v___f_2296_, 14, v___y_2237_);
lean_closure_set(v___f_2296_, 15, v___x_2272_);
lean_closure_set(v___f_2296_, 16, v___y_2239_);
lean_closure_set(v___f_2296_, 17, v___x_2295_);
v___x_2297_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2291_);
v___x_2298_ = lean_io_bind_task(v___x_2297_, v___f_2296_, v___y_2243_, v_val_2180_);
v___y_2202_ = v___y_2253_;
v___y_2203_ = v___y_2254_;
v_snapshotTasks_2204_ = v_snapshotTasks_2260_;
v___y_2205_ = v___y_2245_;
v___y_2206_ = v___y_2248_;
v___y_2207_ = v___y_2263_;
v___y_2208_ = v___y_2250_;
v___y_2209_ = v___y_2251_;
v_traceTask_2210_ = v___x_2298_;
goto v___jp_2201_;
}
}
}
v___jp_2299_:
{
lean_object* v_env_2325_; lean_object* v_messages_2326_; lean_object* v_scopes_2327_; lean_object* v_infoState_2328_; lean_object* v_traceState_2329_; lean_object* v_snapshotTasks_2330_; lean_object* v_codeQualityEntryTasks_2331_; 
v_env_2325_ = lean_ctor_get(v___y_2320_, 0);
lean_inc_ref(v_env_2325_);
v_messages_2326_ = lean_ctor_get(v___y_2320_, 1);
lean_inc_ref(v_messages_2326_);
v_scopes_2327_ = lean_ctor_get(v___y_2320_, 2);
lean_inc(v_scopes_2327_);
v_infoState_2328_ = lean_ctor_get(v___y_2320_, 8);
lean_inc_ref(v_infoState_2328_);
v_traceState_2329_ = lean_ctor_get(v___y_2320_, 9);
lean_inc_ref(v_traceState_2329_);
v_snapshotTasks_2330_ = lean_ctor_get(v___y_2320_, 10);
lean_inc_ref(v_snapshotTasks_2330_);
v_codeQualityEntryTasks_2331_ = lean_ctor_get(v___y_2320_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2331_);
v___y_2234_ = v___y_2300_;
v___y_2235_ = v___y_2301_;
v___y_2236_ = v___y_2302_;
v___y_2237_ = v___y_2303_;
v___y_2238_ = v___y_2304_;
v___y_2239_ = v___y_2305_;
v___y_2240_ = v___y_2306_;
v___y_2241_ = v___y_2307_;
v___y_2242_ = v___y_2308_;
v___y_2243_ = v___y_2309_;
v___y_2244_ = v___y_2310_;
v___y_2245_ = v___y_2311_;
v___y_2246_ = v___y_2312_;
v___y_2247_ = v___y_2313_;
v___y_2248_ = v___y_2314_;
v___y_2249_ = v___y_2315_;
v___y_2250_ = v___y_2316_;
v___y_2251_ = v___y_2317_;
v___y_2252_ = v___y_2318_;
v___y_2253_ = v___y_2319_;
v___y_2254_ = v___y_2320_;
v_env_2255_ = v_env_2325_;
v_messages_2256_ = v_messages_2326_;
v_scopes_2257_ = v_scopes_2327_;
v_infoState_2258_ = v_infoState_2328_;
v_traceState_2259_ = v_traceState_2329_;
v_snapshotTasks_2260_ = v_snapshotTasks_2330_;
v_codeQualityEntryTasks_2261_ = v_codeQualityEntryTasks_2331_;
v___y_2262_ = v___y_2321_;
v___y_2263_ = v___y_2322_;
v___y_2264_ = v___y_2323_;
v_reportedCmdState_2265_ = v_reportedCmdState_2324_;
goto v___jp_2233_;
}
v___jp_2333_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; uint8_t v___x_2357_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2351_);
lean_ctor_set(v___x_2352_, 1, v___x_2197_);
lean_inc_ref(v___y_2343_);
lean_inc_n(v_pos_2189_, 2);
lean_inc(v_revCmds_2178_);
lean_inc(v_fst_2177_);
v___x_2353_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2177_, v_revCmds_2178_, v_cmdState_2190_, v_pos_2189_, v___x_2352_, v___y_2343_, v_a_2181_);
v___x_2354_ = lean_box(v_val_2180_);
v___x_2355_ = lean_box(v___x_2184_);
lean_inc_ref(v_a_2181_);
lean_inc(v___y_2337_);
lean_inc_ref(v___x_2185_);
lean_inc_ref(v___x_2353_);
lean_inc_ref(v___y_2345_);
lean_inc_ref(v___y_2334_);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2356_, 0, v___y_2334_);
lean_closure_set(v___f_2356_, 1, v___y_2345_);
lean_closure_set(v___f_2356_, 2, v___x_2354_);
lean_closure_set(v___f_2356_, 3, v___x_2199_);
lean_closure_set(v___f_2356_, 4, v___x_2353_);
lean_closure_set(v___f_2356_, 5, v___x_2185_);
lean_closure_set(v___f_2356_, 6, v___y_2337_);
lean_closure_set(v___f_2356_, 7, v___x_2355_);
lean_closure_set(v___f_2356_, 8, v_a_2181_);
lean_closure_set(v___f_2356_, 9, v_pos_2189_);
lean_closure_set(v___f_2356_, 10, v___x_2191_);
v___x_2357_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2192_, v___x_2332_);
if (v___x_2357_ == 0)
{
lean_inc_ref(v___x_2353_);
lean_inc(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2334_);
v___y_2300_ = v___y_2334_;
v___y_2301_ = v___y_2335_;
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2338_;
v___y_2304_ = v___y_2340_;
v___y_2305_ = v___y_2341_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___y_2345_;
v___y_2308_ = v___y_2334_;
v___y_2309_ = v___y_2337_;
v___y_2310_ = v___y_2339_;
v___y_2311_ = v___y_2346_;
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___f_2356_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2344_;
v___y_2316_ = v___y_2347_;
v___y_2317_ = v___y_2338_;
v___y_2318_ = v___y_2336_;
v___y_2319_ = v___y_2348_;
v___y_2320_ = v___x_2353_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v___y_2350_;
v_reportedCmdState_2324_ = v___x_2353_;
goto v___jp_2299_;
}
else
{
uint8_t v___x_2358_; 
lean_inc(v_fst_2177_);
v___x_2358_ = l_Lean_Parser_isTerminalCommand(v_fst_2177_);
if (v___x_2358_ == 0)
{
if (v___x_2357_ == 0)
{
lean_inc_ref(v___x_2353_);
lean_inc(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2334_);
v___y_2300_ = v___y_2334_;
v___y_2301_ = v___y_2335_;
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2338_;
v___y_2304_ = v___y_2340_;
v___y_2305_ = v___y_2341_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___y_2345_;
v___y_2308_ = v___y_2334_;
v___y_2309_ = v___y_2337_;
v___y_2310_ = v___y_2339_;
v___y_2311_ = v___y_2346_;
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___f_2356_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2344_;
v___y_2316_ = v___y_2347_;
v___y_2317_ = v___y_2338_;
v___y_2318_ = v___y_2336_;
v___y_2319_ = v___y_2348_;
v___y_2320_ = v___x_2353_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v___y_2350_;
v_reportedCmdState_2324_ = v___x_2353_;
goto v___jp_2299_;
}
else
{
lean_object* v_env_2359_; lean_object* v_messages_2360_; lean_object* v_scopes_2361_; lean_object* v_infoState_2362_; lean_object* v_traceState_2363_; lean_object* v_snapshotTasks_2364_; lean_object* v_codeQualityEntryTasks_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_env_2359_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref_n(v_env_2359_, 2);
v_messages_2360_ = lean_ctor_get(v___x_2353_, 1);
lean_inc_ref(v_messages_2360_);
v_scopes_2361_ = lean_ctor_get(v___x_2353_, 2);
lean_inc(v_scopes_2361_);
v_infoState_2362_ = lean_ctor_get(v___x_2353_, 8);
lean_inc_ref(v_infoState_2362_);
v_traceState_2363_ = lean_ctor_get(v___x_2353_, 9);
lean_inc_ref(v_traceState_2363_);
v_snapshotTasks_2364_ = lean_ctor_get(v___x_2353_, 10);
lean_inc_ref(v_snapshotTasks_2364_);
v_codeQualityEntryTasks_2365_ = lean_ctor_get(v___x_2353_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2365_);
v___x_2366_ = lean_mk_empty_array_with_capacity(v___y_2335_);
lean_inc_ref(v___x_2366_);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_inc_n(v___y_2337_, 4);
v___x_2368_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
lean_ctor_set(v___x_2368_, 1, v___x_2366_);
lean_ctor_set(v___x_2368_, 2, v___y_2337_);
lean_ctor_set(v___x_2368_, 3, v___y_2337_);
lean_ctor_set_usize(v___x_2368_, 4, v___y_2342_);
v___x_2369_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2368_, 2);
v___x_2370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2368_);
lean_ctor_set(v___x_2370_, 2, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2372_ = l_Lean_Options_empty;
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_mk_empty_array_with_capacity(v___y_2337_);
lean_inc_ref_n(v___x_2374_, 3);
lean_inc_n(v___x_2183_, 2);
v___x_2375_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2375_, 0, v___x_2371_);
lean_ctor_set(v___x_2375_, 1, v___x_2372_);
lean_ctor_set(v___x_2375_, 2, v___x_2183_);
lean_ctor_set(v___x_2375_, 3, v___x_2373_);
lean_ctor_set(v___x_2375_, 4, v___x_2373_);
lean_ctor_set(v___x_2375_, 5, v___x_2374_);
lean_ctor_set(v___x_2375_, 6, v___x_2374_);
lean_ctor_set(v___x_2375_, 7, v___x_2373_);
lean_ctor_set(v___x_2375_, 8, v___x_2373_);
lean_ctor_set(v___x_2375_, 9, v___x_2373_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*10, v_val_2180_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*10 + 1, v_val_2180_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*10 + 2, v_val_2180_);
v___x_2376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v___x_2373_);
v___x_2377_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2378_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2379_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2183_);
v___x_2380_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2381_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
lean_ctor_set(v___x_2381_, 2, v___x_2368_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*3, v___x_2184_);
v___x_2382_ = lean_box(0);
lean_inc_ref(v___y_2345_);
v___x_2383_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2383_, 0, v_env_2359_);
lean_ctor_set(v___x_2383_, 1, v___x_2370_);
lean_ctor_set(v___x_2383_, 2, v___x_2376_);
lean_ctor_set(v___x_2383_, 3, v___x_2369_);
lean_ctor_set(v___x_2383_, 4, v___x_2377_);
lean_ctor_set(v___x_2383_, 5, v___y_2337_);
lean_ctor_set(v___x_2383_, 6, v___x_2378_);
lean_ctor_set(v___x_2383_, 7, v___x_2379_);
lean_ctor_set(v___x_2383_, 8, v___x_2381_);
lean_ctor_set(v___x_2383_, 9, v___y_2345_);
lean_ctor_set(v___x_2383_, 10, v___x_2374_);
lean_ctor_set(v___x_2383_, 11, v___x_2382_);
lean_ctor_set(v___x_2383_, 12, v___x_2374_);
lean_inc(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2338_);
lean_inc_ref(v___y_2334_);
v___y_2234_ = v___y_2334_;
v___y_2235_ = v___y_2335_;
v___y_2236_ = v___y_2337_;
v___y_2237_ = v___y_2338_;
v___y_2238_ = v___y_2340_;
v___y_2239_ = v___y_2341_;
v___y_2240_ = v___y_2342_;
v___y_2241_ = v___y_2345_;
v___y_2242_ = v___y_2334_;
v___y_2243_ = v___y_2337_;
v___y_2244_ = v___y_2339_;
v___y_2245_ = v___y_2346_;
v___y_2246_ = v___y_2340_;
v___y_2247_ = v___f_2356_;
v___y_2248_ = v___y_2341_;
v___y_2249_ = v___y_2344_;
v___y_2250_ = v___y_2347_;
v___y_2251_ = v___y_2338_;
v___y_2252_ = v___y_2336_;
v___y_2253_ = v___y_2348_;
v___y_2254_ = v___x_2353_;
v_env_2255_ = v_env_2359_;
v_messages_2256_ = v_messages_2360_;
v_scopes_2257_ = v_scopes_2361_;
v_infoState_2258_ = v_infoState_2362_;
v_traceState_2259_ = v_traceState_2363_;
v_snapshotTasks_2260_ = v_snapshotTasks_2364_;
v_codeQualityEntryTasks_2261_ = v_codeQualityEntryTasks_2365_;
v___y_2262_ = v___y_2349_;
v___y_2263_ = v___y_2343_;
v___y_2264_ = v___y_2350_;
v_reportedCmdState_2265_ = v___x_2383_;
goto v___jp_2233_;
}
}
else
{
lean_inc_ref(v___x_2353_);
lean_inc(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2334_);
v___y_2300_ = v___y_2334_;
v___y_2301_ = v___y_2335_;
v___y_2302_ = v___y_2337_;
v___y_2303_ = v___y_2338_;
v___y_2304_ = v___y_2340_;
v___y_2305_ = v___y_2341_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___y_2345_;
v___y_2308_ = v___y_2334_;
v___y_2309_ = v___y_2337_;
v___y_2310_ = v___y_2339_;
v___y_2311_ = v___y_2346_;
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___f_2356_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2344_;
v___y_2316_ = v___y_2347_;
v___y_2317_ = v___y_2338_;
v___y_2318_ = v___y_2336_;
v___y_2319_ = v___y_2348_;
v___y_2320_ = v___x_2353_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v___y_2350_;
v_reportedCmdState_2324_ = v___x_2353_;
goto v___jp_2299_;
}
}
}
v___jp_2384_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2390_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2182_);
v___x_2391_ = l_IO_CancelToken_new();
v___x_2392_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2183_);
v___x_2393_ = l_Lean_Name_str___override(v___x_2183_, v___x_2392_);
v___x_2394_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2395_ = l_Lean_Name_str___override(v___x_2393_, v___x_2394_);
v___x_2396_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2397_ = l_Lean_Name_str___override(v___x_2395_, v___x_2396_);
v___x_2398_ = l_Lean_Name_str___override(v___x_2397_, v___x_2394_);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = l_Lean_Name_num___override(v___x_2398_, v___x_2399_);
v___x_2401_ = l_Lean_Name_str___override(v___x_2400_, v___x_2394_);
v___x_2402_ = l_Lean_Name_str___override(v___x_2401_, v___x_2396_);
v___x_2403_ = l_Lean_Name_str___override(v___x_2402_, v___x_2394_);
v___x_2404_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2405_ = l_Lean_Name_str___override(v___x_2403_, v___x_2404_);
v___x_2406_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2407_ = l_Lean_Name_str___override(v___x_2405_, v___x_2406_);
v___x_2408_ = l_Lean_Name_toString(v___x_2407_, v___x_2184_);
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_unsigned_to_nat(32u);
v___x_2411_ = lean_mk_empty_array_with_capacity(v___x_2410_);
lean_dec_ref(v___x_2411_);
v___x_2412_ = ((size_t)5ULL);
v___x_2413_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2408_, 2);
v___x_2414_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2414_, 0, v___x_2408_);
lean_ctor_set(v___x_2414_, 1, v___x_2390_);
lean_ctor_set(v___x_2414_, 2, v___x_2409_);
lean_ctor_set(v___x_2414_, 3, v___x_2413_);
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*4, v_val_2180_);
v___x_2415_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2416_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2416_, 0, v___x_2408_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
lean_ctor_set(v___x_2416_, 2, v___x_2409_);
lean_ctor_set(v___x_2416_, 3, v___x_2413_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*4, v_val_2180_);
lean_inc(v___y_2386_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___y_2386_);
v___x_2418_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2417_);
lean_inc_ref(v___x_2391_);
v___x_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2391_);
v___x_2420_ = l_IO_Promise_result_x21___redArg(v___x_2197_);
lean_inc_ref(v___x_2420_);
lean_inc(v___x_2418_);
lean_inc_ref_n(v___x_2417_, 3);
v___x_2421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2417_);
lean_ctor_set(v___x_2421_, 1, v___x_2418_);
lean_ctor_set(v___x_2421_, 2, v___x_2419_);
lean_ctor_set(v___x_2421_, 3, v___x_2420_);
v___x_2422_ = l_IO_Promise_result_x21___redArg(v___x_2198_);
lean_inc_ref(v___x_2422_);
lean_inc_n(v___y_2388_, 3);
v___x_2423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2417_);
lean_ctor_set(v___x_2423_, 1, v___y_2388_);
lean_ctor_set(v___x_2423_, 2, v___x_2409_);
lean_ctor_set(v___x_2423_, 3, v___x_2422_);
v___x_2424_ = l_IO_Promise_result_x21___redArg(v___x_2199_);
lean_inc_ref(v___x_2424_);
v___x_2425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2417_);
lean_ctor_set(v___x_2425_, 1, v___y_2388_);
lean_ctor_set(v___x_2425_, 2, v___x_2409_);
lean_ctor_set(v___x_2425_, 3, v___x_2424_);
v___x_2426_ = l_IO_Promise_result_x21___redArg(v___x_2200_);
v___x_2427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2409_);
lean_ctor_set(v___x_2427_, 1, v___y_2388_);
lean_ctor_set(v___x_2427_, 2, v___x_2409_);
lean_ctor_set(v___x_2427_, 3, v___x_2426_);
lean_inc_ref(v___x_2416_);
v___x_2428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2416_);
lean_ctor_set(v___x_2428_, 1, v___x_2421_);
lean_ctor_set(v___x_2428_, 2, v___x_2423_);
lean_ctor_set(v___x_2428_, 3, v___x_2425_);
lean_ctor_set(v___x_2428_, 4, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2414_);
lean_ctor_set(v___x_2429_, 1, v___y_2386_);
lean_ctor_set(v___x_2429_, 2, v___y_2387_);
lean_ctor_set(v___x_2429_, 3, v___x_2428_);
lean_ctor_set(v___x_2429_, 4, v___y_2389_);
v___x_2430_ = lean_io_promise_resolve(v___x_2429_, v_prom_2193_);
if (lean_obj_tag(v_old_x3f_2194_) == 0)
{
v___y_2334_ = v___x_2408_;
v___y_2335_ = v___x_2410_;
v___y_2336_ = v___x_2417_;
v___y_2337_ = v___x_2399_;
v___y_2338_ = v___x_2416_;
v___y_2339_ = v___x_2418_;
v___y_2340_ = v___x_2409_;
v___y_2341_ = v___x_2409_;
v___y_2342_ = v___x_2412_;
v___y_2343_ = v___x_2391_;
v___y_2344_ = v___x_2420_;
v___y_2345_ = v___x_2413_;
v___y_2346_ = v___x_2409_;
v___y_2347_ = v___y_2388_;
v___y_2348_ = v___y_2385_;
v___y_2349_ = v___x_2424_;
v___y_2350_ = v___x_2422_;
v___y_2351_ = v___x_2409_;
goto v___jp_2333_;
}
else
{
lean_object* v_val_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2442_; 
v_val_2431_ = lean_ctor_get(v_old_x3f_2194_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_old_x3f_2194_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2433_ = v_old_x3f_2194_;
v_isShared_2434_ = v_isSharedCheck_2442_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_val_2431_);
lean_dec(v_old_x3f_2194_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2442_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v_elabSnap_2435_; lean_object* v_stx_2436_; lean_object* v_elabSnap_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v_elabSnap_2435_ = lean_ctor_get(v_val_2431_, 3);
lean_inc_ref(v_elabSnap_2435_);
v_stx_2436_ = lean_ctor_get(v_val_2431_, 1);
lean_inc(v_stx_2436_);
lean_dec(v_val_2431_);
v_elabSnap_2437_ = lean_ctor_get(v_elabSnap_2435_, 1);
lean_inc_ref(v_elabSnap_2437_);
lean_dec_ref(v_elabSnap_2435_);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v_stx_2436_);
lean_ctor_set(v___x_2438_, 1, v_elabSnap_2437_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2438_);
v___x_2440_ = v___x_2433_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
v___y_2334_ = v___x_2408_;
v___y_2335_ = v___x_2410_;
v___y_2336_ = v___x_2417_;
v___y_2337_ = v___x_2399_;
v___y_2338_ = v___x_2416_;
v___y_2339_ = v___x_2418_;
v___y_2340_ = v___x_2409_;
v___y_2341_ = v___x_2409_;
v___y_2342_ = v___x_2412_;
v___y_2343_ = v___x_2391_;
v___y_2344_ = v___x_2420_;
v___y_2345_ = v___x_2413_;
v___y_2346_ = v___x_2409_;
v___y_2347_ = v___y_2388_;
v___y_2348_ = v___y_2385_;
v___y_2349_ = v___x_2424_;
v___y_2350_ = v___x_2422_;
v___y_2351_ = v___x_2440_;
goto v___jp_2333_;
}
}
}
}
v___jp_2443_:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2446_);
lean_inc(v_fst_2177_);
v___x_2448_ = l_Lean_Parser_isTerminalCommand(v_fst_2177_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v_toProcessingContext_2450_; lean_object* v_pos_2451_; lean_object* v_endPos_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2449_ = lean_io_promise_new();
v_toProcessingContext_2450_ = lean_ctor_get(v_a_2181_, 0);
v_pos_2451_ = lean_ctor_get(v_fst_2179_, 0);
v_endPos_2452_ = lean_ctor_get(v_toProcessingContext_2450_, 3);
lean_inc(v___x_2449_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2449_);
v___x_2454_ = lean_box(0);
lean_inc(v_endPos_2452_);
lean_inc(v_pos_2451_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_pos_2451_);
lean_ctor_set(v___x_2455_, 1, v_endPos_2452_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_parseCancelTk_2195_);
v___x_2458_ = l_IO_Promise_result_x21___redArg(v___x_2449_);
lean_dec(v___x_2449_);
v___x_2459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2454_);
lean_ctor_set(v___x_2459_, 1, v___x_2456_);
lean_ctor_set(v___x_2459_, 2, v___x_2457_);
lean_ctor_set(v___x_2459_, 3, v___x_2458_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
v___y_2385_ = v___x_2453_;
v___y_2386_ = v___y_2444_;
v___y_2387_ = v___y_2445_;
v___y_2388_ = v___x_2447_;
v___y_2389_ = v___x_2460_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2461_; 
lean_dec_ref(v_parseCancelTk_2195_);
v___x_2461_ = lean_box(0);
v___y_2385_ = v___x_2461_;
v___y_2386_ = v___y_2444_;
v___y_2387_ = v___y_2445_;
v___y_2388_ = v___x_2447_;
v___y_2389_ = v___x_2461_;
goto v___jp_2384_;
}
}
v___jp_2462_:
{
lean_object* v___x_2465_; 
lean_inc(v_fst_2177_);
v___x_2465_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2177_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_box(0);
v___y_2444_ = v_fst_2463_;
v___y_2445_ = v_snd_2464_;
v___y_2446_ = v___x_2466_;
goto v___jp_2443_;
}
else
{
lean_object* v_val_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2475_; 
v_val_2467_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2469_ = v___x_2465_;
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_val_2467_);
lean_dec(v___x_2465_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_inc(v_val_2467_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_val_2467_);
lean_ctor_set(v___x_2471_, 1, v_val_2467_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2471_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
v___y_2444_ = v_fst_2463_;
v___y_2445_ = v_snd_2464_;
v___y_2446_ = v___x_2473_;
goto v___jp_2443_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2177_ = stack[0].m_obj;
lean_object* v_revCmds_2178_ = stack[1].m_obj;
lean_object* v_fst_2179_ = stack[2].m_obj;
uint8_t v_val_2180_ = stack[3].m_num;
lean_object* v_a_2181_ = stack[4].m_obj;
lean_object* v_snd_2182_ = stack[5].m_obj;
lean_object* v___x_2183_ = stack[6].m_obj;
uint8_t v___x_2184_ = stack[7].m_num;
lean_object* v___x_2185_ = stack[8].m_obj;
lean_object* v___f_2186_ = stack[9].m_obj;
lean_object* v___f_2187_ = stack[10].m_obj;
lean_object* v___f_2188_ = stack[11].m_obj;
lean_object* v_pos_2189_ = stack[12].m_obj;
lean_object* v_cmdState_2190_ = stack[13].m_obj;
lean_object* v___x_2191_ = stack[14].m_obj;
lean_object* v_opts_2192_ = stack[15].m_obj;
lean_object* v_prom_2193_ = stack[16].m_obj;
lean_object* v_old_x3f_2194_ = stack[17].m_obj;
lean_object* v_parseCancelTk_2195_ = stack[18].m_obj;
lean_object* v_res_2480_;
v_res_2480_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2177_, v_revCmds_2178_, v_fst_2179_, v_val_2180_, v_a_2181_, v_snd_2182_, v___x_2183_, v___x_2184_, v___x_2185_, v___f_2186_, v___f_2187_, v___f_2188_, v_pos_2189_, v_cmdState_2190_, v___x_2191_, v_opts_2192_, v_prom_2193_, v_old_x3f_2194_, v_parseCancelTk_2195_);
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2481_ = _args[0];
lean_object* v_revCmds_2482_ = _args[1];
lean_object* v_fst_2483_ = _args[2];
lean_object* v_val_2484_ = _args[3];
lean_object* v_a_2485_ = _args[4];
lean_object* v_snd_2486_ = _args[5];
lean_object* v___x_2487_ = _args[6];
lean_object* v___x_2488_ = _args[7];
lean_object* v___x_2489_ = _args[8];
lean_object* v___f_2490_ = _args[9];
lean_object* v___f_2491_ = _args[10];
lean_object* v___f_2492_ = _args[11];
lean_object* v_pos_2493_ = _args[12];
lean_object* v_cmdState_2494_ = _args[13];
lean_object* v___x_2495_ = _args[14];
lean_object* v_opts_2496_ = _args[15];
lean_object* v_prom_2497_ = _args[16];
lean_object* v_old_x3f_2498_ = _args[17];
lean_object* v_parseCancelTk_2499_ = _args[18];
lean_object* v___y_2500_ = _args[19];
_start:
{
uint8_t v_val_38007__boxed_2501_; uint8_t v___x_38010__boxed_2502_; lean_object* v_res_2503_; 
v_val_38007__boxed_2501_ = lean_unbox(v_val_2484_);
v___x_38010__boxed_2502_ = lean_unbox(v___x_2488_);
v_res_2503_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2481_, v_revCmds_2482_, v_fst_2483_, v_val_38007__boxed_2501_, v_a_2485_, v_snd_2486_, v___x_2487_, v___x_38010__boxed_2502_, v___x_2489_, v___f_2490_, v___f_2491_, v___f_2492_, v_pos_2493_, v_cmdState_2494_, v___x_2495_, v_opts_2496_, v_prom_2497_, v_old_x3f_2498_, v_parseCancelTk_2499_);
lean_dec(v_prom_2497_);
lean_dec_ref(v_opts_2496_);
lean_dec_ref(v_a_2485_);
return v_res_2503_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2506_, lean_object* v_parserState_2507_, lean_object* v_cmdState_2508_, lean_object* v_prom_2509_, uint8_t v_sync_2510_, lean_object* v_parseCancelTk_2511_, lean_object* v_revCmds_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v___y_2518_; lean_object* v_toSnapshot_2520_; lean_object* v_stx_2521_; lean_object* v_parserState_2522_; lean_object* v_elabSnap_2523_; lean_object* v_val_2524_; lean_object* v_newParserState_2525_; lean_object* v___f_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; uint8_t v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; uint8_t v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___x_2697_; 
v___f_2556_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2557_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2558_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2559_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2560_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2697_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2506_) == 1)
{
lean_object* v_val_2730_; lean_object* v_nextCmdSnap_x3f_2731_; 
v_val_2730_ = lean_ctor_get(v_old_x3f_2506_, 0);
v_nextCmdSnap_x3f_2731_ = lean_ctor_get(v_val_2730_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2731_) == 0)
{
goto v___jp_2698_;
}
else
{
lean_object* v_toSnapshot_2732_; lean_object* v_stx_2733_; lean_object* v_parserState_2734_; lean_object* v_elabSnap_2735_; lean_object* v_val_2736_; lean_object* v___x_2737_; 
v_toSnapshot_2732_ = lean_ctor_get(v_val_2730_, 0);
v_stx_2733_ = lean_ctor_get(v_val_2730_, 1);
v_parserState_2734_ = lean_ctor_get(v_val_2730_, 2);
v_elabSnap_2735_ = lean_ctor_get(v_val_2730_, 3);
v_val_2736_ = lean_ctor_get(v_nextCmdSnap_x3f_2731_, 0);
lean_inc(v_val_2736_);
v___x_2737_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2736_);
if (lean_obj_tag(v___x_2737_) == 1)
{
lean_object* v_val_2738_; lean_object* v_nextCmdSnap_x3f_2739_; 
v_val_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v_nextCmdSnap_x3f_2739_ = lean_ctor_get(v_val_2738_, 4);
lean_inc(v_nextCmdSnap_x3f_2739_);
lean_dec(v_val_2738_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2739_) == 0)
{
goto v___jp_2698_;
}
else
{
lean_object* v_val_2740_; lean_object* v___x_2741_; 
v_val_2740_ = lean_ctor_get(v_nextCmdSnap_x3f_2739_, 0);
lean_inc(v_val_2740_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2739_, 1);
v___x_2741_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2740_);
if (lean_obj_tag(v___x_2741_) == 1)
{
lean_object* v_val_2742_; lean_object* v_parserState_2743_; lean_object* v_pos_2744_; uint8_t v___x_2745_; 
v_val_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_val_2742_);
lean_dec_ref_known(v___x_2741_, 1);
v_parserState_2743_ = lean_ctor_get(v_val_2742_, 2);
lean_inc_ref(v_parserState_2743_);
lean_dec(v_val_2742_);
v_pos_2744_ = lean_ctor_get(v_parserState_2743_, 0);
lean_inc(v_pos_2744_);
lean_dec_ref(v_parserState_2743_);
v___x_2745_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2744_, v_a_2513_);
lean_dec(v_pos_2744_);
if (v___x_2745_ == 0)
{
goto v___jp_2698_;
}
else
{
lean_inc(v_val_2736_);
lean_inc_ref(v_elabSnap_2735_);
lean_inc_ref_n(v_parserState_2734_, 2);
lean_inc(v_stx_2733_);
lean_inc_ref(v_toSnapshot_2732_);
lean_dec_ref_known(v_old_x3f_2506_, 1);
lean_dec_ref(v_parseCancelTk_2511_);
lean_dec_ref(v_cmdState_2508_);
lean_dec_ref(v_parserState_2507_);
v_toSnapshot_2520_ = v_toSnapshot_2732_;
v_stx_2521_ = v_stx_2733_;
v_parserState_2522_ = v_parserState_2734_;
v_elabSnap_2523_ = v_elabSnap_2735_;
v_val_2524_ = v_val_2736_;
v_newParserState_2525_ = v_parserState_2734_;
goto v___jp_2519_;
}
}
else
{
lean_dec(v___x_2741_);
goto v___jp_2698_;
}
}
}
else
{
lean_dec(v___x_2737_);
goto v___jp_2698_;
}
}
}
else
{
goto v___jp_2698_;
}
v___jp_2515_:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_box(0);
return v___x_2516_;
}
v___jp_2517_:
{
goto v___jp_2515_;
}
v___jp_2519_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v_resultSnap_2528_; lean_object* v_task_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2552_; 
v___x_2526_ = lean_io_promise_new();
v___x_2527_ = l_IO_CancelToken_new();
v_resultSnap_2528_ = lean_ctor_get(v_elabSnap_2523_, 2);
lean_inc_ref(v_resultSnap_2528_);
v_task_2529_ = lean_ctor_get(v_resultSnap_2528_, 3);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_resultSnap_2528_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; 
v_unused_2553_ = lean_ctor_get(v_resultSnap_2528_, 2);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_resultSnap_2528_, 1);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_resultSnap_2528_, 0);
lean_dec(v_unused_2555_);
v___x_2531_ = v_resultSnap_2528_;
v_isShared_2532_ = v_isSharedCheck_2552_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_task_2529_);
lean_dec(v_resultSnap_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2552_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v_toProcessingContext_2538_; lean_object* v_pos_2539_; lean_object* v_endPos_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2533_ = lean_box(v_sync_2510_);
lean_inc_ref(v_a_2513_);
lean_inc_ref(v___x_2527_);
lean_inc(v___x_2526_);
lean_inc_ref(v_newParserState_2525_);
lean_inc(v_stx_2521_);
v___f_2534_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2534_, 0, v_val_2524_);
lean_closure_set(v___f_2534_, 1, v_stx_2521_);
lean_closure_set(v___f_2534_, 2, v_revCmds_2512_);
lean_closure_set(v___f_2534_, 3, v_newParserState_2525_);
lean_closure_set(v___f_2534_, 4, v___x_2526_);
lean_closure_set(v___f_2534_, 5, v___x_2533_);
lean_closure_set(v___f_2534_, 6, v___x_2527_);
lean_closure_set(v___f_2534_, 7, v_a_2513_);
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = 1;
v___x_2537_ = l_BaseIO_chainTask___redArg(v_task_2529_, v___f_2534_, v___x_2535_, v___x_2536_);
v_toProcessingContext_2538_ = lean_ctor_get(v_a_2513_, 0);
v_pos_2539_ = lean_ctor_get(v_newParserState_2525_, 0);
lean_inc(v_pos_2539_);
lean_dec_ref(v_newParserState_2525_);
v_endPos_2540_ = lean_ctor_get(v_toProcessingContext_2538_, 3);
v___x_2541_ = lean_box(0);
lean_inc(v_endPos_2540_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_pos_2539_);
lean_ctor_set(v___x_2542_, 1, v_endPos_2540_);
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2527_);
v___x_2545_ = l_IO_Promise_result_x21___redArg(v___x_2526_);
lean_dec(v___x_2526_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 3, v___x_2545_);
lean_ctor_set(v___x_2531_, 2, v___x_2544_);
lean_ctor_set(v___x_2531_, 1, v___x_2543_);
lean_ctor_set(v___x_2531_, 0, v___x_2541_);
v___x_2547_ = v___x_2531_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2549_, 0, v_toSnapshot_2520_);
lean_ctor_set(v___x_2549_, 1, v_stx_2521_);
lean_ctor_set(v___x_2549_, 2, v_parserState_2522_);
lean_ctor_set(v___x_2549_, 3, v_elabSnap_2523_);
lean_ctor_set(v___x_2549_, 4, v___x_2548_);
v___x_2550_ = lean_io_promise_resolve(v___x_2549_, v_prom_2509_);
lean_dec(v_prom_2509_);
return v___x_2550_;
}
}
}
v___jp_2561_:
{
lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2579_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2578_);
v___x_2580_ = l_Lean_Parser_isTerminalCommand(v___y_2569_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_io_promise_new();
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
v___x_2583_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2579_, v___y_2574_, v___y_2575_, v_revCmds_2512_, v___y_2568_, v___y_2572_, v_a_2513_, v___y_2564_, v___y_2567_, v___y_2565_, v___y_2576_, v___y_2566_, v___y_2577_, v___x_2559_, v___f_2558_, v___f_2557_, v___f_2556_, v___y_2562_, v_cmdState_2508_, v___y_2563_, v___x_2560_, v___y_2571_, v___y_2570_, v___y_2573_, v_prom_2509_, v_old_x3f_2506_, v_parseCancelTk_2511_, v___x_2582_);
lean_dec(v_prom_2509_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2577_);
lean_dec(v___y_2574_);
v___y_2518_ = v___x_2583_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_box(0);
v___x_2585_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2579_, v___y_2574_, v___y_2575_, v_revCmds_2512_, v___y_2568_, v___y_2572_, v_a_2513_, v___y_2564_, v___y_2567_, v___y_2565_, v___y_2576_, v___y_2566_, v___y_2577_, v___x_2559_, v___f_2558_, v___f_2557_, v___f_2556_, v___y_2562_, v_cmdState_2508_, v___y_2563_, v___x_2560_, v___y_2571_, v___y_2570_, v___y_2573_, v_prom_2509_, v_old_x3f_2506_, v_parseCancelTk_2511_, v___x_2584_);
lean_dec(v_prom_2509_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2577_);
lean_dec(v___y_2574_);
v___y_2518_ = v___x_2585_;
goto v___jp_2517_;
}
}
v___jp_2586_:
{
lean_object* v___x_2603_; 
lean_inc(v___y_2600_);
v___x_2603_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2600_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_box(0);
v___y_2562_ = v___y_2587_;
v___y_2563_ = v___y_2588_;
v___y_2564_ = v___y_2589_;
v___y_2565_ = v___y_2590_;
v___y_2566_ = v___y_2591_;
v___y_2567_ = v___y_2592_;
v___y_2568_ = v___y_2593_;
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2594_;
v___y_2571_ = v___y_2595_;
v___y_2572_ = v___y_2596_;
v___y_2573_ = v_snd_2602_;
v___y_2574_ = v___y_2597_;
v___y_2575_ = v___y_2598_;
v___y_2576_ = v_fst_2601_;
v___y_2577_ = v___y_2599_;
v___y_2578_ = v___x_2604_;
goto v___jp_2561_;
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2613_; 
v_val_2605_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2607_ = v___x_2603_;
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_val_2605_);
lean_dec(v___x_2603_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_inc(v_val_2605_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_val_2605_);
lean_ctor_set(v___x_2609_, 1, v_val_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
v___y_2562_ = v___y_2587_;
v___y_2563_ = v___y_2588_;
v___y_2564_ = v___y_2589_;
v___y_2565_ = v___y_2590_;
v___y_2566_ = v___y_2591_;
v___y_2567_ = v___y_2592_;
v___y_2568_ = v___y_2593_;
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2594_;
v___y_2571_ = v___y_2595_;
v___y_2572_ = v___y_2596_;
v___y_2573_ = v_snd_2602_;
v___y_2574_ = v___y_2597_;
v___y_2575_ = v___y_2598_;
v___y_2576_ = v_fst_2601_;
v___y_2577_ = v___y_2599_;
v___y_2578_ = v___x_2611_;
goto v___jp_2561_;
}
}
}
}
v___jp_2614_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2618_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2619_ = l_Lean_Name_str___override(v___y_2616_, v___x_2618_);
v___x_2620_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2621_ = l_Lean_Name_str___override(v___x_2619_, v___x_2620_);
v___x_2622_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2623_ = l_Lean_Name_str___override(v___x_2621_, v___x_2622_);
v___x_2624_ = l_Lean_Name_str___override(v___x_2623_, v___x_2620_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = l_Lean_Name_num___override(v___x_2624_, v___x_2625_);
v___x_2627_ = l_Lean_Name_str___override(v___x_2626_, v___x_2620_);
v___x_2628_ = l_Lean_Name_str___override(v___x_2627_, v___x_2622_);
v___x_2629_ = l_Lean_Name_str___override(v___x_2628_, v___x_2620_);
v___x_2630_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2631_ = l_Lean_Name_str___override(v___x_2629_, v___x_2630_);
v___x_2632_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2633_ = l_Lean_Name_str___override(v___x_2631_, v___x_2632_);
v___x_2634_ = l_Lean_Name_toString(v___x_2633_, v___y_2615_);
v___x_2635_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2638_ = 0;
v___x_2639_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2639_, 0, v___x_2634_);
lean_ctor_set(v___x_2639_, 1, v___x_2635_);
lean_ctor_set(v___x_2639_, 2, v___x_2636_);
lean_ctor_set(v___x_2639_, 3, v___x_2637_);
lean_ctor_set_uint8(v___x_2639_, sizeof(void*)*4, v___x_2638_);
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2642_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2639_, 3);
v___x_2643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2639_);
lean_ctor_set(v___x_2643_, 1, v_cmdState_2508_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
v___x_2644_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2636_, v___x_2643_);
v___x_2645_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2636_, v___x_2639_);
v___x_2646_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2639_);
lean_ctor_set(v___x_2647_, 1, v___x_2641_);
lean_ctor_set(v___x_2647_, 2, v___x_2644_);
lean_ctor_set(v___x_2647_, 3, v___x_2645_);
lean_ctor_set(v___x_2647_, 4, v___x_2646_);
v___x_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2639_);
lean_ctor_set(v___x_2648_, 1, v___x_2640_);
lean_ctor_set(v___x_2648_, 2, v___y_2617_);
lean_ctor_set(v___x_2648_, 3, v___x_2647_);
lean_ctor_set(v___x_2648_, 4, v___x_2636_);
v___x_2649_ = lean_io_promise_resolve(v___x_2648_, v_prom_2509_);
lean_dec(v_prom_2509_);
v___x_2650_ = lean_box(0);
return v___x_2650_;
}
v___jp_2651_:
{
v___y_2615_ = v___y_2652_;
v___y_2616_ = v___y_2653_;
v___y_2617_ = v___y_2654_;
goto v___jp_2614_;
}
v___jp_2656_:
{
uint8_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = l_IO_CancelToken_isSet(v_parseCancelTk_2511_);
v___x_2668_ = 1;
if (v___x_2667_ == 0)
{
lean_dec(v___y_2665_);
if (v_sync_2510_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2669_ = lean_io_promise_new();
v___x_2670_ = lean_io_promise_new();
v___x_2671_ = lean_io_promise_new();
v___x_2672_ = lean_io_promise_new();
v___x_2673_ = l_Lean_internal_cmdlineSnapshots;
v___x_2674_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2663_, v___x_2673_);
lean_dec_ref(v___y_2663_);
if (v___x_2674_ == 0)
{
lean_inc(v___y_2664_);
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___x_2671_;
v___y_2589_ = v___y_2659_;
v___y_2590_ = v___x_2668_;
v___y_2591_ = v___x_2669_;
v___y_2592_ = v___y_2661_;
v___y_2593_ = v___y_2662_;
v___y_2594_ = v___x_2673_;
v___y_2595_ = v___y_2658_;
v___y_2596_ = v___x_2667_;
v___y_2597_ = v___x_2672_;
v___y_2598_ = v___y_2660_;
v___y_2599_ = v___x_2670_;
v___y_2600_ = v___y_2664_;
v_fst_2601_ = v___y_2664_;
v_snd_2602_ = v___y_2666_;
goto v___jp_2586_;
}
else
{
uint8_t v___x_2675_; 
lean_inc(v___y_2664_);
v___x_2675_ = l_Lean_Parser_isTerminalCommand(v___y_2664_);
if (v___x_2675_ == 0)
{
if (v___x_2674_ == 0)
{
lean_inc(v___y_2664_);
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___x_2671_;
v___y_2589_ = v___y_2659_;
v___y_2590_ = v___x_2668_;
v___y_2591_ = v___x_2669_;
v___y_2592_ = v___y_2661_;
v___y_2593_ = v___y_2662_;
v___y_2594_ = v___x_2673_;
v___y_2595_ = v___y_2658_;
v___y_2596_ = v___x_2667_;
v___y_2597_ = v___x_2672_;
v___y_2598_ = v___y_2660_;
v___y_2599_ = v___x_2670_;
v___y_2600_ = v___y_2664_;
v_fst_2601_ = v___y_2664_;
v_snd_2602_ = v___y_2666_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec_ref(v___y_2666_);
v___x_2676_ = lean_box(0);
v___x_2677_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___x_2671_;
v___y_2589_ = v___y_2659_;
v___y_2590_ = v___x_2668_;
v___y_2591_ = v___x_2669_;
v___y_2592_ = v___y_2661_;
v___y_2593_ = v___y_2662_;
v___y_2594_ = v___x_2673_;
v___y_2595_ = v___y_2658_;
v___y_2596_ = v___x_2667_;
v___y_2597_ = v___x_2672_;
v___y_2598_ = v___y_2660_;
v___y_2599_ = v___x_2670_;
v___y_2600_ = v___y_2664_;
v_fst_2601_ = v___x_2676_;
v_snd_2602_ = v___x_2677_;
goto v___jp_2586_;
}
}
else
{
lean_inc(v___y_2664_);
v___y_2587_ = v___y_2657_;
v___y_2588_ = v___x_2671_;
v___y_2589_ = v___y_2659_;
v___y_2590_ = v___x_2668_;
v___y_2591_ = v___x_2669_;
v___y_2592_ = v___y_2661_;
v___y_2593_ = v___y_2662_;
v___y_2594_ = v___x_2673_;
v___y_2595_ = v___y_2658_;
v___y_2596_ = v___x_2667_;
v___y_2597_ = v___x_2672_;
v___y_2598_ = v___y_2660_;
v___y_2599_ = v___x_2670_;
v___y_2600_ = v___y_2664_;
v_fst_2601_ = v___y_2664_;
v_snd_2602_ = v___y_2666_;
goto v___jp_2586_;
}
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
v___x_2678_ = lean_box(v___x_2667_);
v___x_2679_ = lean_box(v___x_2668_);
lean_inc_ref(v_a_2513_);
v___f_2680_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2680_, 0, v___y_2660_);
lean_closure_set(v___f_2680_, 1, v_revCmds_2512_);
lean_closure_set(v___f_2680_, 2, v___y_2662_);
lean_closure_set(v___f_2680_, 3, v___x_2678_);
lean_closure_set(v___f_2680_, 4, v_a_2513_);
lean_closure_set(v___f_2680_, 5, v___y_2659_);
lean_closure_set(v___f_2680_, 6, v___y_2661_);
lean_closure_set(v___f_2680_, 7, v___x_2679_);
lean_closure_set(v___f_2680_, 8, v___x_2559_);
lean_closure_set(v___f_2680_, 9, v___f_2558_);
lean_closure_set(v___f_2680_, 10, v___f_2557_);
lean_closure_set(v___f_2680_, 11, v___f_2556_);
lean_closure_set(v___f_2680_, 12, v___y_2657_);
lean_closure_set(v___f_2680_, 13, v_cmdState_2508_);
lean_closure_set(v___f_2680_, 14, v___x_2560_);
lean_closure_set(v___f_2680_, 15, v___y_2658_);
lean_closure_set(v___f_2680_, 16, v_prom_2509_);
lean_closure_set(v___f_2680_, 17, v_old_x3f_2506_);
lean_closure_set(v___f_2680_, 18, v_parseCancelTk_2511_);
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = lean_io_as_task(v___f_2680_, v___x_2681_);
lean_dec_ref(v___x_2682_);
goto v___jp_2515_;
}
}
else
{
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v_revCmds_2512_);
lean_dec_ref(v_parseCancelTk_2511_);
if (lean_obj_tag(v_old_x3f_2506_) == 1)
{
lean_object* v_val_2683_; lean_object* v___x_2684_; lean_object* v_children_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v_val_2683_ = lean_ctor_get(v_old_x3f_2506_, 0);
lean_inc(v_val_2683_);
lean_dec_ref_known(v_old_x3f_2506_, 1);
v___x_2684_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2683_);
v_children_2685_ = lean_ctor_get(v___x_2684_, 1);
lean_inc_ref(v_children_2685_);
lean_dec_ref(v___x_2684_);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_array_get_size(v_children_2685_);
v___x_2688_ = lean_nat_dec_lt(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_dec_ref(v_children_2685_);
v___y_2615_ = v___x_2668_;
v___y_2616_ = v___y_2665_;
v___y_2617_ = v___y_2666_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_nat_dec_le(v___x_2687_, v___x_2687_);
if (v___x_2690_ == 0)
{
if (v___x_2688_ == 0)
{
lean_dec_ref(v_children_2685_);
v___y_2615_ = v___x_2668_;
v___y_2616_ = v___y_2665_;
v___y_2617_ = v___y_2666_;
goto v___jp_2614_;
}
else
{
size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = lean_usize_of_nat(v___x_2687_);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2685_, v___x_2691_, v___x_2692_, v___x_2689_);
lean_dec_ref(v_children_2685_);
v___y_2652_ = v___x_2668_;
v___y_2653_ = v___y_2665_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v___x_2693_;
goto v___jp_2651_;
}
}
else
{
size_t v___x_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = ((size_t)0ULL);
v___x_2695_ = lean_usize_of_nat(v___x_2687_);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2685_, v___x_2694_, v___x_2695_, v___x_2689_);
lean_dec_ref(v_children_2685_);
v___y_2652_ = v___x_2668_;
v___y_2653_ = v___y_2665_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v___x_2696_;
goto v___jp_2651_;
}
}
}
else
{
lean_dec(v_old_x3f_2506_);
v___y_2615_ = v___x_2668_;
v___y_2616_ = v___y_2665_;
v___y_2617_ = v___y_2666_;
goto v___jp_2614_;
}
}
}
v___jp_2698_:
{
lean_object* v_env_2699_; lean_object* v_scopes_2700_; lean_object* v___x_2701_; lean_object* v_opts_2702_; lean_object* v_currNamespace_2703_; lean_object* v_openDecls_2704_; lean_object* v___x_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v_snd_2710_; 
v_env_2699_ = lean_ctor_get(v_cmdState_2508_, 0);
v_scopes_2700_ = lean_ctor_get(v_cmdState_2508_, 2);
v___x_2701_ = l_List_head_x21___redArg(v___x_2559_, v_scopes_2700_);
v_opts_2702_ = lean_ctor_get(v___x_2701_, 1);
lean_inc_ref_n(v_opts_2702_, 2);
v_currNamespace_2703_ = lean_ctor_get(v___x_2701_, 2);
lean_inc(v_currNamespace_2703_);
v_openDecls_2704_ = lean_ctor_get(v___x_2701_, 3);
lean_inc(v_openDecls_2704_);
lean_dec(v___x_2701_);
lean_inc_ref(v_env_2699_);
v___x_2705_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2705_, 0, v_env_2699_);
lean_ctor_set(v___x_2705_, 1, v_opts_2702_);
lean_ctor_set(v___x_2705_, 2, v_currNamespace_2703_);
lean_ctor_set(v___x_2705_, 3, v_openDecls_2704_);
lean_inc_ref(v_parserState_2507_);
lean_inc_ref(v_a_2513_);
v___f_2706_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2706_, 0, v_a_2513_);
lean_closure_set(v___f_2706_, 1, v___x_2705_);
lean_closure_set(v___f_2706_, 2, v_parserState_2507_);
v___x_2707_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_profileit(v___x_2707_, v_opts_2702_, v___f_2706_, v___x_2708_);
v_snd_2710_ = lean_ctor_get(v___x_2709_, 1);
lean_inc(v_snd_2710_);
if (lean_obj_tag(v_old_x3f_2506_) == 1)
{
lean_object* v_val_2711_; lean_object* v_fst_2712_; lean_object* v_fst_2713_; lean_object* v_snd_2714_; lean_object* v_pos_2715_; lean_object* v_toSnapshot_2716_; lean_object* v_stx_2717_; lean_object* v_parserState_2718_; lean_object* v_elabSnap_2719_; lean_object* v_nextCmdSnap_x3f_2720_; uint8_t v___x_2721_; 
v_val_2711_ = lean_ctor_get(v_old_x3f_2506_, 0);
v_fst_2712_ = lean_ctor_get(v___x_2709_, 0);
lean_inc_n(v_fst_2712_, 2);
lean_dec(v___x_2709_);
v_fst_2713_ = lean_ctor_get(v_snd_2710_, 0);
lean_inc(v_fst_2713_);
v_snd_2714_ = lean_ctor_get(v_snd_2710_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_snd_2710_);
v_pos_2715_ = lean_ctor_get(v_parserState_2507_, 0);
lean_inc(v_pos_2715_);
lean_dec_ref(v_parserState_2507_);
v_toSnapshot_2716_ = lean_ctor_get(v_val_2711_, 0);
v_stx_2717_ = lean_ctor_get(v_val_2711_, 1);
v_parserState_2718_ = lean_ctor_get(v_val_2711_, 2);
v_elabSnap_2719_ = lean_ctor_get(v_val_2711_, 3);
v_nextCmdSnap_x3f_2720_ = lean_ctor_get(v_val_2711_, 4);
lean_inc(v_stx_2717_);
v___x_2721_ = l_Lean_Syntax_eqWithInfo(v_fst_2712_, v_stx_2717_);
if (v___x_2721_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2720_) == 0)
{
lean_inc(v_fst_2713_);
lean_inc(v_fst_2712_);
lean_inc_ref(v_opts_2702_);
v___y_2657_ = v_pos_2715_;
v___y_2658_ = v_opts_2702_;
v___y_2659_ = v_snd_2714_;
v___y_2660_ = v_fst_2712_;
v___y_2661_ = v___x_2708_;
v___y_2662_ = v_fst_2713_;
v___y_2663_ = v_opts_2702_;
v___y_2664_ = v_fst_2712_;
v___y_2665_ = v___x_2708_;
v___y_2666_ = v_fst_2713_;
goto v___jp_2656_;
}
else
{
lean_object* v_val_2722_; lean_object* v___x_2723_; 
v_val_2722_ = lean_ctor_get(v_nextCmdSnap_x3f_2720_, 0);
lean_inc(v_val_2722_);
v___x_2723_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2697_, v_val_2722_);
lean_inc(v_fst_2713_);
lean_inc(v_fst_2712_);
lean_inc_ref(v_opts_2702_);
v___y_2657_ = v_pos_2715_;
v___y_2658_ = v_opts_2702_;
v___y_2659_ = v_snd_2714_;
v___y_2660_ = v_fst_2712_;
v___y_2661_ = v___x_2708_;
v___y_2662_ = v_fst_2713_;
v___y_2663_ = v_opts_2702_;
v___y_2664_ = v_fst_2712_;
v___y_2665_ = v___x_2708_;
v___y_2666_ = v_fst_2713_;
goto v___jp_2656_;
}
}
else
{
lean_inc(v_val_2711_);
lean_dec(v_pos_2715_);
lean_dec(v_snd_2714_);
lean_dec(v_fst_2712_);
lean_dec_ref_known(v_old_x3f_2506_, 1);
lean_dec_ref(v_opts_2702_);
lean_dec_ref(v_parseCancelTk_2511_);
lean_dec_ref(v_cmdState_2508_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2720_) == 1)
{
lean_object* v_val_2724_; 
lean_inc_ref(v_nextCmdSnap_x3f_2720_);
lean_inc_ref(v_elabSnap_2719_);
lean_inc_ref(v_parserState_2718_);
lean_inc(v_stx_2717_);
lean_inc_ref(v_toSnapshot_2716_);
lean_dec(v_val_2711_);
v_val_2724_ = lean_ctor_get(v_nextCmdSnap_x3f_2720_, 0);
lean_inc(v_val_2724_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2720_, 1);
v_toSnapshot_2520_ = v_toSnapshot_2716_;
v_stx_2521_ = v_stx_2717_;
v_parserState_2522_ = v_parserState_2718_;
v_elabSnap_2523_ = v_elabSnap_2719_;
v_val_2524_ = v_val_2724_;
v_newParserState_2525_ = v_fst_2713_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2725_; 
lean_dec(v_fst_2713_);
lean_dec(v_revCmds_2512_);
v___x_2725_ = lean_io_promise_resolve(v_val_2711_, v_prom_2509_);
lean_dec(v_prom_2509_);
return v___x_2725_;
}
}
}
else
{
lean_object* v_fst_2726_; lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v_pos_2729_; 
v_fst_2726_ = lean_ctor_get(v___x_2709_, 0);
lean_inc_n(v_fst_2726_, 2);
lean_dec(v___x_2709_);
v_fst_2727_ = lean_ctor_get(v_snd_2710_, 0);
lean_inc_n(v_fst_2727_, 2);
v_snd_2728_ = lean_ctor_get(v_snd_2710_, 1);
lean_inc(v_snd_2728_);
lean_dec(v_snd_2710_);
v_pos_2729_ = lean_ctor_get(v_parserState_2507_, 0);
lean_inc(v_pos_2729_);
lean_dec_ref(v_parserState_2507_);
lean_inc_ref(v_opts_2702_);
v___y_2657_ = v_pos_2729_;
v___y_2658_ = v_opts_2702_;
v___y_2659_ = v_snd_2728_;
v___y_2660_ = v_fst_2726_;
v___y_2661_ = v___x_2708_;
v___y_2662_ = v_fst_2727_;
v___y_2663_ = v_opts_2702_;
v___y_2664_ = v_fst_2726_;
v___y_2665_ = v___x_2708_;
v___y_2666_ = v_fst_2727_;
goto v___jp_2656_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_old_x3f_2506_ = stack[0].m_obj;
lean_object* v_parserState_2507_ = stack[1].m_obj;
lean_object* v_cmdState_2508_ = stack[2].m_obj;
lean_object* v_prom_2509_ = stack[3].m_obj;
uint8_t v_sync_2510_ = stack[4].m_num;
lean_object* v_parseCancelTk_2511_ = stack[5].m_obj;
lean_object* v_revCmds_2512_ = stack[6].m_obj;
lean_object* v_a_2513_ = stack[7].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2506_, v_parserState_2507_, v_cmdState_2508_, v_prom_2509_, v_sync_2510_, v_parseCancelTk_2511_, v_revCmds_2512_, v_a_2513_);
stack->m_obj
 = v_res_2746_;
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2747_, lean_object* v_stx_2748_, lean_object* v_revCmds_2749_, lean_object* v_newParserState_2750_, lean_object* v_val_2751_, uint8_t v_sync_2752_, lean_object* v_val_2753_, lean_object* v_a_2754_, lean_object* v_oldNext_2755_){
_start:
{
lean_object* v_cmdState_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v_cmdState_2757_ = lean_ctor_get(v_oldResult_2747_, 1);
lean_inc_ref(v_cmdState_2757_);
lean_dec_ref(v_oldResult_2747_);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_oldNext_2755_);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_stx_2748_);
lean_ctor_set(v___x_2759_, 1, v_revCmds_2749_);
v___x_2760_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2758_, v_newParserState_2750_, v_cmdState_2757_, v_val_2751_, v_sync_2752_, v_val_2753_, v___x_2759_, v_a_2754_);
return v___x_2760_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldResult_2747_ = stack[0].m_obj;
lean_object* v_stx_2748_ = stack[1].m_obj;
lean_object* v_revCmds_2749_ = stack[2].m_obj;
lean_object* v_newParserState_2750_ = stack[3].m_obj;
lean_object* v_val_2751_ = stack[4].m_obj;
uint8_t v_sync_2752_ = stack[5].m_num;
lean_object* v_val_2753_ = stack[6].m_obj;
lean_object* v_a_2754_ = stack[7].m_obj;
lean_object* v_oldNext_2755_ = stack[8].m_obj;
lean_object* v_res_2761_;
v_res_2761_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_2747_, v_stx_2748_, v_revCmds_2749_, v_newParserState_2750_, v_val_2751_, v_sync_2752_, v_val_2753_, v_a_2754_, v_oldNext_2755_);
stack->m_obj
 = v_res_2761_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2762_ = _args[0];
lean_object* v_val_2763_ = _args[1];
lean_object* v_fst_2764_ = _args[2];
lean_object* v_revCmds_2765_ = _args[3];
lean_object* v_fst_2766_ = _args[4];
lean_object* v_val_2767_ = _args[5];
lean_object* v_a_2768_ = _args[6];
lean_object* v_snd_2769_ = _args[7];
lean_object* v___x_2770_ = _args[8];
lean_object* v___x_2771_ = _args[9];
lean_object* v_fst_2772_ = _args[10];
lean_object* v_val_2773_ = _args[11];
lean_object* v_val_2774_ = _args[12];
lean_object* v___x_2775_ = _args[13];
lean_object* v___f_2776_ = _args[14];
lean_object* v___f_2777_ = _args[15];
lean_object* v___f_2778_ = _args[16];
lean_object* v_pos_2779_ = _args[17];
lean_object* v_cmdState_2780_ = _args[18];
lean_object* v_val_2781_ = _args[19];
lean_object* v___x_2782_ = _args[20];
lean_object* v_opts_2783_ = _args[21];
lean_object* v___x_2784_ = _args[22];
lean_object* v_snd_2785_ = _args[23];
lean_object* v_prom_2786_ = _args[24];
lean_object* v_old_x3f_2787_ = _args[25];
lean_object* v_parseCancelTk_2788_ = _args[26];
lean_object* v_next_x3f_2789_ = _args[27];
lean_object* v___y_2790_ = _args[28];
_start:
{
uint8_t v_val_37797__boxed_2791_; uint8_t v___x_37800__boxed_2792_; lean_object* v_res_2793_; 
v_val_37797__boxed_2791_ = lean_unbox(v_val_2767_);
v___x_37800__boxed_2792_ = lean_unbox(v___x_2771_);
v_res_2793_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2762_, v_val_2763_, v_fst_2764_, v_revCmds_2765_, v_fst_2766_, v_val_37797__boxed_2791_, v_a_2768_, v_snd_2769_, v___x_2770_, v___x_37800__boxed_2792_, v_fst_2772_, v_val_2773_, v_val_2774_, v___x_2775_, v___f_2776_, v___f_2777_, v___f_2778_, v_pos_2779_, v_cmdState_2780_, v_val_2781_, v___x_2782_, v_opts_2783_, v___x_2784_, v_snd_2785_, v_prom_2786_, v_old_x3f_2787_, v_parseCancelTk_2788_, v_next_x3f_2789_);
lean_dec(v_prom_2786_);
lean_dec_ref(v___x_2784_);
lean_dec_ref(v_opts_2783_);
lean_dec(v_val_2774_);
lean_dec_ref(v_a_2768_);
lean_dec(v_val_2763_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2794_, lean_object* v_parserState_2795_, lean_object* v_cmdState_2796_, lean_object* v_prom_2797_, lean_object* v_sync_2798_, lean_object* v_parseCancelTk_2799_, lean_object* v_revCmds_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
uint8_t v_sync_boxed_2803_; lean_object* v_res_2804_; 
v_sync_boxed_2803_ = lean_unbox(v_sync_2798_);
v_res_2804_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2794_, v_parserState_2795_, v_cmdState_2796_, v_prom_2797_, v_sync_boxed_2803_, v_parseCancelTk_2799_, v_revCmds_2800_, v_a_2801_);
lean_dec_ref(v_a_2801_);
return v_res_2804_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2805_, size_t v_i_2806_, size_t v_stop_2807_, lean_object* v_b_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2805_, v_i_2806_, v_stop_2807_, v_b_2808_);
return v___x_2811_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2805_ = stack[0].m_obj;
size_t v_i_2806_ = stack[1].m_num;
size_t v_stop_2807_ = stack[2].m_num;
lean_object* v_b_2808_ = stack[3].m_obj;
lean_object* v___y_2809_ = stack[4].m_obj;
lean_object* v_res_2812_;
v_res_2812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2805_, v_i_2806_, v_stop_2807_, v_b_2808_, v___y_2809_);
stack->m_obj
 = v_res_2812_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2813_, lean_object* v_i_2814_, lean_object* v_stop_2815_, lean_object* v_b_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
size_t v_i_boxed_2819_; size_t v_stop_boxed_2820_; lean_object* v_res_2821_; 
v_i_boxed_2819_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_stop_boxed_2820_ = lean_unbox_usize(v_stop_2815_);
lean_dec(v_stop_2815_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2813_, v_i_boxed_2819_, v_stop_boxed_2820_, v_b_2816_, v___y_2817_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v_as_2813_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2822_, lean_object* v_opt_2823_){
_start:
{
lean_object* v_name_2824_; lean_object* v_map_2825_; lean_object* v___x_2826_; 
v_name_2824_ = lean_ctor_get(v_opt_2823_, 0);
v_map_2825_ = lean_ctor_get(v_opts_2822_, 0);
v___x_2826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2825_, v_name_2824_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_box(0);
return v___x_2827_;
}
else
{
lean_object* v_val_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2837_; 
v_val_2828_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2830_ = v___x_2826_;
v_isShared_2831_ = v_isSharedCheck_2837_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_val_2828_);
lean_dec(v___x_2826_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2837_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
if (lean_obj_tag(v_val_2828_) == 0)
{
lean_object* v_v_2832_; lean_object* v___x_2834_; 
v_v_2832_ = lean_ctor_get(v_val_2828_, 0);
lean_inc_ref(v_v_2832_);
lean_dec_ref_known(v_val_2828_, 1);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v_v_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_v_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
else
{
lean_object* v___x_2836_; 
lean_del_object(v___x_2830_);
lean_dec(v_val_2828_);
v___x_2836_ = lean_box(0);
return v___x_2836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2838_, lean_object* v_opt_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2838_, v_opt_2839_);
lean_dec_ref(v_opt_2839_);
lean_dec_ref(v_opts_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2841_, lean_object* v_x_2842_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2841_);
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2845_, 0, v_x_2842_);
lean_ctor_set(v___x_2845_, 1, v___x_2843_);
lean_ctor_set(v___x_2845_, 2, v___x_2844_);
return v___x_2845_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2852_ = l_Lean_Array_toPArray_x27___redArg(v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
if (lean_obj_tag(v_a_2853_) == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = l_List_reverse___redArg(v_a_2854_);
return v___x_2855_;
}
else
{
lean_object* v_head_2856_; lean_object* v_tail_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2870_; 
v_head_2856_ = lean_ctor_get(v_a_2853_, 0);
v_tail_2857_ = lean_ctor_get(v_a_2853_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2859_ = v_a_2853_;
v_isShared_2860_ = v_isSharedCheck_2870_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_tail_2857_);
lean_inc(v_head_2856_);
lean_dec(v_a_2853_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2870_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2861_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v_head_2856_);
v___x_2863_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
v___x_2864_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v_a_2854_);
lean_ctor_set(v___x_2859_, 0, v___x_2865_);
v___x_2867_ = v___x_2859_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_a_2854_);
v___x_2867_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
v_a_2853_ = v_tail_2857_;
v_a_2854_ = v___x_2867_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2871_; double v___x_2872_; 
v___x_2871_ = lean_unsigned_to_nat(1000000000u);
v___x_2872_ = lean_float_of_nat(v___x_2871_);
return v___x_2872_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2890_ = l_Lean_MessageData_ofFormat(v___x_2889_);
return v___x_2890_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2891_, lean_object* v_stx_2892_, lean_object* v_origStx_2893_, lean_object* v_toProcessingContext_2894_, lean_object* v___x_2895_, lean_object* v_fileMap_2896_, lean_object* v_parserState_2897_, lean_object* v_a_2898_, lean_object* v___x_2899_, lean_object* v___x_2900_, lean_object* v___x_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_toProcessingContext_2904_; lean_object* v___x_2905_; 
v_toProcessingContext_2904_ = lean_ctor_get(v___y_2902_, 0);
lean_inc_ref(v_toProcessingContext_2904_);
lean_inc(v_stx_2892_);
v___x_2905_ = lean_apply_3(v_setupImports_2891_, v_stx_2892_, v_toProcessingContext_2904_, lean_box(0));
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_3119_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_3119_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_3119_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
if (lean_obj_tag(v_a_2906_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; 
lean_dec_ref(v___x_2901_);
lean_dec(v___x_2899_);
lean_dec_ref(v_parserState_2897_);
lean_dec_ref(v_fileMap_2896_);
lean_dec(v___x_2895_);
lean_dec_ref(v_toProcessingContext_2894_);
lean_dec(v_origStx_2893_);
lean_dec(v_stx_2892_);
v_a_2910_ = lean_ctor_get(v_a_2906_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v_a_2906_, 1);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v_a_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_3118_; 
v_a_2914_ = lean_ctor_get(v_a_2906_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_2906_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_2916_ = v_a_2906_;
v_isShared_2917_ = v_isSharedCheck_3118_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v_a_2906_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_3118_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v_mainModuleName_2919_; lean_object* v_package_x3f_2920_; uint8_t v_isModule_2921_; lean_object* v_imports_2922_; lean_object* v_opts_2923_; uint32_t v_trustLevel_2924_; lean_object* v_importArts_2925_; lean_object* v_plugins_2926_; double v___x_2927_; double v___x_2928_; double v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; lean_object* v___x_2934_; 
v___x_2918_ = lean_io_mono_nanos_now();
v_mainModuleName_2919_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_mainModuleName_2919_);
v_package_x3f_2920_ = lean_ctor_get(v_a_2914_, 1);
lean_inc(v_package_x3f_2920_);
v_isModule_2921_ = lean_ctor_get_uint8(v_a_2914_, sizeof(void*)*6 + 4);
v_imports_2922_ = lean_ctor_get(v_a_2914_, 2);
lean_inc_ref(v_imports_2922_);
v_opts_2923_ = lean_ctor_get(v_a_2914_, 3);
lean_inc_ref(v_opts_2923_);
v_trustLevel_2924_ = lean_ctor_get_uint32(v_a_2914_, sizeof(void*)*6);
v_importArts_2925_ = lean_ctor_get(v_a_2914_, 4);
lean_inc(v_importArts_2925_);
v_plugins_2926_ = lean_ctor_get(v_a_2914_, 5);
lean_inc_ref(v_plugins_2926_);
lean_dec(v_a_2914_);
v___x_2927_ = lean_float_of_nat(v___x_2918_);
v___x_2928_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2929_ = lean_float_div(v___x_2927_, v___x_2928_);
v___x_2930_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2892_);
v___x_2931_ = l_Lean_MessageLog_empty;
v___x_2932_ = 1;
lean_inc(v_stx_2892_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v_stx_2892_);
v___x_2934_ = v___x_2916_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_stx_2892_);
v___x_2934_ = v_reuseFailAlloc_3117_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_origStx_2893_);
lean_inc_ref(v___x_2934_);
lean_inc_ref(v_opts_2923_);
v___x_2936_ = l_Lean_Elab_processHeaderCore(v___x_2930_, v_imports_2922_, v_isModule_2921_, v_opts_2923_, v___x_2931_, v_toProcessingContext_2894_, v_trustLevel_2924_, v_plugins_2926_, v___x_2932_, v_mainModuleName_2919_, v_package_x3f_2920_, v_importArts_2925_, v___x_2934_, v___x_2935_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3108_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_3108_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3108_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_fst_2941_; lean_object* v_snd_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_3107_; 
v_fst_2941_ = lean_ctor_get(v_a_2937_, 0);
v_snd_2942_ = lean_ctor_get(v_a_2937_, 1);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_a_2937_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_2944_ = v_a_2937_;
v_isShared_2945_ = v_isSharedCheck_3107_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_snd_2942_);
lean_inc(v_fst_2941_);
lean_dec(v_a_2937_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_3107_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; double v___x_2947_; double v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v_traceState_2966_; 
v___x_2946_ = lean_io_mono_nanos_now();
v___x_2947_ = lean_float_of_nat(v___x_2946_);
v___x_2948_ = lean_float_div(v___x_2947_, v___x_2928_);
lean_inc(v_snd_2942_);
v___x_2949_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2942_);
v___x_2950_ = l_Lean_MessageLog_hasErrors(v_snd_2942_);
if (v___x_2950_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_del_object(v___x_2908_);
lean_dec_ref(v___x_2901_);
v___x_3076_ = l_Lean_trace_profiler_output;
v___x_3077_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2923_, v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = l_Lean_trace_profiler_serve;
v___x_3079_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2923_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2966_ = v___x_3080_;
goto v___jp_2965_;
}
else
{
goto v___jp_3060_;
}
}
else
{
lean_dec_ref_known(v___x_3077_, 1);
goto v___jp_3060_;
}
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint64_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
lean_del_object(v___x_2944_);
lean_dec(v_snd_2942_);
lean_dec(v_fst_2941_);
lean_del_object(v___x_2939_);
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_opts_2923_);
lean_dec(v___x_2899_);
lean_dec_ref(v_parserState_2897_);
lean_dec_ref(v_fileMap_2896_);
lean_dec(v_stx_2892_);
v___x_3081_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3082_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3083_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2895_, 2);
v___x_3084_ = l_Lean_Name_num___override(v___x_3083_, v___x_2895_);
v___x_3085_ = l_Lean_Name_str___override(v___x_3084_, v___x_3081_);
v___x_3086_ = l_Lean_Name_str___override(v___x_3085_, v___x_3082_);
v___x_3087_ = l_Lean_Name_str___override(v___x_3086_, v___x_3081_);
v___x_3088_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3089_ = l_Lean_Name_str___override(v___x_3087_, v___x_3088_);
v___x_3090_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3091_ = l_Lean_Name_str___override(v___x_3089_, v___x_3090_);
v___x_3092_ = l_Lean_Name_toString(v___x_3091_, v___x_2932_);
v___x_3093_ = lean_box(0);
v___x_3094_ = 0ULL;
v___x_3095_ = lean_unsigned_to_nat(32u);
v___x_3096_ = lean_mk_empty_array_with_capacity(v___x_3095_);
v___x_3097_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3098_ = ((size_t)5ULL);
v___x_3099_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3096_);
lean_ctor_set(v___x_3099_, 2, v___x_2895_);
lean_ctor_set(v___x_3099_, 3, v___x_2895_);
lean_ctor_set_usize(v___x_3099_, 4, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set_uint64(v___x_3100_, sizeof(void*)*1, v___x_3094_);
v___x_3101_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3101_, 0, v___x_3092_);
lean_ctor_set(v___x_3101_, 1, v___x_2949_);
lean_ctor_set(v___x_3101_, 2, v___x_3093_);
lean_ctor_set(v___x_3101_, 3, v___x_3100_);
lean_ctor_set_uint8(v___x_3101_, sizeof(void*)*4, v___x_2950_);
v___x_3102_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2901_);
v___x_3103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
lean_ctor_set(v___x_3103_, 2, v___x_3093_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_3103_);
v___x_3105_ = v___x_2908_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
v___jp_2951_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___y_2957_);
v___x_2959_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2959_, 0, v___y_2956_);
lean_ctor_set(v___x_2959_, 1, v___x_2949_);
lean_ctor_set(v___x_2959_, 2, v___x_2958_);
lean_ctor_set(v___x_2959_, 3, v___y_2954_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*4, v___x_2950_);
v___x_2960_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2955_, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2952_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
lean_ctor_set(v___x_2961_, 2, v___y_2953_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2961_);
v___x_2963_ = v___x_2939_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
v___jp_2965_:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Language_Lean_reparseOptions(v_opts_2923_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; lean_object* v_env_2970_; lean_object* v_messages_2971_; lean_object* v_scopes_2972_; lean_object* v_usedQuotCtxts_2973_; lean_object* v_nextMacroScope_2974_; lean_object* v_maxRecDepth_2975_; lean_object* v_ngen_2976_; lean_object* v_auxDeclNGen_2977_; lean_object* v_snapshotTasks_2978_; lean_object* v_prevLinterStates_2979_; lean_object* v_codeQualityEntryTasks_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3049_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
lean_inc(v_fst_2941_);
v___x_2969_ = l_Lean_Elab_Command_mkState(v_fst_2941_, v_snd_2942_, v_a_2968_);
v_env_2970_ = lean_ctor_get(v___x_2969_, 0);
v_messages_2971_ = lean_ctor_get(v___x_2969_, 1);
v_scopes_2972_ = lean_ctor_get(v___x_2969_, 2);
v_usedQuotCtxts_2973_ = lean_ctor_get(v___x_2969_, 3);
v_nextMacroScope_2974_ = lean_ctor_get(v___x_2969_, 4);
v_maxRecDepth_2975_ = lean_ctor_get(v___x_2969_, 5);
v_ngen_2976_ = lean_ctor_get(v___x_2969_, 6);
v_auxDeclNGen_2977_ = lean_ctor_get(v___x_2969_, 7);
v_snapshotTasks_2978_ = lean_ctor_get(v___x_2969_, 10);
v_prevLinterStates_2979_ = lean_ctor_get(v___x_2969_, 11);
v_codeQualityEntryTasks_2980_ = lean_ctor_get(v___x_2969_, 12);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; lean_object* v_unused_3051_; 
v_unused_3050_ = lean_ctor_get(v___x_2969_, 9);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v___x_2969_, 8);
lean_dec(v_unused_3051_);
v___x_2982_ = v___x_2969_;
v_isShared_2983_ = v_isSharedCheck_3049_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2980_);
lean_inc(v_prevLinterStates_2979_);
lean_inc(v_snapshotTasks_2978_);
lean_inc(v_auxDeclNGen_2977_);
lean_inc(v_ngen_2976_);
lean_inc(v_maxRecDepth_2975_);
lean_inc(v_nextMacroScope_2974_);
lean_inc(v_usedQuotCtxts_2973_);
lean_inc(v_scopes_2972_);
lean_inc(v_messages_2971_);
lean_inc(v_env_2970_);
lean_dec(v___x_2969_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3049_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2984_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2985_ = lean_box(0);
v___x_2986_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_inc_n(v___x_2895_, 4);
v___x_2987_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2895_);
lean_ctor_set(v___x_2987_, 1, v___x_2895_);
lean_ctor_set(v___x_2987_, 2, v___x_2895_);
lean_ctor_set(v___x_2987_, 3, v___x_2895_);
lean_ctor_set(v___x_2987_, 4, v___x_2984_);
lean_ctor_set(v___x_2987_, 5, v___x_2984_);
lean_ctor_set(v___x_2987_, 6, v___x_2984_);
lean_ctor_set(v___x_2987_, 7, v___x_2984_);
lean_ctor_set(v___x_2987_, 8, v___x_2984_);
lean_ctor_set(v___x_2987_, 9, v___x_2984_);
lean_ctor_set(v___x_2987_, 10, v___x_2984_);
lean_ctor_set(v___x_2987_, 11, v___x_2986_);
v___x_2988_ = l_Lean_Options_empty;
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2993_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2993_, 0, v_fst_2941_);
lean_ctor_set(v___x_2993_, 1, v___x_2985_);
lean_ctor_set(v___x_2993_, 2, v_fileMap_2896_);
lean_ctor_set(v___x_2993_, 3, v___x_2987_);
lean_ctor_set(v___x_2993_, 4, v___x_2988_);
lean_ctor_set(v___x_2993_, 5, v___x_2989_);
lean_ctor_set(v___x_2993_, 6, v___x_2990_);
lean_ctor_set(v___x_2993_, 7, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
v___x_2995_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2892_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_stx_2892_);
lean_ctor_set(v___x_2944_, 0, v___x_2995_);
v___x_2997_ = v___x_2944_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_stx_2892_);
v___x_2997_ = v_reuseFailAlloc_3048_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_2998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
v___x_2999_ = lean_unsigned_to_nat(2u);
v___x_3000_ = l_Lean_Syntax_getArg(v_stx_2892_, v___x_2999_);
lean_dec(v_stx_2892_);
v___x_3001_ = l_Lean_Syntax_getArgs(v___x_3000_);
lean_dec(v___x_3000_);
v___x_3002_ = lean_array_to_list(v___x_3001_);
v___x_3003_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_3002_, v___x_2990_);
v___x_3004_ = l_Lean_List_toPArray_x27___redArg(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_2998_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_2994_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_mk_empty_array_with_capacity(v___x_2991_);
v___x_3008_ = lean_array_push(v___x_3007_, v___x_3006_);
v___x_3009_ = l_Lean_Array_toPArray_x27___redArg(v___x_3008_);
lean_dec_ref(v___x_3008_);
lean_inc_ref(v___x_3009_);
v___x_3010_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3010_, 0, v___x_2984_);
lean_ctor_set(v___x_3010_, 1, v___x_2984_);
lean_ctor_set(v___x_3010_, 2, v___x_3009_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*3, v___x_2932_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 9, v_traceState_2966_);
lean_ctor_set(v___x_2982_, 8, v___x_3010_);
v___x_3012_ = v___x_2982_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_env_2970_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_messages_2971_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_scopes_2972_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_usedQuotCtxts_2973_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_nextMacroScope_2974_);
lean_ctor_set(v_reuseFailAlloc_3047_, 5, v_maxRecDepth_2975_);
lean_ctor_set(v_reuseFailAlloc_3047_, 6, v_ngen_2976_);
lean_ctor_set(v_reuseFailAlloc_3047_, 7, v_auxDeclNGen_2977_);
lean_ctor_set(v_reuseFailAlloc_3047_, 8, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3047_, 9, v_traceState_2966_);
lean_ctor_set(v_reuseFailAlloc_3047_, 10, v_snapshotTasks_2978_);
lean_ctor_set(v_reuseFailAlloc_3047_, 11, v_prevLinterStates_2979_);
lean_ctor_set(v_reuseFailAlloc_3047_, 12, v_codeQualityEntryTasks_2980_);
v___x_3012_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; lean_object* v_size_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint64_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3013_ = lean_io_promise_new();
v___x_3014_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_3014_);
lean_inc(v___x_3013_);
lean_inc_ref(v___x_3012_);
v___x_3015_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2985_, v_parserState_2897_, v___x_3012_, v___x_3013_, v___x_2932_, v___x_3014_, v___x_2990_, v_a_2898_);
v___x_3016_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3017_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3018_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2895_, 3);
v___x_3019_ = l_Lean_Name_num___override(v___x_3018_, v___x_2895_);
v___x_3020_ = lean_unsigned_to_nat(32u);
v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_3020_);
v___x_3022_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3023_ = ((size_t)5ULL);
v___x_3024_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3021_);
lean_ctor_set(v___x_3024_, 2, v___x_2895_);
lean_ctor_set(v___x_3024_, 3, v___x_2895_);
lean_ctor_set_usize(v___x_3024_, 4, v___x_3023_);
v_size_3025_ = lean_ctor_get(v___x_3009_, 2);
v___x_3026_ = l_Lean_Name_str___override(v___x_3019_, v___x_3016_);
v___x_3027_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2899_);
v___x_3028_ = l_Lean_Name_str___override(v___x_3026_, v___x_3017_);
v___x_3029_ = l_Lean_Name_str___override(v___x_3028_, v___x_3016_);
v___x_3030_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3031_ = l_Lean_Name_str___override(v___x_3029_, v___x_3030_);
v___x_3032_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3033_ = l_Lean_Name_str___override(v___x_3031_, v___x_3032_);
v___x_3034_ = l_Lean_Name_toString(v___x_3033_, v___x_2932_);
v___x_3035_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3036_ = 0ULL;
v___x_3037_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3037_, 0, v___x_3024_);
lean_ctor_set_uint64(v___x_3037_, sizeof(void*)*1, v___x_3036_);
v___x_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3014_);
v___x_3039_ = l_IO_Promise_result_x21___redArg(v___x_3013_);
lean_dec(v___x_3013_);
v___x_3040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3040_, 0, v___x_2899_);
lean_ctor_set(v___x_3040_, 1, v___x_3027_);
lean_ctor_set(v___x_3040_, 2, v___x_3038_);
lean_ctor_set(v___x_3040_, 3, v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3012_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_inc_ref(v___x_3037_);
lean_inc_ref(v___x_3034_);
v___x_3043_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3034_);
lean_ctor_set(v___x_3043_, 1, v___x_3035_);
lean_ctor_set(v___x_3043_, 2, v___x_2985_);
lean_ctor_set(v___x_3043_, 3, v___x_3037_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*4, v___x_2950_);
v___x_3044_ = lean_nat_dec_lt(v___x_2895_, v_size_3025_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
lean_dec_ref(v___x_3009_);
lean_dec(v___x_2895_);
v___x_3045_ = l_outOfBounds___redArg(v___x_2900_);
v___y_2952_ = v___x_3043_;
v___y_2953_ = v___x_3042_;
v___y_2954_ = v___x_3037_;
v___y_2955_ = v___x_2934_;
v___y_2956_ = v___x_3034_;
v___y_2957_ = v___x_3045_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2900_, v___x_3009_, v___x_2895_);
lean_dec(v___x_2895_);
lean_dec_ref(v___x_3009_);
v___y_2952_ = v___x_3043_;
v___y_2953_ = v___x_3042_;
v___y_2954_ = v___x_3037_;
v___y_2955_ = v___x_2934_;
v___y_2956_ = v___x_3034_;
v___y_2957_ = v___x_3046_;
goto v___jp_2951_;
}
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v_traceState_2966_);
lean_dec_ref(v___x_2949_);
lean_del_object(v___x_2944_);
lean_dec(v_snd_2942_);
lean_dec(v_fst_2941_);
lean_del_object(v___x_2939_);
lean_dec_ref(v___x_2934_);
lean_dec(v___x_2899_);
lean_dec_ref(v_parserState_2897_);
lean_dec_ref(v_fileMap_2896_);
lean_dec(v___x_2895_);
lean_dec(v_stx_2892_);
v_a_3052_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2967_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2967_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
v___jp_3060_:
{
uint64_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3061_ = 0ULL;
v___x_3062_ = lean_box(0);
v___x_3063_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_3064_ = lean_box(0);
v___x_3065_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3066_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3066_, 0, v___x_3063_);
lean_ctor_set(v___x_3066_, 1, v___x_3064_);
lean_ctor_set(v___x_3066_, 2, v___x_3065_);
lean_ctor_set_float(v___x_3066_, sizeof(void*)*3, v___x_2929_);
lean_ctor_set_float(v___x_3066_, sizeof(void*)*3 + 8, v___x_2948_);
lean_ctor_set_uint8(v___x_3066_, sizeof(void*)*3 + 16, v___x_2932_);
v___x_3067_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_2895_);
v___x_3069_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3066_);
lean_ctor_set(v___x_3069_, 1, v___x_3067_);
lean_ctor_set(v___x_3069_, 2, v___x_3068_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3062_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_unsigned_to_nat(1u);
v___x_3072_ = lean_mk_empty_array_with_capacity(v___x_3071_);
v___x_3073_ = lean_array_push(v___x_3072_, v___x_3070_);
v___x_3074_ = l_Lean_Array_toPArray_x27___redArg(v___x_3073_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set_uint64(v___x_3075_, sizeof(void*)*1, v___x_3061_);
v_traceState_2966_ = v___x_3075_;
goto v___jp_2965_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v___x_2934_);
lean_dec_ref(v_opts_2923_);
lean_del_object(v___x_2908_);
lean_dec_ref(v___x_2901_);
lean_dec(v___x_2899_);
lean_dec_ref(v_parserState_2897_);
lean_dec_ref(v_fileMap_2896_);
lean_dec(v___x_2895_);
lean_dec(v_stx_2892_);
v_a_3109_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2936_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2936_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
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
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v___x_2901_);
lean_dec(v___x_2899_);
lean_dec_ref(v_parserState_2897_);
lean_dec_ref(v_fileMap_2896_);
lean_dec(v___x_2895_);
lean_dec_ref(v_toProcessingContext_2894_);
lean_dec(v_origStx_2893_);
lean_dec(v_stx_2892_);
v_a_3120_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_2905_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_2905_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_setupImports_2891_ = stack[0].m_obj;
lean_object* v_stx_2892_ = stack[1].m_obj;
lean_object* v_origStx_2893_ = stack[2].m_obj;
lean_object* v_toProcessingContext_2894_ = stack[3].m_obj;
lean_object* v___x_2895_ = stack[4].m_obj;
lean_object* v_fileMap_2896_ = stack[5].m_obj;
lean_object* v_parserState_2897_ = stack[6].m_obj;
lean_object* v_a_2898_ = stack[7].m_obj;
lean_object* v___x_2899_ = stack[8].m_obj;
lean_object* v___x_2900_ = stack[9].m_obj;
lean_object* v___x_2901_ = stack[10].m_obj;
lean_object* v___y_2902_ = stack[11].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_2891_, v_stx_2892_, v_origStx_2893_, v_toProcessingContext_2894_, v___x_2895_, v_fileMap_2896_, v_parserState_2897_, v_a_2898_, v___x_2899_, v___x_2900_, v___x_2901_, v___y_2902_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3129_, lean_object* v_stx_3130_, lean_object* v_origStx_3131_, lean_object* v_toProcessingContext_3132_, lean_object* v___x_3133_, lean_object* v_fileMap_3134_, lean_object* v_parserState_3135_, lean_object* v_a_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v___x_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3129_, v_stx_3130_, v_origStx_3131_, v_toProcessingContext_3132_, v___x_3133_, v_fileMap_3134_, v_parserState_3135_, v_a_3136_, v___x_3137_, v___x_3138_, v___x_3139_, v___y_3140_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___x_3138_);
lean_dec_ref(v_a_3136_);
return v_res_3142_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___f_3144_; 
v___x_3143_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3144_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3144_, 0, v___x_3143_);
return v___f_3144_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3145_, lean_object* v_stx_3146_, lean_object* v_origStx_3147_, lean_object* v_parserState_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_toProcessingContext_3151_; lean_object* v_fileMap_3152_; lean_object* v_endPos_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_toProcessingContext_3151_ = lean_ctor_get(v_a_3149_, 0);
v_fileMap_3152_ = lean_ctor_get(v_toProcessingContext_3151_, 2);
v_endPos_3153_ = lean_ctor_get(v_toProcessingContext_3151_, 3);
v___x_3154_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3155_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3156_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3149_, 2);
lean_inc_ref(v_fileMap_3152_);
lean_inc_ref(v_toProcessingContext_3151_);
v___f_3159_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3159_, 0, v_setupImports_3145_);
lean_closure_set(v___f_3159_, 1, v_stx_3146_);
lean_closure_set(v___f_3159_, 2, v_origStx_3147_);
lean_closure_set(v___f_3159_, 3, v_toProcessingContext_3151_);
lean_closure_set(v___f_3159_, 4, v___x_3158_);
lean_closure_set(v___f_3159_, 5, v_fileMap_3152_);
lean_closure_set(v___f_3159_, 6, v_parserState_3148_);
lean_closure_set(v___f_3159_, 7, v_a_3149_);
lean_closure_set(v___f_3159_, 8, v___x_3157_);
lean_closure_set(v___f_3159_, 9, v___x_3156_);
lean_closure_set(v___f_3159_, 10, v___x_3154_);
lean_inc(v_endPos_3153_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v_endPos_3153_);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
v___x_3162_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3162_, 0, lean_box(0));
lean_closure_set(v___x_3162_, 1, v___f_3155_);
lean_closure_set(v___x_3162_, 2, v___f_3159_);
lean_closure_set(v___x_3162_, 3, v_a_3149_);
v___x_3163_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3157_, v___x_3157_, v___x_3161_, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_setupImports_3145_ = stack[0].m_obj;
lean_object* v_stx_3146_ = stack[1].m_obj;
lean_object* v_origStx_3147_ = stack[2].m_obj;
lean_object* v_parserState_3148_ = stack[3].m_obj;
lean_object* v_a_3149_ = stack[4].m_obj;
lean_object* v_res_3164_;
v_res_3164_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3145_, v_stx_3146_, v_origStx_3147_, v_parserState_3148_, v_a_3149_);
stack->m_obj
 = v_res_3164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3165_, lean_object* v_stx_3166_, lean_object* v_origStx_3167_, lean_object* v_parserState_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3165_, v_stx_3166_, v_origStx_3167_, v_parserState_3168_, v_a_3169_);
lean_dec_ref(v_a_3169_);
return v_res_3171_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_box(0);
v___x_3173_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3172_);
return v___x_3173_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = 1;
v___x_3179_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3180_ = l_Lean_Name_toString(v___x_3179_, v___x_3178_);
return v___x_3180_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3181_ = 0;
v___x_3182_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3183_ = lean_box(0);
v___x_3184_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3185_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3186_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v___x_3184_);
lean_ctor_set(v___x_3186_, 2, v___x_3183_);
lean_ctor_set(v___x_3186_, 3, v___x_3182_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*4, v___x_3181_);
return v___x_3186_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3187_, lean_object* v_cmdState_3188_, lean_object* v_a_3189_, lean_object* v_toSnapshot_3190_, lean_object* v_newStx_3191_, lean_object* v_oldCmd_3192_){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_diagnostics_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3222_; 
v___x_3194_ = lean_io_promise_new();
v___x_3195_ = l_IO_CancelToken_new();
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_oldCmd_3192_);
v___x_3197_ = 1;
v___x_3198_ = lean_box(0);
lean_inc_ref(v___x_3195_);
lean_inc(v___x_3194_);
lean_inc_ref(v_cmdState_3188_);
v___x_3199_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3196_, v_newParserState_3187_, v_cmdState_3188_, v___x_3194_, v___x_3197_, v___x_3195_, v___x_3198_, v_a_3189_);
v_diagnostics_3200_ = lean_ctor_get(v_toSnapshot_3190_, 1);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_toSnapshot_3190_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; 
v_unused_3223_ = lean_ctor_get(v_toSnapshot_3190_, 3);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_toSnapshot_3190_, 2);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_toSnapshot_3190_, 0);
lean_dec(v_unused_3225_);
v___x_3202_ = v_toSnapshot_3190_;
v_isShared_3203_ = v_isSharedCheck_3222_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_diagnostics_3200_);
lean_dec(v_toSnapshot_3190_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3222_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3206_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3207_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3195_);
v___x_3209_ = l_IO_Promise_result_x21___redArg(v___x_3194_);
lean_dec(v___x_3194_);
v___x_3210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3204_);
lean_ctor_set(v___x_3210_, 1, v___x_3205_);
lean_ctor_set(v___x_3210_, 2, v___x_3208_);
lean_ctor_set(v___x_3210_, 3, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_cmdState_3188_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = 0;
v___x_3214_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_newStx_3191_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 3, v___x_3207_);
lean_ctor_set(v___x_3202_, 2, v___x_3204_);
lean_ctor_set(v___x_3202_, 0, v___x_3206_);
v___x_3217_ = v___x_3202_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_diagnostics_3200_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v___x_3207_);
v___x_3217_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*4, v___x_3213_);
v___x_3218_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3215_, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3214_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
lean_ctor_set(v___x_3219_, 2, v___x_3212_);
v___x_3220_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3204_, v___x_3219_);
return v___x_3220_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_newParserState_3187_ = stack[0].m_obj;
lean_object* v_cmdState_3188_ = stack[1].m_obj;
lean_object* v_a_3189_ = stack[2].m_obj;
lean_object* v_toSnapshot_3190_ = stack[3].m_obj;
lean_object* v_newStx_3191_ = stack[4].m_obj;
lean_object* v_oldCmd_3192_ = stack[5].m_obj;
lean_object* v_res_3226_;
v_res_3226_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3187_, v_cmdState_3188_, v_a_3189_, v_toSnapshot_3190_, v_newStx_3191_, v_oldCmd_3192_);
stack->m_obj
 = v_res_3226_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3227_, lean_object* v_cmdState_3228_, lean_object* v_a_3229_, lean_object* v_toSnapshot_3230_, lean_object* v_newStx_3231_, lean_object* v_oldCmd_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3227_, v_cmdState_3228_, v_a_3229_, v_toSnapshot_3230_, v_newStx_3231_, v_oldCmd_3232_);
lean_dec_ref(v_a_3229_);
return v_res_3234_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3235_, lean_object* v_a_3236_, lean_object* v_newStx_3237_, lean_object* v___x_3238_, lean_object* v_oldProcessed_3239_){
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
lean_inc_ref(v_a_3236_);
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
lean_dec_ref(v_newParserState_3235_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_newStx_3237_);
v___x_3252_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3251_, v_oldProcessed_3239_);
return v___x_3252_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_newParserState_3235_ = stack[0].m_obj;
lean_object* v_a_3236_ = stack[1].m_obj;
lean_object* v_newStx_3237_ = stack[2].m_obj;
lean_object* v___x_3238_ = stack[3].m_obj;
lean_object* v_oldProcessed_3239_ = stack[4].m_obj;
lean_object* v_res_3253_;
v_res_3253_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3235_, v_a_3236_, v_newStx_3237_, v___x_3238_, v_oldProcessed_3239_);
stack->m_obj
 = v_res_3253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3254_, lean_object* v_a_3255_, lean_object* v_newStx_3256_, lean_object* v___x_3257_, lean_object* v_oldProcessed_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3254_, v_a_3255_, v_newStx_3256_, v___x_3257_, v_oldProcessed_3258_);
lean_dec_ref(v_a_3255_);
return v_res_3260_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3261_ = 0;
v___x_3262_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3263_ = lean_box(0);
v___x_3264_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3265_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3266_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set(v___x_3266_, 1, v___x_3264_);
lean_ctor_set(v___x_3266_, 2, v___x_3263_);
lean_ctor_set(v___x_3266_, 3, v___x_3262_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*4, v___x_3261_);
return v___x_3266_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3267_, lean_object* v_a_3268_, lean_object* v_old_3269_, lean_object* v_newStx_3270_, lean_object* v_newParserState_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_result_x3f_3274_; 
v_result_x3f_3274_ = lean_ctor_get(v_old_3269_, 4);
lean_inc(v_result_x3f_3274_);
if (lean_obj_tag(v_result_x3f_3274_) == 1)
{
lean_object* v_val_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3329_; 
v_val_3275_ = lean_ctor_get(v_result_x3f_3274_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_result_x3f_3274_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3277_ = v_result_x3f_3274_;
v_isShared_3278_ = v_isSharedCheck_3329_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_val_3275_);
lean_dec(v_result_x3f_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3329_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_processedSnap_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3327_; 
v_processedSnap_3279_ = lean_ctor_get(v_val_3275_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_val_3275_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v_val_3275_, 0);
lean_dec(v_unused_3328_);
v___x_3281_ = v_val_3275_;
v_isShared_3282_ = v_isSharedCheck_3327_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_processedSnap_3279_);
lean_dec(v_val_3275_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3327_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_toSnapshot_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3322_; 
v_toSnapshot_3283_ = lean_ctor_get(v_old_3269_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_old_3269_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; lean_object* v_unused_3324_; lean_object* v_unused_3325_; lean_object* v_unused_3326_; 
v_unused_3323_ = lean_ctor_get(v_old_3269_, 4);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_old_3269_, 3);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_old_3269_, 2);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_old_3269_, 1);
lean_dec(v_unused_3326_);
v___x_3285_ = v_old_3269_;
v_isShared_3286_ = v_isSharedCheck_3322_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_toSnapshot_3283_);
lean_dec(v_old_3269_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3322_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_pos_3287_; lean_object* v_endPos_3288_; lean_object* v_stx_x3f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v_diagnostics_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3318_; 
v_pos_3287_ = lean_ctor_get(v_newParserState_3271_, 0);
v_endPos_3288_ = lean_ctor_get(v_toProcessingContext_3267_, 3);
v_stx_x3f_3289_ = lean_ctor_get(v_processedSnap_3279_, 0);
lean_inc(v_stx_x3f_3289_);
lean_inc(v_endPos_3288_);
lean_inc(v_pos_3287_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_pos_3287_);
lean_ctor_set(v___x_3290_, 1, v_endPos_3288_);
v___x_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_inc_ref(v___x_3291_);
lean_inc(v_newStx_3270_);
lean_inc_ref(v_a_3268_);
lean_inc_ref(v_newParserState_3271_);
v___f_3292_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3292_, 0, v_newParserState_3271_);
lean_closure_set(v___f_3292_, 1, v_a_3268_);
lean_closure_set(v___f_3292_, 2, v_newStx_3270_);
lean_closure_set(v___f_3292_, 3, v___x_3291_);
v___x_3293_ = lean_box(0);
v___x_3294_ = 1;
v___x_3295_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3279_, v___f_3292_, v_stx_x3f_3289_, v___x_3291_, v___x_3293_, v___x_3294_);
v_diagnostics_3296_ = lean_ctor_get(v_toSnapshot_3283_, 1);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_toSnapshot_3283_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; lean_object* v_unused_3320_; lean_object* v_unused_3321_; 
v_unused_3319_ = lean_ctor_get(v_toSnapshot_3283_, 3);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_toSnapshot_3283_, 2);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_toSnapshot_3283_, 0);
lean_dec(v_unused_3321_);
v___x_3298_ = v_toSnapshot_3283_;
v_isShared_3299_ = v_isSharedCheck_3318_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_diagnostics_3296_);
lean_dec(v_toSnapshot_3283_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3318_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3300_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3301_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v___x_3295_);
lean_ctor_set(v___x_3281_, 0, v_newParserState_3271_);
v___x_3303_ = v___x_3281_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_newParserState_3271_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v___x_3295_);
v___x_3303_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3305_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3303_);
v___x_3305_ = v___x_3277_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3306_ = 0;
v___x_3307_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3270_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_newStx_3270_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 3, v___x_3301_);
lean_ctor_set(v___x_3298_, 2, v___x_3293_);
lean_ctor_set(v___x_3298_, 0, v___x_3300_);
v___x_3310_ = v___x_3298_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_diagnostics_3296_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v___x_3301_);
v___x_3310_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*4, v___x_3306_);
v___x_3311_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3308_, v___x_3310_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 4, v___x_3305_);
lean_ctor_set(v___x_3285_, 3, v_newStx_3270_);
lean_ctor_set(v___x_3285_, 2, v_toProcessingContext_3267_);
lean_ctor_set(v___x_3285_, 1, v___x_3311_);
lean_ctor_set(v___x_3285_, 0, v___x_3307_);
v___x_3313_ = v___x_3285_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_toProcessingContext_3267_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_newStx_3270_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v___x_3305_);
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
}
}
}
}
else
{
lean_dec(v_result_x3f_3274_);
lean_dec_ref(v_newParserState_3271_);
lean_dec(v_newStx_3270_);
lean_dec_ref(v_toProcessingContext_3267_);
return v_old_3269_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toProcessingContext_3267_ = stack[0].m_obj;
lean_object* v_a_3268_ = stack[1].m_obj;
lean_object* v_old_3269_ = stack[2].m_obj;
lean_object* v_newStx_3270_ = stack[3].m_obj;
lean_object* v_newParserState_3271_ = stack[4].m_obj;
lean_object* v___y_3272_ = stack[5].m_obj;
lean_object* v_res_3330_;
v_res_3330_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3267_, v_a_3268_, v_old_3269_, v_newStx_3270_, v_newParserState_3271_, v___y_3272_);
stack->m_obj
 = v_res_3330_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3331_, lean_object* v_a_3332_, lean_object* v_old_3333_, lean_object* v_newStx_3334_, lean_object* v_newParserState_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3331_, v_a_3332_, v_old_3333_, v_newStx_3334_, v_newParserState_3335_, v___y_3336_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v_a_3332_);
return v_res_3338_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3339_, lean_object* v_setupImports_3340_, lean_object* v_old_x3f_3341_, lean_object* v___x_3342_, lean_object* v___f_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; 
lean_inc_ref(v_toProcessingContext_3339_);
v___x_3346_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3339_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3415_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3415_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3415_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_snd_3351_; lean_object* v_fst_3352_; lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3414_; 
v_snd_3351_ = lean_ctor_get(v_a_3347_, 1);
lean_inc(v_snd_3351_);
v_fst_3352_ = lean_ctor_get(v_a_3347_, 0);
lean_inc(v_fst_3352_);
lean_dec(v_a_3347_);
v_fst_3353_ = lean_ctor_get(v_snd_3351_, 0);
v_snd_3354_ = lean_ctor_get(v_snd_3351_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_snd_3351_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3356_ = v_snd_3351_;
v_isShared_3357_ = v_isSharedCheck_3414_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_snd_3354_);
lean_inc(v_fst_3353_);
lean_dec(v_snd_3351_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3414_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
uint8_t v___x_3358_; 
v___x_3358_ = l_Lean_MessageLog_hasErrors(v_snd_3354_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v___y_3361_; 
lean_inc(v_fst_3352_);
v___x_3359_ = l_Lean_Syntax_unsetTrailing(v_fst_3352_);
if (lean_obj_tag(v_old_x3f_3341_) == 1)
{
lean_object* v_val_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3397_; 
v_val_3382_ = lean_ctor_get(v_old_x3f_3341_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_old_x3f_3341_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3384_ = v_old_x3f_3341_;
v_isShared_3385_ = v_isSharedCheck_3397_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_val_3382_);
lean_dec(v_old_x3f_3341_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3397_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_stx_3386_; lean_object* v_result_x3f_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_stx_3386_ = lean_ctor_get(v_val_3382_, 3);
v_result_x3f_3387_ = lean_ctor_get(v_val_3382_, 4);
lean_inc(v_stx_3386_);
v___x_3388_ = l_Lean_Syntax_unsetTrailing(v_stx_3386_);
lean_inc(v___x_3359_);
v___x_3389_ = l_Lean_Syntax_eqWithInfo(v___x_3359_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_inc(v_result_x3f_3387_);
lean_del_object(v___x_3384_);
lean_dec(v_val_3382_);
lean_dec_ref(v___f_3343_);
if (lean_obj_tag(v_result_x3f_3387_) == 0)
{
lean_dec_ref(v___x_3342_);
v___y_3361_ = v___y_3344_;
goto v___jp_3360_;
}
else
{
lean_object* v_val_3390_; lean_object* v_processedSnap_3391_; lean_object* v___x_3392_; 
v_val_3390_ = lean_ctor_get(v_result_x3f_3387_, 0);
lean_inc(v_val_3390_);
lean_dec_ref_known(v_result_x3f_3387_, 1);
v_processedSnap_3391_ = lean_ctor_get(v_val_3390_, 1);
lean_inc_ref(v_processedSnap_3391_);
lean_dec(v_val_3390_);
v___x_3392_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3342_, v_processedSnap_3391_);
v___y_3361_ = v___y_3344_;
goto v___jp_3360_;
}
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
lean_dec(v___x_3359_);
lean_del_object(v___x_3356_);
lean_dec(v_snd_3354_);
lean_del_object(v___x_3349_);
lean_dec_ref(v___x_3342_);
lean_dec_ref(v_setupImports_3340_);
lean_dec_ref(v_toProcessingContext_3339_);
lean_inc_ref(v___y_3344_);
v___x_3393_ = lean_apply_5(v___f_3343_, v_val_3382_, v_fst_3352_, v_fst_3353_, v___y_3344_, lean_box(0));
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3393_);
v___x_3395_ = v___x_3384_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_dec_ref(v___f_3343_);
lean_dec_ref(v___x_3342_);
lean_dec(v_old_x3f_3341_);
v___y_3361_ = v___y_3344_;
goto v___jp_3360_;
}
v___jp_3360_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3362_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3354_);
lean_inc(v_fst_3353_);
lean_inc(v_fst_3352_);
v___x_3363_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3340_, v___x_3359_, v_fst_3352_, v_fst_3353_, v___y_3361_);
v___x_3364_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3365_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3366_ = lean_box(0);
v___x_3367_ = lean_unsigned_to_nat(32u);
v___x_3368_ = lean_mk_empty_array_with_capacity(v___x_3367_);
lean_dec_ref(v___x_3368_);
v___x_3369_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v___x_3363_);
v___x_3371_ = v___x_3356_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3363_);
v___x_3371_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
v___x_3373_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3373_, 0, v___x_3364_);
lean_ctor_set(v___x_3373_, 1, v___x_3365_);
lean_ctor_set(v___x_3373_, 2, v___x_3366_);
lean_ctor_set(v___x_3373_, 3, v___x_3369_);
lean_ctor_set_uint8(v___x_3373_, sizeof(void*)*4, v___x_3358_);
lean_inc(v_fst_3352_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_fst_3352_);
v___x_3375_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3375_, 0, v___x_3364_);
lean_ctor_set(v___x_3375_, 1, v___x_3362_);
lean_ctor_set(v___x_3375_, 2, v___x_3366_);
lean_ctor_set(v___x_3375_, 3, v___x_3369_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*4, v___x_3358_);
v___x_3376_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3374_, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3373_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
lean_ctor_set(v___x_3377_, 2, v_toProcessingContext_3339_);
lean_ctor_set(v___x_3377_, 3, v_fst_3352_);
lean_ctor_set(v___x_3377_, 4, v___x_3372_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3377_);
v___x_3379_ = v___x_3349_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
lean_del_object(v___x_3356_);
lean_dec(v_fst_3353_);
lean_dec_ref(v___f_3343_);
lean_dec_ref(v___x_3342_);
lean_dec(v_old_x3f_3341_);
lean_dec_ref(v_setupImports_3340_);
v___x_3398_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3354_);
v___x_3399_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3400_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3401_ = lean_box(0);
v___x_3402_ = lean_unsigned_to_nat(32u);
v___x_3403_ = lean_mk_empty_array_with_capacity(v___x_3402_);
lean_dec_ref(v___x_3403_);
v___x_3404_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3405_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3405_, 0, v___x_3399_);
lean_ctor_set(v___x_3405_, 1, v___x_3400_);
lean_ctor_set(v___x_3405_, 2, v___x_3401_);
lean_ctor_set(v___x_3405_, 3, v___x_3404_);
lean_ctor_set_uint8(v___x_3405_, sizeof(void*)*4, v___x_3358_);
lean_inc(v_fst_3352_);
v___x_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_fst_3352_);
v___x_3407_ = 0;
v___x_3408_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3408_, 0, v___x_3399_);
lean_ctor_set(v___x_3408_, 1, v___x_3398_);
lean_ctor_set(v___x_3408_, 2, v___x_3401_);
lean_ctor_set(v___x_3408_, 3, v___x_3404_);
lean_ctor_set_uint8(v___x_3408_, sizeof(void*)*4, v___x_3407_);
v___x_3409_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3406_, v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3405_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
lean_ctor_set(v___x_3410_, 2, v_toProcessingContext_3339_);
lean_ctor_set(v___x_3410_, 3, v_fst_3352_);
lean_ctor_set(v___x_3410_, 4, v___x_3401_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3410_);
v___x_3412_ = v___x_3349_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v___f_3343_);
lean_dec_ref(v___x_3342_);
lean_dec(v_old_x3f_3341_);
lean_dec_ref(v_setupImports_3340_);
lean_dec_ref(v_toProcessingContext_3339_);
v_a_3416_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3346_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3346_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toProcessingContext_3339_ = stack[0].m_obj;
lean_object* v_setupImports_3340_ = stack[1].m_obj;
lean_object* v_old_x3f_3341_ = stack[2].m_obj;
lean_object* v___x_3342_ = stack[3].m_obj;
lean_object* v___f_3343_ = stack[4].m_obj;
lean_object* v___y_3344_ = stack[5].m_obj;
lean_object* v_res_3424_;
v_res_3424_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3339_, v_setupImports_3340_, v_old_x3f_3341_, v___x_3342_, v___f_3343_, v___y_3344_);
stack->m_obj
 = v_res_3424_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3425_, lean_object* v_setupImports_3426_, lean_object* v_old_x3f_3427_, lean_object* v___x_3428_, lean_object* v___f_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3425_, v_setupImports_3426_, v_old_x3f_3427_, v___x_3428_, v___f_3429_, v___y_3430_);
lean_dec_ref(v___y_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3433_, lean_object* v_toProcessingContext_3434_, lean_object* v_x_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3436_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3433_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3439_, 0, v_x_3435_);
lean_ctor_set(v___x_3439_, 1, v___x_3436_);
lean_ctor_set(v___x_3439_, 2, v_toProcessingContext_3434_);
lean_ctor_set(v___x_3439_, 3, v___x_3437_);
lean_ctor_set(v___x_3439_, 4, v___x_3438_);
return v___x_3439_;
}
}
lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3440_, lean_object* v_old_x3f_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_toProcessingContext_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___f_3447_; lean_object* v___f_3448_; lean_object* v___f_3449_; 
v_toProcessingContext_3444_ = lean_ctor_get(v_a_3442_, 0);
v___x_3445_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3446_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3442_);
lean_inc_ref_n(v_toProcessingContext_3444_, 3);
v___f_3447_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3447_, 0, v_toProcessingContext_3444_);
lean_closure_set(v___f_3447_, 1, v_a_3442_);
lean_inc(v_old_x3f_3441_);
v___f_3448_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3448_, 0, v_toProcessingContext_3444_);
lean_closure_set(v___f_3448_, 1, v_setupImports_3440_);
lean_closure_set(v___f_3448_, 2, v_old_x3f_3441_);
lean_closure_set(v___f_3448_, 3, v___x_3446_);
lean_closure_set(v___f_3448_, 4, v___f_3447_);
v___f_3449_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3449_, 0, v___x_3445_);
lean_closure_set(v___f_3449_, 1, v_toProcessingContext_3444_);
if (lean_obj_tag(v_old_x3f_3441_) == 1)
{
lean_object* v_val_3450_; lean_object* v_result_x3f_3451_; 
v_val_3450_ = lean_ctor_get(v_old_x3f_3441_, 0);
lean_inc(v_val_3450_);
lean_dec_ref_known(v_old_x3f_3441_, 1);
v_result_x3f_3451_ = lean_ctor_get(v_val_3450_, 4);
if (lean_obj_tag(v_result_x3f_3451_) == 1)
{
lean_object* v_stx_3452_; lean_object* v_val_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_stx_3452_ = lean_ctor_get(v_val_3450_, 3);
lean_inc(v_stx_3452_);
v_val_3453_ = lean_ctor_get(v_result_x3f_3451_, 0);
lean_inc(v_val_3450_);
v___x_3454_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3450_);
v___x_3455_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3454_);
if (lean_obj_tag(v___x_3455_) == 1)
{
lean_object* v_val_3456_; 
v_val_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v___x_3455_, 1);
if (lean_obj_tag(v_val_3456_) == 1)
{
lean_object* v_val_3457_; lean_object* v_firstCmdSnap_3458_; lean_object* v___x_3459_; 
v_val_3457_ = lean_ctor_get(v_val_3456_, 0);
lean_inc(v_val_3457_);
lean_dec_ref_known(v_val_3456_, 1);
v_firstCmdSnap_3458_ = lean_ctor_get(v_val_3457_, 1);
lean_inc_ref(v_firstCmdSnap_3458_);
lean_dec(v_val_3457_);
v___x_3459_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3458_);
if (lean_obj_tag(v___x_3459_) == 1)
{
lean_object* v_val_3460_; lean_object* v_nextCmdSnap_x3f_3461_; 
v_val_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_val_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_nextCmdSnap_x3f_3461_ = lean_ctor_get(v_val_3460_, 4);
lean_inc(v_nextCmdSnap_x3f_3461_);
lean_dec(v_val_3460_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3461_) == 0)
{
lean_object* v___x_3462_; 
lean_dec(v_stx_3452_);
lean_dec(v_val_3450_);
v___x_3462_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3462_;
}
else
{
lean_object* v_val_3463_; lean_object* v___x_3464_; 
v_val_3463_ = lean_ctor_get(v_nextCmdSnap_x3f_3461_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3461_, 1);
v___x_3464_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3463_);
if (lean_obj_tag(v___x_3464_) == 1)
{
lean_object* v_val_3465_; lean_object* v_parserState_3466_; lean_object* v_pos_3467_; uint8_t v___x_3468_; 
v_val_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_val_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v_parserState_3466_ = lean_ctor_get(v_val_3465_, 2);
lean_inc_ref(v_parserState_3466_);
lean_dec(v_val_3465_);
v_pos_3467_ = lean_ctor_get(v_parserState_3466_, 0);
lean_inc(v_pos_3467_);
lean_dec_ref(v_parserState_3466_);
v___x_3468_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3467_, v_a_3442_);
lean_dec(v_pos_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_dec(v_stx_3452_);
lean_dec(v_val_3450_);
v___x_3469_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3469_;
}
else
{
lean_object* v_parserState_3470_; lean_object* v___x_3471_; 
lean_dec_ref(v___f_3449_);
lean_dec_ref(v___f_3448_);
v_parserState_3470_ = lean_ctor_get(v_val_3453_, 0);
lean_inc_ref(v_parserState_3470_);
lean_inc_ref(v_toProcessingContext_3444_);
v___x_3471_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3444_, v_a_3442_, v_val_3450_, v_stx_3452_, v_parserState_3470_, v_a_3442_);
return v___x_3471_;
}
}
else
{
lean_object* v___x_3472_; 
lean_dec(v___x_3464_);
lean_dec(v_stx_3452_);
lean_dec(v_val_3450_);
v___x_3472_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3472_;
}
}
}
else
{
lean_object* v___x_3473_; 
lean_dec(v___x_3459_);
lean_dec(v_stx_3452_);
lean_dec(v_val_3450_);
v___x_3473_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3473_;
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v_val_3456_);
lean_dec(v_stx_3452_);
lean_dec(v_val_3450_);
v___x_3474_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3474_;
}
}
else
{
lean_object* v___x_3475_; 
lean_dec(v___x_3455_);
lean_dec(v_stx_3452_);
lean_dec(v_val_3450_);
v___x_3475_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3475_;
}
}
else
{
lean_object* v___x_3476_; 
lean_dec(v_val_3450_);
v___x_3476_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3476_;
}
}
else
{
lean_object* v___x_3477_; 
lean_dec(v_old_x3f_3441_);
v___x_3477_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3449_, v___f_3448_, v_a_3442_);
return v___x_3477_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_setupImports_3440_ = stack[0].m_obj;
lean_object* v_old_x3f_3441_ = stack[1].m_obj;
lean_object* v_a_3442_ = stack[2].m_obj;
lean_object* v_res_3478_;
v_res_3478_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3440_, v_old_x3f_3441_, v_a_3442_);
stack->m_obj
 = v_res_3478_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3479_, lean_object* v_old_x3f_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3479_, v_old_x3f_3480_, v_a_3481_);
lean_dec_ref(v_a_3481_);
return v_res_3483_;
}
}
lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3484_, lean_object* v_old_x3f_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v___x_3488_; 
lean_inc(v_old_x3f_3485_);
v___x_3488_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3488_, 0, v_setupImports_3484_);
lean_closure_set(v___x_3488_, 1, v_old_x3f_3485_);
if (lean_obj_tag(v_old_x3f_3485_) == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_box(0);
v___x_3490_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3488_, v___x_3489_, v_a_3486_);
return v___x_3490_;
}
else
{
lean_object* v_val_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3500_; 
v_val_3491_ = lean_ctor_get(v_old_x3f_3485_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_old_x3f_3485_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3493_ = v_old_x3f_3485_;
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_val_3491_);
lean_dec(v_old_x3f_3485_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v_ictx_3495_; lean_object* v___x_3497_; 
v_ictx_3495_ = lean_ctor_get(v_val_3491_, 2);
lean_inc_ref(v_ictx_3495_);
lean_dec(v_val_3491_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_ictx_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_ictx_3495_);
v___x_3497_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3488_, v___x_3497_, v_a_3486_);
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_process_0interp(lean_interpreter_value* stack)
{
lean_object* v_setupImports_3484_ = stack[0].m_obj;
lean_object* v_old_x3f_3485_ = stack[1].m_obj;
lean_object* v_a_3486_ = stack[2].m_obj;
lean_object* v_res_3501_;
v_res_3501_ = l_Lean_Language_Lean_process(v_setupImports_3484_, v_old_x3f_3485_, v_a_3486_);
stack->m_obj
 = v_res_3501_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3502_, lean_object* v_old_x3f_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Language_Lean_process(v_setupImports_3502_, v_old_x3f_3503_, v_a_3504_);
lean_dec_ref(v_a_3504_);
return v_res_3506_;
}
}
lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3507_, lean_object* v_parserState_3508_, lean_object* v_commandState_3509_, lean_object* v_old_x3f_3510_){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3520_; 
v___x_3512_ = lean_io_promise_new();
v___x_3513_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3510_) == 0)
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_box(0);
v___y_3520_ = v___x_3535_;
goto v___jp_3519_;
}
else
{
lean_object* v_val_3536_; lean_object* v_snd_3537_; lean_object* v___x_3538_; 
v_val_3536_ = lean_ctor_get(v_old_x3f_3510_, 0);
v_snd_3537_ = lean_ctor_get(v_val_3536_, 1);
lean_inc(v_snd_3537_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v_snd_3537_);
v___y_3520_ = v___x_3538_;
goto v___jp_3519_;
}
v___jp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3515_, v___y_3516_, v_inputCtx_3507_);
lean_dec(v___x_3517_);
v___x_3518_ = l_IO_Promise_result_x21___redArg(v___x_3512_);
lean_dec(v___x_3512_);
return v___x_3518_;
}
v___jp_3519_:
{
uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3521_ = 1;
v___x_3522_ = lean_box(0);
v___x_3523_ = lean_box(v___x_3521_);
lean_inc(v___x_3512_);
v___x_3524_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3524_, 0, v___y_3520_);
lean_closure_set(v___x_3524_, 1, v_parserState_3508_);
lean_closure_set(v___x_3524_, 2, v_commandState_3509_);
lean_closure_set(v___x_3524_, 3, v___x_3512_);
lean_closure_set(v___x_3524_, 4, v___x_3523_);
lean_closure_set(v___x_3524_, 5, v___x_3513_);
lean_closure_set(v___x_3524_, 6, v___x_3522_);
if (lean_obj_tag(v_old_x3f_3510_) == 0)
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_box(0);
v___y_3515_ = v___x_3524_;
v___y_3516_ = v___x_3525_;
goto v___jp_3514_;
}
else
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_val_3526_ = lean_ctor_get(v_old_x3f_3510_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_old_x3f_3510_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3528_ = v_old_x3f_3510_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_old_x3f_3510_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_fst_3530_; lean_object* v___x_3532_; 
v_fst_3530_ = lean_ctor_get(v_val_3526_, 0);
lean_inc(v_fst_3530_);
lean_dec(v_val_3526_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v_fst_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_fst_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
v___y_3515_ = v___x_3524_;
v___y_3516_ = v___x_3532_;
goto v___jp_3514_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_processCommands_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_3507_ = stack[0].m_obj;
lean_object* v_parserState_3508_ = stack[1].m_obj;
lean_object* v_commandState_3509_ = stack[2].m_obj;
lean_object* v_old_x3f_3510_ = stack[3].m_obj;
lean_object* v_res_3539_;
v_res_3539_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3507_, v_parserState_3508_, v_commandState_3509_, v_old_x3f_3510_);
stack->m_obj
 = v_res_3539_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3540_, lean_object* v_parserState_3541_, lean_object* v_commandState_3542_, lean_object* v_old_x3f_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3540_, v_parserState_3541_, v_commandState_3542_, v_old_x3f_3543_);
lean_dec_ref(v_inputCtx_3540_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3546_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3547_; 
v_nextCmdSnap_x3f_3547_ = lean_ctor_get(v_snap_3546_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3547_) == 1)
{
lean_object* v_val_3548_; lean_object* v___x_3549_; 
lean_inc_ref(v_nextCmdSnap_x3f_3547_);
lean_dec_ref(v_snap_3546_);
v_val_3548_ = lean_ctor_get(v_nextCmdSnap_x3f_3547_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3547_, 1);
v___x_3549_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3548_);
v_snap_3546_ = v___x_3549_;
goto _start;
}
else
{
lean_object* v_elabSnap_3551_; lean_object* v_resultSnap_3552_; lean_object* v___x_3553_; lean_object* v_cmdState_3554_; lean_object* v___x_3555_; 
v_elabSnap_3551_ = lean_ctor_get(v_snap_3546_, 3);
lean_inc_ref(v_elabSnap_3551_);
lean_dec_ref(v_snap_3546_);
v_resultSnap_3552_ = lean_ctor_get(v_elabSnap_3551_, 2);
lean_inc_ref(v_resultSnap_3552_);
lean_dec_ref(v_elabSnap_3551_);
v___x_3553_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3552_);
v_cmdState_3554_ = lean_ctor_get(v___x_3553_, 1);
lean_inc_ref(v_cmdState_3554_);
lean_dec(v___x_3553_);
v___x_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_cmdState_3554_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3556_){
_start:
{
lean_object* v_result_x3f_3557_; 
v_result_x3f_3557_ = lean_ctor_get(v_snap_3556_, 4);
lean_inc(v_result_x3f_3557_);
lean_dec_ref(v_snap_3556_);
if (lean_obj_tag(v_result_x3f_3557_) == 0)
{
lean_object* v___x_3558_; 
v___x_3558_ = lean_box(0);
return v___x_3558_;
}
else
{
lean_object* v_val_3559_; lean_object* v_processedSnap_3560_; lean_object* v___x_3561_; lean_object* v_result_x3f_3562_; 
v_val_3559_ = lean_ctor_get(v_result_x3f_3557_, 0);
lean_inc(v_val_3559_);
lean_dec_ref_known(v_result_x3f_3557_, 1);
v_processedSnap_3560_ = lean_ctor_get(v_val_3559_, 1);
lean_inc_ref(v_processedSnap_3560_);
lean_dec(v_val_3559_);
v___x_3561_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3560_);
v_result_x3f_3562_ = lean_ctor_get(v___x_3561_, 2);
lean_inc(v_result_x3f_3562_);
lean_dec(v___x_3561_);
if (lean_obj_tag(v_result_x3f_3562_) == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_box(0);
return v___x_3563_;
}
else
{
lean_object* v_val_3564_; lean_object* v_firstCmdSnap_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_val_3564_ = lean_ctor_get(v_result_x3f_3562_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v_result_x3f_3562_, 1);
v_firstCmdSnap_3565_ = lean_ctor_get(v_val_3564_, 1);
lean_inc_ref(v_firstCmdSnap_3565_);
lean_dec(v_val_3564_);
v___x_3566_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3565_);
v___x_3567_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3566_);
return v___x_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3568_, lean_object* v_snap_3569_, lean_object* v_acc_3570_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3571_; lean_object* v_acc_3572_; 
v_nextCmdSnap_x3f_3571_ = lean_ctor_get(v_snap_3569_, 4);
lean_inc(v_nextCmdSnap_x3f_3571_);
lean_inc(v_f_3568_);
v_acc_3572_ = lean_apply_2(v_f_3568_, v_acc_3570_, v_snap_3569_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3571_) == 1)
{
lean_object* v_val_3573_; lean_object* v___x_3574_; 
v_val_3573_ = lean_ctor_get(v_nextCmdSnap_x3f_3571_, 0);
lean_inc(v_val_3573_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3571_, 1);
v___x_3574_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3573_);
v_snap_3569_ = v___x_3574_;
v_acc_3570_ = v_acc_3572_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3571_);
lean_dec(v_f_3568_);
return v_acc_3572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3576_, lean_object* v_f_3577_, lean_object* v_snap_3578_, lean_object* v_acc_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3577_, v_snap_3578_, v_acc_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3581_, lean_object* v_init_3582_, lean_object* v_f_3583_){
_start:
{
lean_object* v_result_x3f_3584_; 
v_result_x3f_3584_ = lean_ctor_get(v_snap_3581_, 4);
lean_inc(v_result_x3f_3584_);
lean_dec_ref(v_snap_3581_);
if (lean_obj_tag(v_result_x3f_3584_) == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_f_3583_);
lean_dec(v_init_3582_);
v___x_3585_ = lean_box(0);
return v___x_3585_;
}
else
{
lean_object* v_val_3586_; lean_object* v_processedSnap_3587_; lean_object* v___x_3588_; lean_object* v_result_x3f_3589_; 
v_val_3586_ = lean_ctor_get(v_result_x3f_3584_, 0);
lean_inc(v_val_3586_);
lean_dec_ref_known(v_result_x3f_3584_, 1);
v_processedSnap_3587_ = lean_ctor_get(v_val_3586_, 1);
lean_inc_ref(v_processedSnap_3587_);
lean_dec(v_val_3586_);
v___x_3588_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3587_);
v_result_x3f_3589_ = lean_ctor_get(v___x_3588_, 2);
lean_inc(v_result_x3f_3589_);
lean_dec(v___x_3588_);
if (lean_obj_tag(v_result_x3f_3589_) == 0)
{
lean_object* v___x_3590_; 
lean_dec(v_f_3583_);
lean_dec(v_init_3582_);
v___x_3590_ = lean_box(0);
return v___x_3590_;
}
else
{
lean_object* v_val_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3601_; 
v_val_3591_ = lean_ctor_get(v_result_x3f_3589_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_result_x3f_3589_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3593_ = v_result_x3f_3589_;
v_isShared_3594_ = v_isSharedCheck_3601_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_val_3591_);
lean_dec(v_result_x3f_3589_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3601_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_firstCmdSnap_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
v_firstCmdSnap_3595_ = lean_ctor_get(v_val_3591_, 1);
lean_inc_ref(v_firstCmdSnap_3595_);
lean_dec(v_val_3591_);
v___x_3596_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3595_);
v___x_3597_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3583_, v___x_3596_, v_init_3582_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3597_);
v___x_3599_ = v___x_3593_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3602_, lean_object* v_snap_3603_, lean_object* v_init_3604_, lean_object* v_f_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3603_, v_init_3604_, v_f_3605_);
return v___x_3606_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = 1;
v___x_3613_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3614_ = l_Lean_Name_toString(v___x_3613_, v___x_3612_);
return v___x_3614_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3615_ = 0;
v___x_3616_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3617_ = lean_box(0);
v___x_3618_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3619_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3620_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3618_);
lean_ctor_set(v___x_3620_, 2, v___x_3617_);
lean_ctor_set(v___x_3620_, 3, v___x_3616_);
lean_ctor_set_uint8(v___x_3620_, sizeof(void*)*4, v___x_3615_);
return v___x_3620_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3622_ = lean_box(0);
v___x_3623_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3622_, v___x_3621_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3624_){
_start:
{
lean_object* v_result_x3f_3625_; 
v_result_x3f_3625_ = lean_ctor_get(v_snap_3624_, 4);
lean_inc(v_result_x3f_3625_);
if (lean_obj_tag(v_result_x3f_3625_) == 1)
{
lean_object* v_val_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3701_; 
v_val_3626_ = lean_ctor_get(v_result_x3f_3625_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_result_x3f_3625_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3628_ = v_result_x3f_3625_;
v_isShared_3629_ = v_isSharedCheck_3701_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_val_3626_);
lean_dec(v_result_x3f_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3701_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v_toSnapshot_3630_; lean_object* v_metaSnap_3631_; lean_object* v_ictx_3632_; lean_object* v_stx_3633_; lean_object* v_parserState_3634_; lean_object* v_processedSnap_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3700_; 
v_toSnapshot_3630_ = lean_ctor_get(v_snap_3624_, 0);
v_metaSnap_3631_ = lean_ctor_get(v_snap_3624_, 1);
v_ictx_3632_ = lean_ctor_get(v_snap_3624_, 2);
v_stx_3633_ = lean_ctor_get(v_snap_3624_, 3);
v_parserState_3634_ = lean_ctor_get(v_val_3626_, 0);
v_processedSnap_3635_ = lean_ctor_get(v_val_3626_, 1);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_val_3626_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3637_ = v_val_3626_;
v_isShared_3638_ = v_isSharedCheck_3700_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_processedSnap_3635_);
lean_inc(v_parserState_3634_);
lean_dec(v_val_3626_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3700_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v_processed_3639_; lean_object* v_result_x3f_3640_; 
v_processed_3639_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3635_);
v_result_x3f_3640_ = lean_ctor_get(v_processed_3639_, 2);
lean_inc(v_result_x3f_3640_);
if (lean_obj_tag(v_result_x3f_3640_) == 1)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3694_; 
lean_inc(v_stx_3633_);
lean_inc_ref(v_ictx_3632_);
lean_inc_ref(v_metaSnap_3631_);
lean_inc_ref(v_toSnapshot_3630_);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_snap_3624_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; lean_object* v_unused_3696_; lean_object* v_unused_3697_; lean_object* v_unused_3698_; lean_object* v_unused_3699_; 
v_unused_3695_ = lean_ctor_get(v_snap_3624_, 4);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_snap_3624_, 3);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_snap_3624_, 2);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_snap_3624_, 1);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_snap_3624_, 0);
lean_dec(v_unused_3699_);
v___x_3642_ = v_snap_3624_;
v_isShared_3643_ = v_isSharedCheck_3694_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v_snap_3624_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3694_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_val_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3693_; 
v_val_3644_ = lean_ctor_get(v_result_x3f_3640_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_result_x3f_3640_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3646_ = v_result_x3f_3640_;
v_isShared_3647_ = v_isSharedCheck_3693_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_val_3644_);
lean_dec(v_result_x3f_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3693_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_toSnapshot_3648_; lean_object* v_metaSnap_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3691_; 
v_toSnapshot_3648_ = lean_ctor_get(v_processed_3639_, 0);
v_metaSnap_3649_ = lean_ctor_get(v_processed_3639_, 1);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_processed_3639_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; 
v_unused_3692_ = lean_ctor_get(v_processed_3639_, 2);
lean_dec(v_unused_3692_);
v___x_3651_ = v_processed_3639_;
v_isShared_3652_ = v_isSharedCheck_3691_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_metaSnap_3649_);
lean_inc(v_toSnapshot_3648_);
lean_dec(v_processed_3639_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3691_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_cmdState_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3689_; 
v_cmdState_3653_ = lean_ctor_get(v_val_3644_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_val_3644_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_val_3644_, 1);
lean_dec(v_unused_3690_);
v___x_3655_ = v_val_3644_;
v_isShared_3656_ = v_isSharedCheck_3689_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_cmdState_3653_);
lean_dec(v_val_3644_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3689_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v_resultSnap_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v_elabSnap_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_termCmd_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3657_ = lean_box(0);
v___x_3658_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3659_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3653_);
v_resultSnap_3660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3660_, 0, v___x_3658_);
lean_ctor_set(v_resultSnap_3660_, 1, v_cmdState_3653_);
lean_ctor_set(v_resultSnap_3660_, 2, v___x_3659_);
v___x_3661_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3662_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3657_, v_resultSnap_3660_);
v___x_3663_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3664_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3665_, 0, v___x_3658_);
lean_ctor_set(v_elabSnap_3665_, 1, v___x_3661_);
lean_ctor_set(v_elabSnap_3665_, 2, v___x_3662_);
lean_ctor_set(v_elabSnap_3665_, 3, v___x_3663_);
lean_ctor_set(v_elabSnap_3665_, 4, v___x_3664_);
v___x_3666_ = lean_box(0);
v___x_3667_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3668_, 0, v___x_3658_);
lean_ctor_set(v_termCmd_3668_, 1, v___x_3666_);
lean_ctor_set(v_termCmd_3668_, 2, v___x_3667_);
lean_ctor_set(v_termCmd_3668_, 3, v_elabSnap_3665_);
lean_ctor_set(v_termCmd_3668_, 4, v___x_3657_);
v___x_3669_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3657_, v_termCmd_3668_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 1, v___x_3669_);
v___x_3671_ = v___x_3655_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_cmdState_3653_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3671_);
v___x_3673_ = v___x_3646_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v_newProcessed_3675_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 2, v___x_3673_);
v_newProcessed_3675_ = v___x_3651_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_toSnapshot_3648_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_metaSnap_3649_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v___x_3673_);
v_newProcessed_3675_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3657_, v_newProcessed_3675_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 1, v___x_3676_);
v___x_3678_ = v___x_3637_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_parserState_3634_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; 
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3678_);
v___x_3680_ = v___x_3628_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; 
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 4, v___x_3680_);
v___x_3682_ = v___x_3642_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_toSnapshot_3630_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_metaSnap_3631_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v_ictx_3632_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v_stx_3633_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
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
lean_dec(v_result_x3f_3640_);
lean_dec(v_processed_3639_);
lean_del_object(v___x_3637_);
lean_dec_ref(v_parserState_3634_);
lean_del_object(v___x_3628_);
return v_snap_3624_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3625_);
return v_snap_3624_;
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

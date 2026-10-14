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
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_ctor_set(v___x_626_, 3, v___x_625_);
lean_ctor_set(v___x_626_, 4, v___x_624_);
lean_ctor_set(v___x_626_, 5, v___x_624_);
lean_ctor_set(v___x_626_, 6, v___x_624_);
lean_ctor_set(v___x_626_, 7, v___x_624_);
lean_ctor_set(v___x_626_, 8, v___x_624_);
lean_ctor_set(v___x_626_, 9, v___x_624_);
lean_ctor_set(v___x_626_, 10, v___x_624_);
lean_ctor_set(v___x_626_, 11, v___x_623_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(32u);
v___x_628_ = lean_mk_empty_array_with_capacity(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = ((size_t)5ULL);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_unsigned_to_nat(32u);
v___x_633_ = lean_mk_empty_array_with_capacity(v___x_632_);
v___x_634_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_635_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_631_);
lean_ctor_set(v___x_635_, 3, v___x_631_);
lean_ctor_set_usize(v___x_635_, 4, v___x_630_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_box(1);
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_638_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_636_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_env_644_; uint8_t v___x_645_; lean_object* v_env_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_scopes_649_; lean_object* v___x_650_; lean_object* v_opts_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_643_ = lean_st_ref_get(v___y_641_);
v_env_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_env_644_);
lean_dec(v___x_643_);
v___x_645_ = 0;
v_env_646_ = l_Lean_Environment_setRecordingDeps(v_env_644_, v___x_645_);
v___x_647_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_648_ = lean_st_ref_get(v___y_641_);
v_scopes_649_ = lean_ctor_get(v___x_648_, 2);
lean_inc(v_scopes_649_);
lean_dec(v___x_648_);
v___x_650_ = l_List_head_x21___redArg(v___x_647_, v_scopes_649_);
lean_dec(v_scopes_649_);
v_opts_651_ = lean_ctor_get(v___x_650_, 1);
lean_inc_ref(v_opts_651_);
lean_dec(v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_653_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_646_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
lean_ctor_set(v___x_654_, 2, v___x_653_);
lean_ctor_set(v___x_654_, 3, v_opts_651_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_msgData_640_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_657_, v___y_658_);
lean_dec(v___y_658_);
return v_res_660_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_661_, uint8_t v___y_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_663_) == 1)
{
lean_object* v_pre_664_; 
v_pre_664_ = lean_ctor_get(v_x_663_, 0);
if (lean_obj_tag(v_pre_664_) == 0)
{
lean_object* v_str_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_str_665_ = lean_ctor_get(v_x_663_, 1);
v___x_666_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_667_ = lean_string_dec_eq(v_str_665_, v___x_666_);
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
return v_suppressElabErrors_661_;
}
}
else
{
return v___y_662_;
}
}
else
{
return v___y_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_668_, lean_object* v___y_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_suppressElabErrors_boxed_671_; uint8_t v___y_9378__boxed_672_; uint8_t v_res_673_; lean_object* v_r_674_; 
v_suppressElabErrors_boxed_671_ = lean_unbox(v_suppressElabErrors_668_);
v___y_9378__boxed_672_ = lean_unbox(v___y_669_);
v_res_673_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_671_, v___y_9378__boxed_672_, v_x_670_);
lean_dec(v_x_670_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_676_, lean_object* v_msgData_677_, uint8_t v_severity_678_, uint8_t v_isSilent_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_749_; uint8_t v___y_750_; lean_object* v___y_751_; uint8_t v___y_752_; lean_object* v___y_753_; uint8_t v___y_777_; uint8_t v___y_778_; lean_object* v___y_779_; uint8_t v___y_780_; lean_object* v___y_781_; uint8_t v___y_785_; uint8_t v___y_786_; uint8_t v___y_787_; uint8_t v___x_802_; uint8_t v___y_804_; uint8_t v___y_805_; uint8_t v___y_806_; uint8_t v___y_808_; uint8_t v___x_820_; 
v___x_802_ = 2;
v___x_820_ = l_Lean_instBEqMessageSeverity_beq(v_severity_678_, v___x_802_);
if (v___x_820_ == 0)
{
v___y_808_ = v___x_820_;
goto v___jp_807_;
}
else
{
uint8_t v___x_821_; 
lean_inc_ref(v_msgData_677_);
v___x_821_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_677_);
v___y_808_ = v___x_821_;
goto v___jp_807_;
}
v___jp_683_:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Elab_Command_getScope___redArg(v___y_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_currNamespace_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_currNamespace_694_ = lean_ctor_get(v_a_693_, 2);
lean_inc(v_currNamespace_694_);
lean_dec(v_a_693_);
v___x_695_ = l_Lean_Elab_Command_getScope___redArg(v___y_691_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_731_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_731_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_731_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_731_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_openDecls_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_env_705_; lean_object* v_messages_706_; lean_object* v_scopes_707_; lean_object* v_usedQuotCtxts_708_; lean_object* v_nextMacroScope_709_; lean_object* v_maxRecDepth_710_; lean_object* v_ngen_711_; lean_object* v_auxDeclNGen_712_; lean_object* v_infoState_713_; lean_object* v_traceState_714_; lean_object* v_snapshotTasks_715_; lean_object* v_prevLinterStates_716_; lean_object* v_codeQualityEntryTasks_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_730_; 
v_openDecls_700_ = lean_ctor_get(v_a_696_, 3);
lean_inc(v_openDecls_700_);
lean_dec(v_a_696_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_currNamespace_694_);
lean_ctor_set(v___x_701_, 1, v_openDecls_700_);
v___x_702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___y_684_);
lean_inc_ref(v___y_685_);
lean_inc_ref(v___y_689_);
v___x_703_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_703_, 0, v___y_689_);
lean_ctor_set(v___x_703_, 1, v___y_687_);
lean_ctor_set(v___x_703_, 2, v___y_690_);
lean_ctor_set(v___x_703_, 3, v___y_685_);
lean_ctor_set(v___x_703_, 4, v___x_702_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*5, v___y_688_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*5 + 1, v___y_686_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*5 + 2, v_isSilent_679_);
v___x_704_ = lean_st_ref_take(v___y_691_);
v_env_705_ = lean_ctor_get(v___x_704_, 0);
v_messages_706_ = lean_ctor_get(v___x_704_, 1);
v_scopes_707_ = lean_ctor_get(v___x_704_, 2);
v_usedQuotCtxts_708_ = lean_ctor_get(v___x_704_, 3);
v_nextMacroScope_709_ = lean_ctor_get(v___x_704_, 4);
v_maxRecDepth_710_ = lean_ctor_get(v___x_704_, 5);
v_ngen_711_ = lean_ctor_get(v___x_704_, 6);
v_auxDeclNGen_712_ = lean_ctor_get(v___x_704_, 7);
v_infoState_713_ = lean_ctor_get(v___x_704_, 8);
v_traceState_714_ = lean_ctor_get(v___x_704_, 9);
v_snapshotTasks_715_ = lean_ctor_get(v___x_704_, 10);
v_prevLinterStates_716_ = lean_ctor_get(v___x_704_, 11);
v_codeQualityEntryTasks_717_ = lean_ctor_get(v___x_704_, 12);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_730_ == 0)
{
v___x_719_ = v___x_704_;
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_codeQualityEntryTasks_717_);
lean_inc(v_prevLinterStates_716_);
lean_inc(v_snapshotTasks_715_);
lean_inc(v_traceState_714_);
lean_inc(v_infoState_713_);
lean_inc(v_auxDeclNGen_712_);
lean_inc(v_ngen_711_);
lean_inc(v_maxRecDepth_710_);
lean_inc(v_nextMacroScope_709_);
lean_inc(v_usedQuotCtxts_708_);
lean_inc(v_scopes_707_);
lean_inc(v_messages_706_);
lean_inc(v_env_705_);
lean_dec(v___x_704_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Lean_MessageLog_add(v___x_703_, v_messages_706_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_env_705_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_scopes_707_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_usedQuotCtxts_708_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_nextMacroScope_709_);
lean_ctor_set(v_reuseFailAlloc_729_, 5, v_maxRecDepth_710_);
lean_ctor_set(v_reuseFailAlloc_729_, 6, v_ngen_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 7, v_auxDeclNGen_712_);
lean_ctor_set(v_reuseFailAlloc_729_, 8, v_infoState_713_);
lean_ctor_set(v_reuseFailAlloc_729_, 9, v_traceState_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 10, v_snapshotTasks_715_);
lean_ctor_set(v_reuseFailAlloc_729_, 11, v_prevLinterStates_716_);
lean_ctor_set(v_reuseFailAlloc_729_, 12, v_codeQualityEntryTasks_717_);
v___x_724_ = v_reuseFailAlloc_729_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_st_ref_put(v___y_691_, v___x_724_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_721_);
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_721_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_currNamespace_694_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_684_);
v_a_732_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_695_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_695_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v___y_690_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_684_);
v_a_740_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_692_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_692_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
v___jp_748_:
{
lean_object* v_fileName_754_; lean_object* v_fileMap_755_; uint8_t v_suppressElabErrors_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_775_; 
v_fileName_754_ = lean_ctor_get(v___y_680_, 0);
v_fileMap_755_ = lean_ctor_get(v___y_680_, 1);
v_suppressElabErrors_756_ = lean_ctor_get_uint8(v___y_680_, sizeof(void*)*10);
v___x_757_ = lean_box(v_suppressElabErrors_756_);
v___x_758_ = lean_box(v___y_749_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_759_, 0, v___x_757_);
lean_closure_set(v___f_759_, 1, v___x_758_);
v___x_760_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_677_);
v___x_761_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_760_, v___y_681_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_775_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_inc_ref_n(v_fileMap_755_, 2);
v___x_766_ = l_Lean_FileMap_toPosition(v_fileMap_755_, v___y_751_);
lean_dec(v___y_751_);
v___x_767_ = l_Lean_FileMap_toPosition(v_fileMap_755_, v___y_753_);
lean_dec(v___y_753_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_756_ == 0)
{
lean_del_object(v___x_764_);
lean_dec_ref(v___f_759_);
v___y_684_ = v_a_762_;
v___y_685_ = v___x_769_;
v___y_686_ = v___y_750_;
v___y_687_ = v___x_766_;
v___y_688_ = v___y_752_;
v___y_689_ = v_fileName_754_;
v___y_690_ = v___x_768_;
v___y_691_ = v___y_681_;
goto v___jp_683_;
}
else
{
uint8_t v___x_770_; 
lean_inc(v_a_762_);
v___x_770_ = l_Lean_MessageData_hasTag(v___f_759_, v_a_762_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec_ref_known(v___x_768_, 1);
lean_dec_ref(v___x_766_);
lean_dec(v_a_762_);
v___x_771_ = lean_box(0);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_771_);
v___x_773_ = v___x_764_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_del_object(v___x_764_);
v___y_684_ = v_a_762_;
v___y_685_ = v___x_769_;
v___y_686_ = v___y_750_;
v___y_687_ = v___x_766_;
v___y_688_ = v___y_752_;
v___y_689_ = v_fileName_754_;
v___y_690_ = v___x_768_;
v___y_691_ = v___y_681_;
goto v___jp_683_;
}
}
}
}
v___jp_776_:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Syntax_getTailPos_x3f(v___y_779_, v___y_780_);
lean_dec(v___y_779_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_inc(v___y_781_);
v___y_749_ = v___y_777_;
v___y_750_ = v___y_778_;
v___y_751_ = v___y_781_;
v___y_752_ = v___y_780_;
v___y_753_ = v___y_781_;
goto v___jp_748_;
}
else
{
lean_object* v_val_783_; 
v_val_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v___x_782_, 1);
v___y_749_ = v___y_777_;
v___y_750_ = v___y_778_;
v___y_751_ = v___y_781_;
v___y_752_ = v___y_780_;
v___y_753_ = v_val_783_;
goto v___jp_748_;
}
}
v___jp_784_:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Elab_Command_getRef___redArg(v___y_680_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_ref_790_; lean_object* v___x_791_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v_ref_790_ = l_Lean_replaceRef(v_ref_676_, v_a_789_);
lean_dec(v_a_789_);
v___x_791_ = l_Lean_Syntax_getPos_x3f(v_ref_790_, v___y_786_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___y_777_ = v___y_785_;
v___y_778_ = v___y_787_;
v___y_779_ = v_ref_790_;
v___y_780_ = v___y_786_;
v___y_781_ = v___x_792_;
goto v___jp_776_;
}
else
{
lean_object* v_val_793_; 
v_val_793_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v___x_791_, 1);
v___y_777_ = v___y_785_;
v___y_778_ = v___y_787_;
v___y_779_ = v_ref_790_;
v___y_780_ = v___y_786_;
v___y_781_ = v_val_793_;
goto v___jp_776_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_msgData_677_);
v_a_794_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_788_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_788_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
v___jp_803_:
{
if (v___y_806_ == 0)
{
v___y_785_ = v___y_804_;
v___y_786_ = v___y_805_;
v___y_787_ = v_severity_678_;
goto v___jp_784_;
}
else
{
v___y_785_ = v___y_804_;
v___y_786_ = v___y_805_;
v___y_787_ = v___x_802_;
goto v___jp_784_;
}
}
v___jp_807_:
{
if (v___y_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_scopes_811_; lean_object* v___x_812_; lean_object* v_opts_813_; uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_809_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_810_ = lean_st_ref_get(v___y_681_);
v_scopes_811_ = lean_ctor_get(v___x_810_, 2);
lean_inc(v_scopes_811_);
lean_dec(v___x_810_);
v___x_812_ = l_List_head_x21___redArg(v___x_809_, v_scopes_811_);
lean_dec(v_scopes_811_);
v_opts_813_ = lean_ctor_get(v___x_812_, 1);
lean_inc_ref(v_opts_813_);
lean_dec(v___x_812_);
v___x_814_ = 1;
v___x_815_ = l_Lean_instBEqMessageSeverity_beq(v_severity_678_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec_ref(v_opts_813_);
v___y_804_ = v___y_808_;
v___y_805_ = v___y_808_;
v___y_806_ = v___x_815_;
goto v___jp_803_;
}
else
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = l_Lean_warningAsError;
v___x_817_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_813_, v___x_816_);
lean_dec_ref(v_opts_813_);
v___y_804_ = v___y_808_;
v___y_805_ = v___y_808_;
v___y_806_ = v___x_817_;
goto v___jp_803_;
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_msgData_677_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_822_, lean_object* v_msgData_823_, lean_object* v_severity_824_, lean_object* v_isSilent_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_severity_boxed_829_; uint8_t v_isSilent_boxed_830_; lean_object* v_res_831_; 
v_severity_boxed_829_ = lean_unbox(v_severity_824_);
v_isSilent_boxed_830_ = lean_unbox(v_isSilent_825_);
v_res_831_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_822_, v_msgData_823_, v_severity_boxed_829_, v_isSilent_boxed_830_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v_ref_822_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_832_, uint8_t v_severity_833_, uint8_t v_isSilent_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Elab_Command_getRef___redArg(v___y_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_839_, v_msgData_832_, v_severity_833_, v_isSilent_834_, v___y_835_, v___y_836_);
lean_dec(v_a_839_);
return v___x_840_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_msgData_832_);
v_a_841_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_838_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_838_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_849_, lean_object* v_severity_850_, lean_object* v_isSilent_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v_severity_boxed_855_; uint8_t v_isSilent_boxed_856_; lean_object* v_res_857_; 
v_severity_boxed_855_ = lean_unbox(v_severity_850_);
v_isSilent_boxed_856_ = lean_unbox(v_isSilent_851_);
v_res_857_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_849_, v_severity_boxed_855_, v_isSilent_boxed_856_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
uint8_t v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = 2;
v___x_863_ = 0;
v___x_864_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_858_, v___x_862_, v___x_863_, v___y_859_, v___y_860_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_870_, lean_object* v_msgData_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = 2;
v___x_876_ = 0;
v___x_877_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_870_, v_msgData_871_, v___x_875_, v___x_876_, v___y_872_, v___y_873_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_878_, lean_object* v_msgData_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_878_, v_msgData_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v_ref_878_);
return v_res_883_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
if (lean_obj_tag(v_ex_887_) == 0)
{
lean_object* v_ref_891_; lean_object* v_msg_892_; lean_object* v___x_893_; 
v_ref_891_ = lean_ctor_get(v_ex_887_, 0);
lean_inc(v_ref_891_);
v_msg_892_ = lean_ctor_get(v_ex_887_, 1);
lean_inc_ref(v_msg_892_);
lean_dec_ref_known(v_ex_887_, 2);
v___x_893_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_891_, v_msg_892_, v___y_888_, v___y_889_);
lean_dec(v_ref_891_);
return v___x_893_;
}
else
{
lean_object* v_id_894_; uint8_t v___y_896_; uint8_t v___x_918_; 
v_id_894_ = lean_ctor_get(v_ex_887_, 0);
lean_inc(v_id_894_);
v___x_918_ = l_Lean_Elab_isAbortExceptionId(v_id_894_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_Exception_isInterrupt(v_ex_887_);
lean_dec_ref_known(v_ex_887_, 2);
v___y_896_ = v___x_919_;
goto v___jp_895_;
}
else
{
lean_dec_ref_known(v_ex_887_, 2);
v___y_896_ = v___x_918_;
goto v___jp_895_;
}
v___jp_895_:
{
if (v___y_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_InternalExceptionId_getName(v_id_894_);
lean_dec(v_id_894_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_900_ = l_Lean_MessageData_ofName(v_a_898_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_901_, v___y_888_, v___y_889_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_915_; 
v_a_903_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_915_ == 0)
{
v___x_905_ = v___x_897_;
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_897_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_ref_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v_ref_907_ = lean_ctor_get(v___y_888_, 7);
v___x_908_ = lean_io_error_to_string(v_a_903_);
v___x_909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___x_910_ = l_Lean_MessageData_ofFormat(v___x_909_);
lean_inc(v_ref_907_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_ref_907_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_911_);
v___x_913_ = v___x_905_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v_id_894_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
v___x_929_ = lean_apply_3(v_x_925_, v___y_926_, v___y_927_, lean_box(0));
if (lean_obj_tag(v___x_929_) == 0)
{
return v___x_929_;
}
else
{
lean_object* v_a_930_; uint8_t v___x_931_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
v___x_931_ = l_Lean_Exception_isInterrupt(v_a_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref_known(v___x_929_, 1);
v___x_932_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_930_, v___y_926_, v___y_927_);
return v___x_932_;
}
else
{
lean_dec(v_a_930_);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_938_, lean_object* v___x_939_, lean_object* v_val_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_a_944_; lean_object* v___x_946_; 
v___x_946_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_938_, v___x_939_, v_val_940_);
if (lean_obj_tag(v___x_946_) == 0)
{
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v_a_944_ = v_a_947_;
goto v___jp_943_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_946_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v___x_956_; 
lean_dec_ref_known(v___x_946_, 1);
v___x_956_ = lean_box(0);
v_a_944_ = v___x_956_;
goto v___jp_943_;
}
v___jp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_a_944_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_957_, lean_object* v___x_958_, lean_object* v_val_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_957_, v___x_958_, v_val_959_, v___y_960_);
lean_dec_ref(v___y_960_);
lean_dec(v_val_959_);
lean_dec_ref(v___x_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_963_, lean_object* v_x_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_get_set_stderr(v_h_963_);
lean_inc_ref(v___y_965_);
v___x_968_ = lean_apply_2(v_x_964_, v___y_965_, lean_box(0));
v___x_969_ = lean_get_set_stderr(v___x_967_);
lean_dec_ref(v___x_969_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_970_, lean_object* v_x_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_970_, v_x_971_, v___y_972_);
lean_dec_ref(v___y_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_975_, lean_object* v_h_976_, lean_object* v_x_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_976_, v_x_977_, v___y_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_981_, lean_object* v_h_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_981_, v_h_982_, v_x_983_, v___y_984_);
lean_dec_ref(v___y_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_987_, lean_object* v_x_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_get_set_stdin(v_h_987_);
lean_inc_ref(v___y_989_);
v___x_992_ = lean_apply_2(v_x_988_, v___y_989_, lean_box(0));
v___x_993_ = lean_get_set_stdin(v___x_991_);
lean_dec_ref(v___x_993_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_994_, v_x_995_, v___y_996_);
lean_dec_ref(v___y_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1001_ = lean_panic_fn_borrowed(v___x_1000_, v_msg_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_get_set_stdout(v_h_1002_);
lean_inc_ref(v___y_1004_);
v___x_1007_ = lean_apply_2(v_x_1003_, v___y_1004_, lean_box(0));
v___x_1008_ = lean_get_set_stdout(v___x_1006_);
lean_dec_ref(v___x_1008_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1009_, v_x_1010_, v___y_1011_);
lean_dec_ref(v___y_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_1014_, lean_object* v_h_1015_, lean_object* v_x_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1015_, v_x_1016_, v___y_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_h_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1020_, v_h_1021_, v_x_1022_, v___y_1023_);
lean_dec_ref(v___y_1023_);
return v_res_1025_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = l_ByteArray_empty;
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1026_);
return v___x_1028_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1032_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1033_ = lean_unsigned_to_nat(46u);
v___x_1034_ = lean_unsigned_to_nat(193u);
v___x_1035_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1036_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1037_ = l_mkPanicMessageWithDecl(v___x_1036_, v___x_1035_, v___x_1034_, v___x_1033_, v___x_1032_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1038_, uint8_t v_isolateStderr_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___y_1052_; 
v___x_1046_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1047_ = lean_st_mk_ref(v___x_1046_);
v___x_1048_ = lean_st_mk_ref(v___x_1046_);
v___x_1049_ = l_IO_FS_Stream_ofBuffer(v___x_1047_);
lean_inc(v___x_1048_);
v___x_1050_ = l_IO_FS_Stream_ofBuffer(v___x_1048_);
if (v_isolateStderr_1039_ == 0)
{
v___y_1052_ = v_x_1038_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1061_; 
lean_inc_ref(v___x_1050_);
v___x_1061_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1061_, 0, lean_box(0));
lean_closure_set(v___x_1061_, 1, v___x_1050_);
lean_closure_set(v___x_1061_, 2, v_x_1038_);
v___y_1052_ = v___x_1061_;
goto v___jp_1051_;
}
v___jp_1042_:
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___y_1044_);
lean_ctor_set(v___x_1045_, 1, v___y_1043_);
return v___x_1045_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_data_1056_; uint8_t v___x_1057_; 
v___x_1053_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1053_, 0, lean_box(0));
lean_closure_set(v___x_1053_, 1, v___x_1050_);
lean_closure_set(v___x_1053_, 2, v___y_1052_);
v___x_1054_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1049_, v___x_1053_, v___y_1040_);
v___x_1055_ = lean_st_ref_get(v___x_1048_);
lean_dec(v___x_1048_);
v_data_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_data_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = lean_string_validate_utf8(v_data_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v_data_1056_);
v___x_1058_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1059_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1058_);
v___y_1043_ = v___x_1054_;
v___y_1044_ = v___x_1059_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_string_from_utf8_unchecked(v_data_1056_);
v___y_1043_ = v___x_1054_;
v___y_1044_ = v___x_1060_;
goto v___jp_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1062_, lean_object* v_isolateStderr_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_isolateStderr_boxed_1066_; lean_object* v_res_1067_; 
v_isolateStderr_boxed_1066_ = lean_unbox(v_isolateStderr_1063_);
v_res_1067_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1062_, v_isolateStderr_boxed_1066_, v___y_1064_);
lean_dec_ref(v___y_1064_);
return v_res_1067_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = 1;
v___x_1077_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1078_ = l_Lean_Name_toString(v___x_1077_, v___x_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1079_, lean_object* v_revCmds_1080_, lean_object* v_cmdState_1081_, lean_object* v_beginPos_1082_, lean_object* v_snap_1083_, lean_object* v_cancelTk_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_env_1087_; lean_object* v_scopes_1088_; lean_object* v_usedQuotCtxts_1089_; lean_object* v_nextMacroScope_1090_; lean_object* v_maxRecDepth_1091_; lean_object* v_ngen_1092_; lean_object* v_auxDeclNGen_1093_; lean_object* v_infoState_1094_; lean_object* v_prevLinterStates_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1177_; 
v_env_1087_ = lean_ctor_get(v_cmdState_1081_, 0);
v_scopes_1088_ = lean_ctor_get(v_cmdState_1081_, 2);
v_usedQuotCtxts_1089_ = lean_ctor_get(v_cmdState_1081_, 3);
v_nextMacroScope_1090_ = lean_ctor_get(v_cmdState_1081_, 4);
v_maxRecDepth_1091_ = lean_ctor_get(v_cmdState_1081_, 5);
v_ngen_1092_ = lean_ctor_get(v_cmdState_1081_, 6);
v_auxDeclNGen_1093_ = lean_ctor_get(v_cmdState_1081_, 7);
v_infoState_1094_ = lean_ctor_get(v_cmdState_1081_, 8);
v_prevLinterStates_1095_ = lean_ctor_get(v_cmdState_1081_, 11);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_cmdState_1081_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1178_ = lean_ctor_get(v_cmdState_1081_, 12);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_cmdState_1081_, 10);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_cmdState_1081_, 9);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_cmdState_1081_, 1);
lean_dec(v_unused_1181_);
v___x_1097_ = v_cmdState_1081_;
v_isShared_1098_ = v_isSharedCheck_1177_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_prevLinterStates_1095_);
lean_inc(v_infoState_1094_);
lean_inc(v_auxDeclNGen_1093_);
lean_inc(v_ngen_1092_);
lean_inc(v_maxRecDepth_1091_);
lean_inc(v_nextMacroScope_1090_);
lean_inc(v_usedQuotCtxts_1089_);
lean_inc(v_scopes_1088_);
lean_inc(v_env_1087_);
lean_dec(v_cmdState_1081_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1177_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___f_1099_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1099_, 0, v_stx_1079_);
lean_closure_set(v___f_1099_, 1, v_revCmds_1080_);
v___x_1100_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1101_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1102_ = l_List_head_x21___redArg(v___x_1100_, v_scopes_1088_);
v___x_1103_ = l_Lean_MessageLog_empty;
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1106_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 12, v___x_1106_);
lean_ctor_set(v___x_1097_, 10, v___x_1106_);
lean_ctor_set(v___x_1097_, 9, v___x_1105_);
lean_ctor_set(v___x_1097_, 1, v___x_1103_);
v___x_1108_ = v___x_1097_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_env_1087_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_scopes_1088_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_usedQuotCtxts_1089_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_nextMacroScope_1090_);
lean_ctor_set(v_reuseFailAlloc_1176_, 5, v_maxRecDepth_1091_);
lean_ctor_set(v_reuseFailAlloc_1176_, 6, v_ngen_1092_);
lean_ctor_set(v_reuseFailAlloc_1176_, 7, v_auxDeclNGen_1093_);
lean_ctor_set(v_reuseFailAlloc_1176_, 8, v_infoState_1094_);
lean_ctor_set(v_reuseFailAlloc_1176_, 9, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1176_, 10, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1176_, 11, v_prevLinterStates_1095_);
lean_ctor_set(v_reuseFailAlloc_1176_, 12, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v_toProcessingContext_1110_; lean_object* v_fileName_1111_; lean_object* v_fileMap_1112_; lean_object* v_opts_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v_env_1121_; lean_object* v_scopes_1122_; lean_object* v_usedQuotCtxts_1123_; lean_object* v_nextMacroScope_1124_; lean_object* v_maxRecDepth_1125_; lean_object* v_ngen_1126_; lean_object* v_auxDeclNGen_1127_; lean_object* v_infoState_1128_; lean_object* v_traceState_1129_; lean_object* v_snapshotTasks_1130_; lean_object* v_prevLinterStates_1131_; lean_object* v_codeQualityEntryTasks_1132_; uint8_t v___y_1133_; lean_object* v_messages_1134_; lean_object* v___y_1143_; 
v___x_1109_ = lean_st_mk_ref(v___x_1108_);
v_toProcessingContext_1110_ = lean_ctor_get(v_a_1085_, 0);
v_fileName_1111_ = lean_ctor_get(v_toProcessingContext_1110_, 1);
v_fileMap_1112_ = lean_ctor_get(v_toProcessingContext_1110_, 2);
v_opts_1113_ = lean_ctor_get(v___x_1102_, 1);
lean_inc_ref(v_opts_1113_);
lean_dec(v___x_1102_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Lean_firstFrontendMacroScope;
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Lean_internal_cmdlineSnapshots;
v___x_1119_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1113_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1175_; 
lean_inc_ref(v_snap_1083_);
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_snap_1083_);
v___y_1143_ = v___x_1175_;
goto v___jp_1142_;
}
else
{
v___y_1143_ = v___x_1115_;
goto v___jp_1142_;
}
v___jp_1120_:
{
lean_object* v_new_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_new_1135_ = lean_ctor_get(v_snap_1083_, 1);
lean_inc(v_new_1135_);
lean_dec_ref(v_snap_1083_);
v___x_1136_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1136_, 0, v_env_1121_);
lean_ctor_set(v___x_1136_, 1, v_messages_1134_);
lean_ctor_set(v___x_1136_, 2, v_scopes_1122_);
lean_ctor_set(v___x_1136_, 3, v_usedQuotCtxts_1123_);
lean_ctor_set(v___x_1136_, 4, v_nextMacroScope_1124_);
lean_ctor_set(v___x_1136_, 5, v_maxRecDepth_1125_);
lean_ctor_set(v___x_1136_, 6, v_ngen_1126_);
lean_ctor_set(v___x_1136_, 7, v_auxDeclNGen_1127_);
lean_ctor_set(v___x_1136_, 8, v_infoState_1128_);
lean_ctor_set(v___x_1136_, 9, v_traceState_1129_);
lean_ctor_set(v___x_1136_, 10, v_snapshotTasks_1130_);
lean_ctor_set(v___x_1136_, 11, v_prevLinterStates_1131_);
lean_ctor_set(v___x_1136_, 12, v_codeQualityEntryTasks_1132_);
v___x_1137_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1138_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1139_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
lean_ctor_set(v___x_1139_, 2, v___x_1115_);
lean_ctor_set(v___x_1139_, 3, v___x_1105_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*4, v___y_1133_);
v___x_1140_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1101_, v___x_1139_);
v___x_1141_ = lean_io_promise_resolve(v___x_1140_, v_new_1135_);
lean_dec(v_new_1135_);
return v___x_1136_;
}
v___jp_1142_:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v_fst_1151_; lean_object* v___x_1152_; lean_object* v_env_1153_; lean_object* v_messages_1154_; lean_object* v_scopes_1155_; lean_object* v_usedQuotCtxts_1156_; lean_object* v_nextMacroScope_1157_; lean_object* v_maxRecDepth_1158_; lean_object* v_ngen_1159_; lean_object* v_auxDeclNGen_1160_; lean_object* v_infoState_1161_; lean_object* v_traceState_1162_; lean_object* v_snapshotTasks_1163_; lean_object* v_prevLinterStates_1164_; lean_object* v_codeQualityEntryTasks_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_cancelTk_1084_);
v___x_1145_ = 0;
lean_inc(v_beginPos_1082_);
lean_inc_ref(v_fileMap_1112_);
lean_inc_ref(v_fileName_1111_);
v___x_1146_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1146_, 0, v_fileName_1111_);
lean_ctor_set(v___x_1146_, 1, v_fileMap_1112_);
lean_ctor_set(v___x_1146_, 2, v___x_1104_);
lean_ctor_set(v___x_1146_, 3, v_beginPos_1082_);
lean_ctor_set(v___x_1146_, 4, v___x_1114_);
lean_ctor_set(v___x_1146_, 5, v___x_1115_);
lean_ctor_set(v___x_1146_, 6, v___x_1116_);
lean_ctor_set(v___x_1146_, 7, v___x_1117_);
lean_ctor_set(v___x_1146_, 8, v___y_1143_);
lean_ctor_set(v___x_1146_, 9, v___x_1144_);
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*10, v___x_1145_);
lean_inc(v___x_1109_);
v___f_1147_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1147_, 0, v___f_1099_);
lean_closure_set(v___f_1147_, 1, v___x_1146_);
lean_closure_set(v___f_1147_, 2, v___x_1109_);
v___x_1148_ = l_Lean_Core_stderrAsMessages;
v___x_1149_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1113_, v___x_1148_);
lean_dec_ref(v_opts_1113_);
v___x_1150_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1147_, v___x_1149_, v_a_1085_);
v_fst_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_fst_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_st_ref_get(v___x_1109_);
lean_dec(v___x_1109_);
v_env_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc_ref(v_env_1153_);
v_messages_1154_ = lean_ctor_get(v___x_1152_, 1);
lean_inc_ref(v_messages_1154_);
v_scopes_1155_ = lean_ctor_get(v___x_1152_, 2);
lean_inc(v_scopes_1155_);
v_usedQuotCtxts_1156_ = lean_ctor_get(v___x_1152_, 3);
lean_inc(v_usedQuotCtxts_1156_);
v_nextMacroScope_1157_ = lean_ctor_get(v___x_1152_, 4);
lean_inc(v_nextMacroScope_1157_);
v_maxRecDepth_1158_ = lean_ctor_get(v___x_1152_, 5);
lean_inc(v_maxRecDepth_1158_);
v_ngen_1159_ = lean_ctor_get(v___x_1152_, 6);
lean_inc_ref(v_ngen_1159_);
v_auxDeclNGen_1160_ = lean_ctor_get(v___x_1152_, 7);
lean_inc_ref(v_auxDeclNGen_1160_);
v_infoState_1161_ = lean_ctor_get(v___x_1152_, 8);
lean_inc_ref(v_infoState_1161_);
v_traceState_1162_ = lean_ctor_get(v___x_1152_, 9);
lean_inc_ref(v_traceState_1162_);
v_snapshotTasks_1163_ = lean_ctor_get(v___x_1152_, 10);
lean_inc_ref(v_snapshotTasks_1163_);
v_prevLinterStates_1164_ = lean_ctor_get(v___x_1152_, 11);
lean_inc(v_prevLinterStates_1164_);
v_codeQualityEntryTasks_1165_ = lean_ctor_get(v___x_1152_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1165_);
lean_dec(v___x_1152_);
v___x_1166_ = lean_string_utf8_byte_size(v_fst_1151_);
v___x_1167_ = lean_nat_dec_eq(v___x_1166_, v___x_1104_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc_ref(v_fileMap_1112_);
v___x_1168_ = l_Lean_FileMap_toPosition(v_fileMap_1112_, v_beginPos_1082_);
lean_dec(v_beginPos_1082_);
v___x_1169_ = 0;
v___x_1170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_fst_1151_);
v___x_1172_ = l_Lean_MessageData_ofFormat(v___x_1171_);
lean_inc_ref(v_fileName_1111_);
v___x_1173_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1173_, 0, v_fileName_1111_);
lean_ctor_set(v___x_1173_, 1, v___x_1168_);
lean_ctor_set(v___x_1173_, 2, v___x_1115_);
lean_ctor_set(v___x_1173_, 3, v___x_1170_);
lean_ctor_set(v___x_1173_, 4, v___x_1172_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*5, v___x_1145_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*5 + 1, v___x_1169_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*5 + 2, v___x_1145_);
v___x_1174_ = l_Lean_MessageLog_add(v___x_1173_, v_messages_1154_);
v_env_1121_ = v_env_1153_;
v_scopes_1122_ = v_scopes_1155_;
v_usedQuotCtxts_1123_ = v_usedQuotCtxts_1156_;
v_nextMacroScope_1124_ = v_nextMacroScope_1157_;
v_maxRecDepth_1125_ = v_maxRecDepth_1158_;
v_ngen_1126_ = v_ngen_1159_;
v_auxDeclNGen_1127_ = v_auxDeclNGen_1160_;
v_infoState_1128_ = v_infoState_1161_;
v_traceState_1129_ = v_traceState_1162_;
v_snapshotTasks_1130_ = v_snapshotTasks_1163_;
v_prevLinterStates_1131_ = v_prevLinterStates_1164_;
v_codeQualityEntryTasks_1132_ = v_codeQualityEntryTasks_1165_;
v___y_1133_ = v___x_1145_;
v_messages_1134_ = v___x_1174_;
goto v___jp_1120_;
}
else
{
lean_dec(v_fst_1151_);
lean_dec(v_beginPos_1082_);
v_env_1121_ = v_env_1153_;
v_scopes_1122_ = v_scopes_1155_;
v_usedQuotCtxts_1123_ = v_usedQuotCtxts_1156_;
v_nextMacroScope_1124_ = v_nextMacroScope_1157_;
v_maxRecDepth_1125_ = v_maxRecDepth_1158_;
v_ngen_1126_ = v_ngen_1159_;
v_auxDeclNGen_1127_ = v_auxDeclNGen_1160_;
v_infoState_1128_ = v_infoState_1161_;
v_traceState_1129_ = v_traceState_1162_;
v_snapshotTasks_1130_ = v_snapshotTasks_1163_;
v_prevLinterStates_1131_ = v_prevLinterStates_1164_;
v_codeQualityEntryTasks_1132_ = v_codeQualityEntryTasks_1165_;
v___y_1133_ = v___x_1145_;
v_messages_1134_ = v_messages_1154_;
goto v___jp_1120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1182_, lean_object* v_revCmds_1183_, lean_object* v_cmdState_1184_, lean_object* v_beginPos_1185_, lean_object* v_snap_1186_, lean_object* v_cancelTk_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1182_, v_revCmds_1183_, v_cmdState_1184_, v_beginPos_1185_, v_snap_1186_, v_cancelTk_1187_, v_a_1188_);
lean_dec_ref(v_a_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1191_, lean_object* v_h_1192_, lean_object* v_x_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1192_, v_x_1193_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_h_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1197_, v_h_1198_, v_x_1199_, v___y_1200_);
lean_dec_ref(v___y_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1203_, lean_object* v_x_1204_, uint8_t v_isolateStderr_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1204_, v_isolateStderr_1205_, v___y_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1209_, lean_object* v_x_1210_, lean_object* v_isolateStderr_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v_isolateStderr_boxed_1214_; lean_object* v_res_1215_; 
v_isolateStderr_boxed_1214_ = lean_unbox(v_isolateStderr_1211_);
v_res_1215_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1209_, v_x_1210_, v_isolateStderr_boxed_1214_, v___y_1212_);
lean_dec_ref(v___y_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1216_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1226_){
_start:
{
lean_object* v_toSnapshotTreeM_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_toSnapshotTreeM_1227_ = lean_ctor_get(v_a_1226_, 1);
lean_inc_ref(v_toSnapshotTreeM_1227_);
lean_dec_ref(v_a_1226_);
v___x_1228_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1229_ = lean_apply_1(v_toSnapshotTreeM_1227_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1230_){
_start:
{
lean_object* v_toSnapshot_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_toSnapshot_1231_ = lean_ctor_get(v_a_1230_, 0);
lean_inc_ref(v_toSnapshot_1231_);
lean_dec_ref(v_a_1230_);
v___x_1232_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1233_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1231_, v___x_1232_);
v___x_1234_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1237_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1238_ = l_Lean_Language_Snapshot_transform(v_a_1236_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1241_, lean_object* v_opt_1242_){
_start:
{
lean_object* v_name_1243_; lean_object* v_defValue_1244_; lean_object* v_map_1245_; lean_object* v___x_1246_; 
v_name_1243_ = lean_ctor_get(v_opt_1242_, 0);
v_defValue_1244_ = lean_ctor_get(v_opt_1242_, 1);
v_map_1245_ = lean_ctor_get(v_opts_1241_, 0);
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1245_, v_name_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_inc(v_defValue_1244_);
return v_defValue_1244_;
}
else
{
lean_object* v_val_1247_; 
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v___x_1246_, 1);
if (lean_obj_tag(v_val_1247_) == 3)
{
lean_object* v_v_1248_; 
v_v_1248_ = lean_ctor_get(v_val_1247_, 0);
lean_inc(v_v_1248_);
lean_dec_ref_known(v_val_1247_, 1);
return v_v_1248_;
}
else
{
lean_dec(v_val_1247_);
lean_inc(v_defValue_1244_);
return v_defValue_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1249_, lean_object* v_opt_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1249_, v_opt_1250_);
lean_dec_ref(v_opt_1250_);
lean_dec_ref(v_opts_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1254_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1252_, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1261_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1262_ = l_Lean_Name_append(v___x_1261_, v___x_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1263_, lean_object* v___x_1264_, uint8_t v_val_1265_, lean_object* v_val_1266_, lean_object* v_val_1267_, lean_object* v___x_1268_, lean_object* v___x_1269_, uint8_t v___x_1270_, lean_object* v_a_1271_, lean_object* v_pos_1272_, lean_object* v___x_1273_, lean_object* v_infoSt_1274_){
_start:
{
lean_object* v___y_1277_; lean_object* v_msgLog_1278_; lean_object* v___y_1284_; lean_object* v_trees_1316_; lean_object* v_size_1317_; uint8_t v___x_1318_; 
v_trees_1316_ = lean_ctor_get(v_infoSt_1274_, 2);
v_size_1317_ = lean_ctor_get(v_trees_1316_, 2);
v___x_1318_ = lean_nat_dec_lt(v___x_1269_, v_size_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = l_outOfBounds___redArg(v___x_1273_);
v___y_1284_ = v___x_1319_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1273_, v_trees_1316_, v___x_1269_);
v___y_1284_ = v___x_1320_;
goto v___jp_1283_;
}
v___jp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1278_);
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___y_1277_);
v___x_1281_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1263_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_ctor_set(v___x_1281_, 2, v___x_1280_);
lean_ctor_set(v___x_1281_, 3, v___x_1264_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*4, v_val_1265_);
v___x_1282_ = lean_io_promise_resolve(v___x_1281_, v_val_1266_);
return v___x_1282_;
}
v___jp_1283_:
{
lean_object* v_scopes_1285_; lean_object* v___x_1286_; lean_object* v_opts_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v_hasTrace_1291_; 
v_scopes_1285_ = lean_ctor_get(v_val_1267_, 2);
v___x_1286_ = l_List_head_x21___redArg(v___x_1268_, v_scopes_1285_);
v_opts_1287_ = lean_ctor_get(v___x_1286_, 1);
lean_inc_ref(v_opts_1287_);
lean_dec(v___x_1286_);
v___x_1288_ = l_Lean_MessageLog_empty;
v___x_1289_ = l_Lean_inheritedTraceOptions;
v___x_1290_ = lean_st_ref_get(v___x_1289_);
v_hasTrace_1291_ = lean_ctor_get_uint8(v_opts_1287_, sizeof(void*)*1);
if (v_hasTrace_1291_ == 0)
{
lean_dec(v___x_1290_);
lean_dec_ref(v_opts_1287_);
lean_dec(v___x_1269_);
v___y_1277_ = v___y_1284_;
v_msgLog_1278_ = v___x_1288_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1293_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1294_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1295_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1290_, v_opts_1287_, v___x_1294_);
lean_dec_ref(v_opts_1287_);
lean_dec(v___x_1290_);
if (v___x_1295_ == 0)
{
lean_dec(v___x_1269_);
v___y_1277_ = v___y_1284_;
v_msgLog_1278_ = v___x_1288_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_box(0);
lean_inc_ref(v___y_1284_);
v___x_1297_ = l_Lean_Elab_InfoTree_format(v___y_1284_, v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; double v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_toProcessingContext_1302_; lean_object* v_fileName_1303_; lean_object* v_fileMap_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = lean_float_of_nat(v___x_1269_);
v___x_1300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1301_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1301_, 0, v___x_1292_);
lean_ctor_set(v___x_1301_, 1, v___x_1296_);
lean_ctor_set(v___x_1301_, 2, v___x_1300_);
lean_ctor_set_float(v___x_1301_, sizeof(void*)*3, v___x_1299_);
lean_ctor_set_float(v___x_1301_, sizeof(void*)*3 + 8, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*3 + 16, v___x_1270_);
v_toProcessingContext_1302_ = lean_ctor_get(v_a_1271_, 0);
v_fileName_1303_ = lean_ctor_get(v_toProcessingContext_1302_, 1);
v_fileMap_1304_ = lean_ctor_get(v_toProcessingContext_1302_, 2);
v___x_1305_ = l_Lean_MessageData_nil;
v___x_1306_ = l_Lean_MessageData_ofFormat(v_a_1298_);
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_mk_empty_array_with_capacity(v___x_1307_);
v___x_1309_ = lean_array_push(v___x_1308_, v___x_1306_);
v___x_1310_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1301_);
lean_ctor_set(v___x_1310_, 1, v___x_1305_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1293_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
lean_inc_ref(v_fileMap_1304_);
v___x_1312_ = l_Lean_FileMap_toPosition(v_fileMap_1304_, v_pos_1272_);
v___x_1313_ = 0;
lean_inc_ref(v_fileName_1303_);
v___x_1314_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1314_, 0, v_fileName_1303_);
lean_ctor_set(v___x_1314_, 1, v___x_1312_);
lean_ctor_set(v___x_1314_, 2, v___x_1296_);
lean_ctor_set(v___x_1314_, 3, v___x_1300_);
lean_ctor_set(v___x_1314_, 4, v___x_1311_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5, v_val_1265_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5 + 1, v___x_1313_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5 + 2, v_val_1265_);
v___x_1315_ = l_Lean_MessageLog_add(v___x_1314_, v___x_1288_);
v___y_1277_ = v___y_1284_;
v_msgLog_1278_ = v___x_1315_;
goto v___jp_1276_;
}
else
{
lean_dec_ref_known(v___x_1297_, 1);
lean_dec(v___x_1269_);
v___y_1277_ = v___y_1284_;
v_msgLog_1278_ = v___x_1288_;
goto v___jp_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_val_1323_, lean_object* v_val_1324_, lean_object* v_val_1325_, lean_object* v___x_1326_, lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_a_1329_, lean_object* v_pos_1330_, lean_object* v___x_1331_, lean_object* v_infoSt_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v_val_36487__boxed_1334_; uint8_t v___x_36492__boxed_1335_; lean_object* v_res_1336_; 
v_val_36487__boxed_1334_ = lean_unbox(v_val_1323_);
v___x_36492__boxed_1335_ = lean_unbox(v___x_1328_);
v_res_1336_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1321_, v___x_1322_, v_val_36487__boxed_1334_, v_val_1324_, v_val_1325_, v___x_1326_, v___x_1327_, v___x_36492__boxed_1335_, v_a_1329_, v_pos_1330_, v___x_1331_, v_infoSt_1332_);
lean_dec_ref(v_infoSt_1332_);
lean_dec_ref(v___x_1331_);
lean_dec(v_pos_1330_);
lean_dec_ref(v_a_1329_);
lean_dec_ref(v___x_1326_);
lean_dec_ref(v_val_1325_);
lean_dec(v_val_1324_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v___x_1339_, uint8_t v_val_1340_, lean_object* v_as_1341_, size_t v_sz_1342_, size_t v_i_1343_, lean_object* v_b_1344_){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v___x_1339_);
lean_dec_ref(v___x_1337_);
return v_b_1344_;
}
else
{
lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1365_; 
v_snd_1347_ = lean_ctor_get(v_b_1344_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_b_1344_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_b_1344_, 0);
lean_dec(v_unused_1366_);
v___x_1349_ = v_b_1344_;
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_dec(v_b_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_a_1351_; lean_object* v_msg_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v_a_1351_ = lean_array_uget_borrowed(v_as_1341_, v_i_1343_);
v_msg_1352_ = lean_ctor_get(v_a_1351_, 1);
v___x_1353_ = lean_box(0);
lean_inc_ref(v___x_1337_);
v___x_1354_ = l_Lean_FileMap_toPosition(v___x_1337_, v___x_1338_);
v___x_1355_ = 0;
v___x_1356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1352_);
lean_inc_ref(v___x_1339_);
v___x_1357_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1357_, 0, v___x_1339_);
lean_ctor_set(v___x_1357_, 1, v___x_1354_);
lean_ctor_set(v___x_1357_, 2, v___x_1353_);
lean_ctor_set(v___x_1357_, 3, v___x_1356_);
lean_ctor_set(v___x_1357_, 4, v_msg_1352_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*5, v_val_1340_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*5 + 1, v___x_1355_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*5 + 2, v_val_1340_);
v___x_1358_ = l_Lean_MessageLog_add(v___x_1357_, v_snd_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1358_);
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1360_ = v___x_1349_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
size_t v___x_1361_; size_t v___x_1362_; 
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_add(v_i_1343_, v___x_1361_);
v_i_1343_ = v___x_1362_;
v_b_1344_ = v___x_1360_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v___x_1369_, lean_object* v_val_1370_, lean_object* v_as_1371_, lean_object* v_sz_1372_, lean_object* v_i_1373_, lean_object* v_b_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v_val_36600__boxed_1376_; size_t v_sz_boxed_1377_; size_t v_i_boxed_1378_; lean_object* v_res_1379_; 
v_val_36600__boxed_1376_ = lean_unbox(v_val_1370_);
v_sz_boxed_1377_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1378_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1367_, v___x_1368_, v___x_1369_, v_val_36600__boxed_1376_, v_as_1371_, v_sz_boxed_1377_, v_i_boxed_1378_, v_b_1374_);
lean_dec_ref(v_as_1371_);
lean_dec(v___x_1368_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, uint8_t v_val_1383_, lean_object* v_as_1384_, size_t v_sz_1385_, size_t v_i_1386_, lean_object* v_b_1387_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_usize_dec_lt(v_i_1386_, v_sz_1385_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v___x_1382_);
lean_dec_ref(v___x_1380_);
return v_b_1387_;
}
else
{
lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1408_; 
v_snd_1390_ = lean_ctor_get(v_b_1387_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_b_1387_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_b_1387_, 0);
lean_dec(v_unused_1409_);
v___x_1392_ = v_b_1387_;
v_isShared_1393_ = v_isSharedCheck_1408_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_dec(v_b_1387_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1408_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_a_1394_; lean_object* v_msg_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v_a_1394_ = lean_array_uget_borrowed(v_as_1384_, v_i_1386_);
v_msg_1395_ = lean_ctor_get(v_a_1394_, 1);
v___x_1396_ = lean_box(0);
lean_inc_ref(v___x_1380_);
v___x_1397_ = l_Lean_FileMap_toPosition(v___x_1380_, v___x_1381_);
v___x_1398_ = 0;
v___x_1399_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1395_);
lean_inc_ref(v___x_1382_);
v___x_1400_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1400_, 0, v___x_1382_);
lean_ctor_set(v___x_1400_, 1, v___x_1397_);
lean_ctor_set(v___x_1400_, 2, v___x_1396_);
lean_ctor_set(v___x_1400_, 3, v___x_1399_);
lean_ctor_set(v___x_1400_, 4, v_msg_1395_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*5, v_val_1383_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*5 + 1, v___x_1398_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*5 + 2, v_val_1383_);
v___x_1401_ = l_Lean_MessageLog_add(v___x_1400_, v_snd_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___x_1401_);
lean_ctor_set(v___x_1392_, 0, v___x_1396_);
v___x_1403_ = v___x_1392_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_add(v_i_1386_, v___x_1404_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1380_, v___x_1381_, v___x_1382_, v_val_1383_, v_as_1384_, v_sz_1385_, v___x_1405_, v___x_1403_);
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v_val_1413_, lean_object* v_as_1414_, lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v_val_36652__boxed_1419_; size_t v_sz_boxed_1420_; size_t v_i_boxed_1421_; lean_object* v_res_1422_; 
v_val_36652__boxed_1419_ = lean_unbox(v_val_1413_);
v_sz_boxed_1420_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1421_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1410_, v___x_1411_, v___x_1412_, v_val_36652__boxed_1419_, v_as_1414_, v_sz_boxed_1420_, v_i_boxed_1421_, v_b_1417_);
lean_dec_ref(v_as_1414_);
lean_dec(v___x_1411_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, uint8_t v_val_1427_, lean_object* v_n_1428_, lean_object* v_b_1429_){
_start:
{
if (lean_obj_tag(v_n_1428_) == 0)
{
lean_object* v_cs_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; size_t v_sz_1434_; size_t v___x_1435_; lean_object* v___x_1436_; lean_object* v_fst_1437_; 
v_cs_1431_ = lean_ctor_get(v_n_1428_, 0);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v_b_1429_);
v_sz_1434_ = lean_array_size(v_cs_1431_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1423_, v___x_1424_, v___x_1425_, v___x_1426_, v_val_1427_, v_cs_1431_, v_sz_1434_, v___x_1435_, v___x_1433_);
v_fst_1437_ = lean_ctor_get(v___x_1436_, 0);
if (lean_obj_tag(v_fst_1437_) == 0)
{
lean_object* v_snd_1438_; lean_object* v___x_1439_; 
v_snd_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_snd_1438_);
lean_dec_ref(v___x_1436_);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_snd_1438_);
return v___x_1439_;
}
else
{
lean_object* v_val_1440_; 
lean_inc_ref(v_fst_1437_);
lean_dec_ref(v___x_1436_);
v_val_1440_ = lean_ctor_get(v_fst_1437_, 0);
lean_inc(v_val_1440_);
lean_dec_ref_known(v_fst_1437_, 1);
return v_val_1440_;
}
}
else
{
lean_object* v_vs_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; size_t v_sz_1444_; size_t v___x_1445_; lean_object* v___x_1446_; lean_object* v_fst_1447_; 
v_vs_1441_ = lean_ctor_get(v_n_1428_, 0);
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v_b_1429_);
v_sz_1444_ = lean_array_size(v_vs_1441_);
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1424_, v___x_1425_, v___x_1426_, v_val_1427_, v_vs_1441_, v_sz_1444_, v___x_1445_, v___x_1443_);
v_fst_1447_ = lean_ctor_get(v___x_1446_, 0);
if (lean_obj_tag(v_fst_1447_) == 0)
{
lean_object* v_snd_1448_; lean_object* v___x_1449_; 
v_snd_1448_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_snd_1448_);
lean_dec_ref(v___x_1446_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_snd_1448_);
return v___x_1449_;
}
else
{
lean_object* v_val_1450_; 
lean_inc_ref(v_fst_1447_);
lean_dec_ref(v___x_1446_);
v_val_1450_ = lean_ctor_get(v_fst_1447_, 0);
lean_inc(v_val_1450_);
lean_dec_ref_known(v_fst_1447_, 1);
return v_val_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1451_, lean_object* v___x_1452_, lean_object* v___x_1453_, lean_object* v___x_1454_, uint8_t v_val_1455_, lean_object* v_as_1456_, size_t v_sz_1457_, size_t v_i_1458_, lean_object* v_b_1459_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_lt(v_i_1458_, v_sz_1457_);
if (v___x_1461_ == 0)
{
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___x_1452_);
return v_b_1459_;
}
else
{
lean_object* v_snd_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1480_; 
v_snd_1462_ = lean_ctor_get(v_b_1459_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_b_1459_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_b_1459_, 0);
lean_dec(v_unused_1481_);
v___x_1464_ = v_b_1459_;
v_isShared_1465_ = v_isSharedCheck_1480_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snd_1462_);
lean_dec(v_b_1459_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1480_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v_a_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_box(0);
v_a_1467_ = lean_array_uget_borrowed(v_as_1456_, v_i_1458_);
lean_inc(v_snd_1462_);
lean_inc_ref(v___x_1454_);
lean_inc_ref(v___x_1452_);
v___x_1468_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1451_, v___x_1452_, v___x_1453_, v___x_1454_, v_val_1455_, v_a_1467_, v_snd_1462_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___x_1452_);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1469_);
v___x_1471_ = v___x_1464_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_snd_1462_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; 
lean_dec(v_snd_1462_);
v_a_1473_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1468_, 1);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v_a_1473_);
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1473_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
size_t v___x_1476_; size_t v___x_1477_; 
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_add(v_i_1458_, v___x_1476_);
v_i_1458_ = v___x_1477_;
v_b_1459_ = v___x_1475_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, lean_object* v___x_1485_, lean_object* v_val_1486_, lean_object* v_as_1487_, lean_object* v_sz_1488_, lean_object* v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v_val_36703__boxed_1492_; size_t v_sz_boxed_1493_; size_t v_i_boxed_1494_; lean_object* v_res_1495_; 
v_val_36703__boxed_1492_ = lean_unbox(v_val_1486_);
v_sz_boxed_1493_ = lean_unbox_usize(v_sz_1488_);
lean_dec(v_sz_1488_);
v_i_boxed_1494_ = lean_unbox_usize(v_i_1489_);
lean_dec(v_i_1489_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1482_, v___x_1483_, v___x_1484_, v___x_1485_, v_val_36703__boxed_1492_, v_as_1487_, v_sz_boxed_1493_, v_i_boxed_1494_, v_b_1490_);
lean_dec_ref(v_as_1487_);
lean_dec(v___x_1484_);
lean_dec_ref(v_init_1482_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1496_, lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v_val_1500_, lean_object* v_n_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_val_36719__boxed_1504_; lean_object* v_res_1505_; 
v_val_36719__boxed_1504_ = lean_unbox(v_val_1500_);
v_res_1505_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1496_, v___x_1497_, v___x_1498_, v___x_1499_, v_val_36719__boxed_1504_, v_n_1501_, v_b_1502_);
lean_dec_ref(v_n_1501_);
lean_dec(v___x_1498_);
lean_dec_ref(v_init_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v___x_1508_, uint8_t v_val_1509_, lean_object* v_as_1510_, size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_b_1513_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1515_ == 0)
{
lean_dec_ref(v___x_1508_);
lean_dec_ref(v___x_1506_);
return v_b_1513_;
}
else
{
lean_object* v_snd_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1534_; 
v_snd_1516_ = lean_ctor_get(v_b_1513_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_b_1513_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_b_1513_, 0);
lean_dec(v_unused_1535_);
v___x_1518_ = v_b_1513_;
v_isShared_1519_ = v_isSharedCheck_1534_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snd_1516_);
lean_dec(v_b_1513_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1534_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_a_1520_; lean_object* v_msg_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v_a_1520_ = lean_array_uget_borrowed(v_as_1510_, v_i_1512_);
v_msg_1521_ = lean_ctor_get(v_a_1520_, 1);
v___x_1522_ = lean_box(0);
lean_inc_ref(v___x_1506_);
v___x_1523_ = l_Lean_FileMap_toPosition(v___x_1506_, v___x_1507_);
v___x_1524_ = 0;
v___x_1525_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1521_);
lean_inc_ref(v___x_1508_);
v___x_1526_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1526_, 0, v___x_1508_);
lean_ctor_set(v___x_1526_, 1, v___x_1523_);
lean_ctor_set(v___x_1526_, 2, v___x_1522_);
lean_ctor_set(v___x_1526_, 3, v___x_1525_);
lean_ctor_set(v___x_1526_, 4, v_msg_1521_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*5, v_val_1509_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*5 + 1, v___x_1524_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*5 + 2, v_val_1509_);
v___x_1527_ = l_Lean_MessageLog_add(v___x_1526_, v_snd_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v___x_1527_);
lean_ctor_set(v___x_1518_, 0, v___x_1522_);
v___x_1529_ = v___x_1518_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
size_t v___x_1530_; size_t v___x_1531_; 
v___x_1530_ = ((size_t)1ULL);
v___x_1531_ = lean_usize_add(v_i_1512_, v___x_1530_);
v_i_1512_ = v___x_1531_;
v_b_1513_ = v___x_1529_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1536_, lean_object* v___x_1537_, lean_object* v___x_1538_, lean_object* v_val_1539_, lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v_val_36801__boxed_1545_; size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v_val_36801__boxed_1545_ = lean_unbox(v_val_1539_);
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1536_, v___x_1537_, v___x_1538_, v_val_36801__boxed_1545_, v_as_1540_, v_sz_boxed_1546_, v_i_boxed_1547_, v_b_1543_);
lean_dec_ref(v_as_1540_);
lean_dec(v___x_1537_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1549_, lean_object* v___x_1550_, lean_object* v___x_1551_, uint8_t v_val_1552_, lean_object* v_as_1553_, size_t v_sz_1554_, size_t v_i_1555_, lean_object* v_b_1556_){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_usize_dec_lt(v_i_1555_, v_sz_1554_);
if (v___x_1558_ == 0)
{
lean_dec_ref(v___x_1551_);
lean_dec_ref(v___x_1549_);
return v_b_1556_;
}
else
{
lean_object* v_snd_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1577_; 
v_snd_1559_ = lean_ctor_get(v_b_1556_, 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_b_1556_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_b_1556_, 0);
lean_dec(v_unused_1578_);
v___x_1561_ = v_b_1556_;
v_isShared_1562_ = v_isSharedCheck_1577_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snd_1559_);
lean_dec(v_b_1556_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1577_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_a_1563_; lean_object* v_msg_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v_a_1563_ = lean_array_uget_borrowed(v_as_1553_, v_i_1555_);
v_msg_1564_ = lean_ctor_get(v_a_1563_, 1);
v___x_1565_ = lean_box(0);
lean_inc_ref(v___x_1549_);
v___x_1566_ = l_Lean_FileMap_toPosition(v___x_1549_, v___x_1550_);
v___x_1567_ = 0;
v___x_1568_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1564_);
lean_inc_ref(v___x_1551_);
v___x_1569_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1569_, 0, v___x_1551_);
lean_ctor_set(v___x_1569_, 1, v___x_1566_);
lean_ctor_set(v___x_1569_, 2, v___x_1565_);
lean_ctor_set(v___x_1569_, 3, v___x_1568_);
lean_ctor_set(v___x_1569_, 4, v_msg_1564_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*5, v_val_1552_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*5 + 1, v___x_1567_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*5 + 2, v_val_1552_);
v___x_1570_ = l_Lean_MessageLog_add(v___x_1569_, v_snd_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___x_1570_);
lean_ctor_set(v___x_1561_, 0, v___x_1565_);
v___x_1572_ = v___x_1561_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = ((size_t)1ULL);
v___x_1574_ = lean_usize_add(v_i_1555_, v___x_1573_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1549_, v___x_1550_, v___x_1551_, v_val_1552_, v_as_1553_, v_sz_1554_, v___x_1574_, v___x_1572_);
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1579_, lean_object* v___x_1580_, lean_object* v___x_1581_, lean_object* v_val_1582_, lean_object* v_as_1583_, lean_object* v_sz_1584_, lean_object* v_i_1585_, lean_object* v_b_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v_val_36853__boxed_1588_; size_t v_sz_boxed_1589_; size_t v_i_boxed_1590_; lean_object* v_res_1591_; 
v_val_36853__boxed_1588_ = lean_unbox(v_val_1582_);
v_sz_boxed_1589_ = lean_unbox_usize(v_sz_1584_);
lean_dec(v_sz_1584_);
v_i_boxed_1590_ = lean_unbox_usize(v_i_1585_);
lean_dec(v_i_1585_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1579_, v___x_1580_, v___x_1581_, v_val_36853__boxed_1588_, v_as_1583_, v_sz_boxed_1589_, v_i_boxed_1590_, v_b_1586_);
lean_dec_ref(v_as_1583_);
lean_dec(v___x_1580_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, uint8_t v_val_1595_, lean_object* v_t_1596_, lean_object* v_init_1597_){
_start:
{
lean_object* v_root_1599_; lean_object* v_tail_1600_; lean_object* v___x_1601_; 
v_root_1599_ = lean_ctor_get(v_t_1596_, 0);
v_tail_1600_ = lean_ctor_get(v_t_1596_, 1);
lean_inc_ref(v___x_1594_);
lean_inc_ref(v___x_1592_);
lean_inc_ref(v_init_1597_);
v___x_1601_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1597_, v___x_1592_, v___x_1593_, v___x_1594_, v_val_1595_, v_root_1599_, v_init_1597_);
lean_dec_ref(v_init_1597_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; 
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1592_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
return v_a_1602_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; 
v_a_1603_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v_a_1603_);
v_sz_1606_ = lean_array_size(v_tail_1600_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1592_, v___x_1593_, v___x_1594_, v_val_1595_, v_tail_1600_, v_sz_1606_, v___x_1607_, v___x_1605_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
if (lean_obj_tag(v_fst_1609_) == 0)
{
lean_object* v_snd_1610_; 
v_snd_1610_ = lean_ctor_get(v___x_1608_, 1);
lean_inc(v_snd_1610_);
lean_dec_ref(v___x_1608_);
return v_snd_1610_;
}
else
{
lean_object* v_val_1611_; 
lean_inc_ref(v_fst_1609_);
lean_dec_ref(v___x_1608_);
v_val_1611_ = lean_ctor_get(v_fst_1609_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v_fst_1609_, 1);
return v_val_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1612_, lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_val_1615_, lean_object* v_t_1616_, lean_object* v_init_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v_val_36904__boxed_1619_; lean_object* v_res_1620_; 
v_val_36904__boxed_1619_ = lean_unbox(v_val_1615_);
v_res_1620_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1612_, v___x_1613_, v___x_1614_, v_val_36904__boxed_1619_, v_t_1616_, v_init_1617_);
lean_dec_ref(v_t_1616_);
lean_dec(v___x_1613_);
return v_res_1620_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = l_Lean_firstFrontendMacroScope;
v___x_1623_ = lean_nat_add(v___x_1622_, v___x_1621_);
return v___x_1623_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1634_, lean_object* v_opts_1635_, lean_object* v___x_1636_, lean_object* v___x_1637_, lean_object* v___x_1638_, size_t v___x_1639_, uint8_t v___x_1640_, lean_object* v_env_1641_, lean_object* v___x_1642_, lean_object* v___x_1643_, lean_object* v_pos_1644_, uint8_t v_val_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v___x_1650_, uint8_t v___x_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_toProcessingContext_1654_; lean_object* v_fileName_1655_; lean_object* v_fileMap_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint16_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_fileName_1680_; lean_object* v_fileMap_1681_; lean_object* v_currNamespace_1682_; lean_object* v_openDecls_1683_; lean_object* v_initHeartbeats_1684_; lean_object* v_maxHeartbeats_1685_; lean_object* v_quotContext_1686_; lean_object* v_currMacroScope_1687_; lean_object* v_cancelTk_x3f_1688_; lean_object* v_inheritedTraceOptions_1689_; lean_object* v_currRecDepth_1690_; lean_object* v_ref_1691_; uint8_t v_suppressElabErrors_1692_; uint8_t v_isRecordingDeps_1693_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___y_1713_; uint8_t v___y_1735_; uint8_t v___y_1736_; lean_object* v_env_1737_; uint8_t v___x_1738_; uint8_t v___y_1740_; uint16_t v___x_1741_; uint16_t v___x_1742_; uint16_t v___x_1743_; uint8_t v___x_1744_; 
v_toProcessingContext_1654_ = lean_ctor_get(v_a_1634_, 0);
v_fileName_1655_ = lean_ctor_get(v_toProcessingContext_1654_, 1);
v_fileMap_1656_ = lean_ctor_get(v_toProcessingContext_1654_, 2);
v___x_1657_ = lean_box(0);
v___x_1658_ = l_Lean_Core_getMaxHeartbeats(v_opts_1635_);
v___x_1659_ = l_Lean_firstFrontendMacroScope;
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Lean_OptionFlags_ofOptions(v_opts_1635_);
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1664_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1636_);
v___x_1665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1636_);
lean_ctor_set(v___x_1665_, 1, v___x_1662_);
lean_ctor_set(v___x_1665_, 2, v___x_1657_);
v___x_1666_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1667_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1637_);
v___x_1669_ = l_Lean_Options_empty;
lean_inc_n(v___x_1637_, 5);
lean_inc_ref_n(v___x_1668_, 3);
v___x_1670_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
lean_ctor_set(v___x_1670_, 2, v___x_1668_);
lean_ctor_set(v___x_1670_, 3, v___x_1637_);
lean_ctor_set(v___x_1670_, 4, v___x_1637_);
lean_ctor_set(v___x_1670_, 5, v___x_1637_);
v___x_1671_ = lean_mk_empty_array_with_capacity(v___x_1638_);
lean_inc_ref(v___x_1671_);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v___x_1671_);
lean_ctor_set(v___x_1673_, 2, v___x_1637_);
lean_ctor_set(v___x_1673_, 3, v___x_1637_);
lean_ctor_set_usize(v___x_1673_, 4, v___x_1639_);
v___x_1674_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1673_, 2);
v___x_1675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1673_);
lean_ctor_set(v___x_1675_, 2, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1666_);
lean_ctor_set(v___x_1676_, 1, v___x_1666_);
lean_ctor_set(v___x_1676_, 2, v___x_1673_);
lean_ctor_set_uint8(v___x_1676_, sizeof(void*)*3, v___x_1640_);
lean_inc_ref(v___x_1642_);
v___x_1677_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1677_, 0, v_env_1641_);
lean_ctor_set(v___x_1677_, 1, v___x_1663_);
lean_ctor_set(v___x_1677_, 2, v___x_1664_);
lean_ctor_set(v___x_1677_, 3, v___x_1665_);
lean_ctor_set(v___x_1677_, 4, v___x_1642_);
lean_ctor_set(v___x_1677_, 5, v___x_1667_);
lean_ctor_set(v___x_1677_, 6, v___x_1670_);
lean_ctor_set(v___x_1677_, 7, v___x_1675_);
lean_ctor_set(v___x_1677_, 8, v___x_1676_);
lean_ctor_set(v___x_1677_, 9, v___x_1668_);
v___x_1678_ = lean_st_mk_ref(v___x_1677_);
v___x_1710_ = lean_st_ref_get(v___x_1649_);
v___x_1711_ = lean_st_ref_get(v___x_1678_);
v_env_1737_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_env_1737_);
lean_dec(v___x_1711_);
v___x_1738_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1737_);
lean_dec_ref(v_env_1737_);
v___x_1741_ = 512;
v___x_1742_ = lean_uint16_land(v___x_1661_, v___x_1741_);
v___x_1743_ = 0;
v___x_1744_ = lean_uint16_dec_eq(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
if (v___x_1651_ == 0)
{
v___y_1740_ = v___x_1651_;
goto v___jp_1739_;
}
else
{
v___y_1735_ = v___x_1651_;
v___y_1736_ = v___x_1738_;
goto v___jp_1734_;
}
}
else
{
v___y_1740_ = v_val_1645_;
goto v___jp_1739_;
}
v___jp_1679_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1694_ = l_Lean_maxRecDepth;
v___x_1695_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1635_, v___x_1694_);
lean_inc(v_currMacroScope_1687_);
lean_inc(v_openDecls_1683_);
v___x_1696_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1696_, 0, v_fileName_1680_);
lean_ctor_set(v___x_1696_, 1, v_fileMap_1681_);
lean_ctor_set(v___x_1696_, 2, v_opts_1635_);
lean_ctor_set(v___x_1696_, 3, v___x_1695_);
lean_ctor_set(v___x_1696_, 4, v_currNamespace_1682_);
lean_ctor_set(v___x_1696_, 5, v_openDecls_1683_);
lean_ctor_set(v___x_1696_, 6, v_initHeartbeats_1684_);
lean_ctor_set(v___x_1696_, 7, v_maxHeartbeats_1685_);
lean_ctor_set(v___x_1696_, 8, v_quotContext_1686_);
lean_ctor_set(v___x_1696_, 9, v_currMacroScope_1687_);
lean_ctor_set(v___x_1696_, 10, v_cancelTk_x3f_1688_);
lean_ctor_set(v___x_1696_, 11, v_inheritedTraceOptions_1689_);
lean_inc(v_ref_1691_);
v___x_1697_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v_currRecDepth_1690_);
lean_ctor_set(v___x_1697_, 2, v_ref_1691_);
lean_ctor_set_uint16(v___x_1697_, sizeof(void*)*3, v___x_1661_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*3 + 2, v_suppressElabErrors_1692_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*3 + 3, v_isRecordingDeps_1693_);
v___x_1698_ = l_Lean_Language_SnapshotTree_trace(v___x_1643_, v___x_1697_, v___x_1678_);
lean_dec_ref_known(v___x_1697_, 3);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v___x_1699_; lean_object* v_traceState_1700_; lean_object* v_traces_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec_ref_known(v___x_1698_, 1);
lean_dec_ref(v___x_1648_);
v___x_1699_ = lean_st_ref_get(v___x_1678_);
lean_dec(v___x_1678_);
v_traceState_1700_ = lean_ctor_get(v___x_1699_, 4);
lean_inc_ref(v_traceState_1700_);
lean_dec(v___x_1699_);
v_traces_1701_ = lean_ctor_get(v_traceState_1700_, 0);
lean_inc_ref(v_traces_1701_);
lean_dec_ref(v_traceState_1700_);
v___x_1702_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1655_);
lean_inc_ref(v_fileMap_1656_);
v___x_1703_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1656_, v_pos_1644_, v_fileName_1655_, v_val_1645_, v_traces_1701_, v___x_1702_);
lean_dec_ref(v_traces_1701_);
v___x_1704_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1705_, 0, v___x_1646_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
lean_ctor_set(v___x_1705_, 2, v___x_1647_);
lean_ctor_set(v___x_1705_, 3, v___x_1642_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*4, v_val_1645_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___x_1668_);
v___x_1707_ = lean_task_pure(v___x_1706_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1698_, 1);
lean_dec(v___x_1678_);
lean_dec(v___x_1647_);
lean_dec_ref(v___x_1646_);
lean_dec_ref(v___x_1642_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1648_);
lean_ctor_set(v___x_1708_, 1, v___x_1668_);
v___x_1709_ = lean_task_pure(v___x_1708_);
return v___x_1709_;
}
}
v___jp_1712_:
{
lean_object* v___x_1714_; lean_object* v_env_1715_; lean_object* v_nextMacroScope_1716_; lean_object* v_ngen_1717_; lean_object* v_auxDeclNGen_1718_; lean_object* v_traceState_1719_; lean_object* v_recordedDeps_1720_; lean_object* v_messages_1721_; lean_object* v_infoState_1722_; lean_object* v_snapshotTasks_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
v___x_1714_ = lean_st_ref_take(v___x_1678_);
v_env_1715_ = lean_ctor_get(v___x_1714_, 0);
v_nextMacroScope_1716_ = lean_ctor_get(v___x_1714_, 1);
v_ngen_1717_ = lean_ctor_get(v___x_1714_, 2);
v_auxDeclNGen_1718_ = lean_ctor_get(v___x_1714_, 3);
v_traceState_1719_ = lean_ctor_get(v___x_1714_, 4);
v_recordedDeps_1720_ = lean_ctor_get(v___x_1714_, 6);
v_messages_1721_ = lean_ctor_get(v___x_1714_, 7);
v_infoState_1722_ = lean_ctor_get(v___x_1714_, 8);
v_snapshotTasks_1723_ = lean_ctor_get(v___x_1714_, 9);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v___x_1714_, 5);
lean_dec(v_unused_1733_);
v___x_1725_ = v___x_1714_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_snapshotTasks_1723_);
lean_inc(v_infoState_1722_);
lean_inc(v_messages_1721_);
lean_inc(v_recordedDeps_1720_);
lean_inc(v_traceState_1719_);
lean_inc(v_auxDeclNGen_1718_);
lean_inc(v_ngen_1717_);
lean_inc(v_nextMacroScope_1716_);
lean_inc(v_env_1715_);
lean_dec(v___x_1714_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Kernel_enableDiag(v_env_1715_, v___y_1713_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 5, v___x_1667_);
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_nextMacroScope_1716_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_ngen_1717_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_auxDeclNGen_1718_);
lean_ctor_set(v_reuseFailAlloc_1731_, 4, v_traceState_1719_);
lean_ctor_set(v_reuseFailAlloc_1731_, 5, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1731_, 6, v_recordedDeps_1720_);
lean_ctor_set(v_reuseFailAlloc_1731_, 7, v_messages_1721_);
lean_ctor_set(v_reuseFailAlloc_1731_, 8, v_infoState_1722_);
lean_ctor_set(v_reuseFailAlloc_1731_, 9, v_snapshotTasks_1723_);
v___x_1729_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_st_ref_put(v___x_1678_, v___x_1729_);
lean_inc(v___x_1637_);
lean_inc(v___x_1636_);
lean_inc_ref(v_fileMap_1656_);
lean_inc_ref(v_fileName_1655_);
v_fileName_1680_ = v_fileName_1655_;
v_fileMap_1681_ = v_fileMap_1656_;
v_currNamespace_1682_ = v___x_1636_;
v_openDecls_1683_ = v___x_1657_;
v_initHeartbeats_1684_ = v___x_1637_;
v_maxHeartbeats_1685_ = v___x_1658_;
v_quotContext_1686_ = v___x_1636_;
v_currMacroScope_1687_ = v___x_1659_;
v_cancelTk_x3f_1688_ = v___x_1650_;
v_inheritedTraceOptions_1689_ = v___x_1710_;
v_currRecDepth_1690_ = v___x_1637_;
v_ref_1691_ = v___x_1660_;
v_suppressElabErrors_1692_ = v_val_1645_;
v_isRecordingDeps_1693_ = v_val_1645_;
goto v___jp_1679_;
}
}
}
v___jp_1734_:
{
if (v___y_1736_ == 0)
{
v___y_1713_ = v___y_1735_;
goto v___jp_1712_;
}
else
{
lean_inc(v___x_1637_);
lean_inc(v___x_1636_);
lean_inc_ref(v_fileMap_1656_);
lean_inc_ref(v_fileName_1655_);
v_fileName_1680_ = v_fileName_1655_;
v_fileMap_1681_ = v_fileMap_1656_;
v_currNamespace_1682_ = v___x_1636_;
v_openDecls_1683_ = v___x_1657_;
v_initHeartbeats_1684_ = v___x_1637_;
v_maxHeartbeats_1685_ = v___x_1658_;
v_quotContext_1686_ = v___x_1636_;
v_currMacroScope_1687_ = v___x_1659_;
v_cancelTk_x3f_1688_ = v___x_1650_;
v_inheritedTraceOptions_1689_ = v___x_1710_;
v_currRecDepth_1690_ = v___x_1637_;
v_ref_1691_ = v___x_1660_;
v_suppressElabErrors_1692_ = v_val_1645_;
v_isRecordingDeps_1693_ = v_val_1645_;
goto v___jp_1679_;
}
}
v___jp_1739_:
{
if (v___x_1738_ == 0)
{
v___y_1735_ = v___y_1740_;
v___y_1736_ = v___x_1651_;
goto v___jp_1734_;
}
else
{
v___y_1713_ = v___y_1740_;
goto v___jp_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1745_ = _args[0];
lean_object* v_opts_1746_ = _args[1];
lean_object* v___x_1747_ = _args[2];
lean_object* v___x_1748_ = _args[3];
lean_object* v___x_1749_ = _args[4];
lean_object* v___x_1750_ = _args[5];
lean_object* v___x_1751_ = _args[6];
lean_object* v_env_1752_ = _args[7];
lean_object* v___x_1753_ = _args[8];
lean_object* v___x_1754_ = _args[9];
lean_object* v_pos_1755_ = _args[10];
lean_object* v_val_1756_ = _args[11];
lean_object* v___x_1757_ = _args[12];
lean_object* v___x_1758_ = _args[13];
lean_object* v___x_1759_ = _args[14];
lean_object* v___x_1760_ = _args[15];
lean_object* v___x_1761_ = _args[16];
lean_object* v___x_1762_ = _args[17];
lean_object* v_x_1763_ = _args[18];
lean_object* v___y_1764_ = _args[19];
_start:
{
size_t v___x_36964__boxed_1765_; uint8_t v___x_36965__boxed_1766_; uint8_t v_val_36968__boxed_1767_; uint8_t v___x_36974__boxed_1768_; lean_object* v_res_1769_; 
v___x_36964__boxed_1765_ = lean_unbox_usize(v___x_1750_);
lean_dec(v___x_1750_);
v___x_36965__boxed_1766_ = lean_unbox(v___x_1751_);
v_val_36968__boxed_1767_ = lean_unbox(v_val_1756_);
v___x_36974__boxed_1768_ = lean_unbox(v___x_1762_);
v_res_1769_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1745_, v_opts_1746_, v___x_1747_, v___x_1748_, v___x_1749_, v___x_36964__boxed_1765_, v___x_36965__boxed_1766_, v_env_1752_, v___x_1753_, v___x_1754_, v_pos_1755_, v_val_36968__boxed_1767_, v___x_1757_, v___x_1758_, v___x_1759_, v___x_1760_, v___x_1761_, v___x_36974__boxed_1768_, v_x_1763_);
lean_dec(v___x_1760_);
lean_dec(v_pos_1755_);
lean_dec(v___x_1749_);
lean_dec_ref(v_a_1745_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1770_, lean_object* v___x_1771_, lean_object* v_parserState_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v_toProcessingContext_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_toProcessingContext_1774_ = lean_ctor_get(v_a_1770_, 0);
v___x_1775_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1774_);
v___x_1776_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1774_, v___x_1771_, v_parserState_1772_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1777_, lean_object* v___x_1778_, lean_object* v_parserState_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1777_, v___x_1778_, v_parserState_1779_, v_x_1780_);
lean_dec_ref(v_a_1777_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1783_, size_t v_i_1784_, size_t v_stop_1785_, lean_object* v_b_1786_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_usize_dec_eq(v_i_1784_, v_stop_1785_);
if (v___x_1788_ == 0)
{
lean_object* v___f_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; 
v___f_1789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1790_ = lean_array_uget_borrowed(v_as_1783_, v_i_1784_);
lean_inc(v___x_1790_);
v___x_1791_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1789_, v___x_1790_);
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_add(v_i_1784_, v___x_1792_);
v_i_1784_ = v___x_1793_;
v_b_1786_ = v___x_1791_;
goto _start;
}
else
{
return v_b_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1795_, lean_object* v_i_1796_, lean_object* v_stop_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_i_boxed_1800_; size_t v_stop_boxed_1801_; lean_object* v_res_1802_; 
v_i_boxed_1800_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_stop_boxed_1801_ = lean_unbox_usize(v_stop_1797_);
lean_dec(v_stop_1797_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1795_, v_i_boxed_1800_, v_stop_boxed_1801_, v_b_1798_);
lean_dec_ref(v_as_1795_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1803_, lean_object* v_stx_1804_, lean_object* v_revCmds_1805_, lean_object* v_newParserState_1806_, lean_object* v_val_1807_, lean_object* v_sync_1808_, lean_object* v_val_1809_, lean_object* v_a_1810_, lean_object* v_oldNext_1811_, lean_object* v___y_1812_){
_start:
{
uint8_t v_sync_boxed_1813_; lean_object* v_res_1814_; 
v_sync_boxed_1813_ = lean_unbox(v_sync_1808_);
v_res_1814_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1803_, v_stx_1804_, v_revCmds_1805_, v_newParserState_1806_, v_val_1807_, v_sync_boxed_1813_, v_val_1809_, v_a_1810_, v_oldNext_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1815_, lean_object* v_stx_1816_, lean_object* v_revCmds_1817_, lean_object* v_newParserState_1818_, lean_object* v_val_1819_, uint8_t v_sync_1820_, lean_object* v_val_1821_, lean_object* v_a_1822_, lean_object* v_oldResult_1823_){
_start:
{
lean_object* v_task_1825_; lean_object* v___x_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; 
v_task_1825_ = lean_ctor_get(v_val_1815_, 3);
lean_inc_ref(v_task_1825_);
lean_dec_ref(v_val_1815_);
v___x_1826_ = lean_box(v_sync_1820_);
lean_inc_ref(v_a_1822_);
v___f_1827_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1827_, 0, v_oldResult_1823_);
lean_closure_set(v___f_1827_, 1, v_stx_1816_);
lean_closure_set(v___f_1827_, 2, v_revCmds_1817_);
lean_closure_set(v___f_1827_, 3, v_newParserState_1818_);
lean_closure_set(v___f_1827_, 4, v_val_1819_);
lean_closure_set(v___f_1827_, 5, v___x_1826_);
lean_closure_set(v___f_1827_, 6, v_val_1821_);
lean_closure_set(v___f_1827_, 7, v_a_1822_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = 1;
v___x_1830_ = l_BaseIO_chainTask___redArg(v_task_1825_, v___f_1827_, v___x_1828_, v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1831_, lean_object* v_stx_1832_, lean_object* v_revCmds_1833_, lean_object* v_newParserState_1834_, lean_object* v_val_1835_, lean_object* v_sync_1836_, lean_object* v_val_1837_, lean_object* v_a_1838_, lean_object* v_oldResult_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_sync_boxed_1841_; lean_object* v_res_1842_; 
v_sync_boxed_1841_ = lean_unbox(v_sync_1836_);
v_res_1842_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1831_, v_stx_1832_, v_revCmds_1833_, v_newParserState_1834_, v_val_1835_, v_sync_boxed_1841_, v_val_1837_, v_a_1838_, v_oldResult_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1842_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1851_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1852_ = l_Lean_Name_append(v___x_1851_, v___x_1850_);
return v___x_1852_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1856_, lean_object* v_val_1857_, lean_object* v_fst_1858_, lean_object* v_revCmds_1859_, lean_object* v_fst_1860_, uint8_t v_val_1861_, lean_object* v_a_1862_, lean_object* v_snd_1863_, lean_object* v___x_1864_, uint8_t v___x_1865_, lean_object* v_fst_1866_, lean_object* v_val_1867_, lean_object* v_val_1868_, lean_object* v___x_1869_, lean_object* v___f_1870_, lean_object* v___f_1871_, lean_object* v___f_1872_, lean_object* v_pos_1873_, lean_object* v_cmdState_1874_, lean_object* v_val_1875_, lean_object* v___x_1876_, lean_object* v_opts_1877_, lean_object* v___x_1878_, lean_object* v_snd_1879_, lean_object* v_prom_1880_, lean_object* v_old_x3f_1881_, lean_object* v_parseCancelTk_1882_, lean_object* v_next_x3f_1883_){
_start:
{
lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v_snapshotTasks_1891_; lean_object* v_traceTask_1892_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1914_; size_t v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_env_1930_; lean_object* v_messages_1931_; lean_object* v_scopes_1932_; lean_object* v_infoState_1933_; lean_object* v_traceState_1934_; lean_object* v_snapshotTasks_1935_; lean_object* v_codeQualityEntryTasks_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v_reportedCmdState_1943_; lean_object* v___y_1978_; size_t v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v_reportedCmdState_2000_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; size_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2058_; 
if (lean_obj_tag(v_next_x3f_1883_) == 0)
{
lean_object* v___x_2111_; 
lean_dec_ref(v_parseCancelTk_1882_);
v___x_2111_ = lean_box(0);
v___y_2058_ = v___x_2111_;
goto v___jp_2057_;
}
else
{
lean_object* v_toProcessingContext_2112_; lean_object* v_val_2113_; lean_object* v_pos_2114_; lean_object* v_endPos_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_toProcessingContext_2112_ = lean_ctor_get(v_a_1862_, 0);
v_val_2113_ = lean_ctor_get(v_next_x3f_1883_, 0);
v_pos_2114_ = lean_ctor_get(v_fst_1860_, 0);
v_endPos_2115_ = lean_ctor_get(v_toProcessingContext_2112_, 3);
v___x_2116_ = lean_box(0);
lean_inc(v_endPos_2115_);
lean_inc(v_pos_2114_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v_pos_2114_);
lean_ctor_set(v___x_2117_, 1, v_endPos_2115_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_parseCancelTk_1882_);
v___x_2120_ = l_IO_Promise_result_x21___redArg(v_val_2113_);
v___x_2121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2116_);
lean_ctor_set(v___x_2121_, 1, v___x_2118_);
lean_ctor_set(v___x_2121_, 2, v___x_2119_);
lean_ctor_set(v___x_2121_, 3, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___y_2058_ = v___x_2122_;
goto v___jp_2057_;
}
v___jp_1885_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1893_, 0, v___y_1889_);
lean_ctor_set(v___x_1893_, 1, v___x_1856_);
lean_ctor_set(v___x_1893_, 2, v___y_1887_);
lean_ctor_set(v___x_1893_, 3, v_traceTask_1892_);
v___x_1894_ = lean_array_push(v_snapshotTasks_1891_, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___y_1886_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_io_promise_resolve(v___x_1895_, v_val_1857_);
if (lean_obj_tag(v_next_x3f_1883_) == 1)
{
lean_object* v_val_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_val_1897_ = lean_ctor_get(v_next_x3f_1883_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v_next_x3f_1883_, 1);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_fst_1858_);
lean_ctor_set(v___x_1899_, 1, v_revCmds_1859_);
v___x_1900_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1898_, v_fst_1860_, v___y_1890_, v_val_1897_, v_val_1861_, v___y_1888_, v___x_1899_, v_a_1862_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; 
lean_dec_ref(v___y_1890_);
lean_dec_ref(v___y_1888_);
lean_dec(v_next_x3f_1883_);
lean_dec_ref(v_fst_1860_);
lean_dec(v_revCmds_1859_);
lean_dec(v_fst_1858_);
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
}
v___jp_1902_:
{
lean_object* v_snapshotTasks_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_snapshotTasks_1909_ = lean_ctor_get(v___y_1908_, 10);
lean_inc_ref(v_snapshotTasks_1909_);
v___x_1910_ = lean_mk_empty_array_with_capacity(v___y_1903_);
lean_dec(v___y_1903_);
lean_inc_ref(v___y_1904_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___y_1904_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_task_pure(v___x_1911_);
v___y_1886_ = v___y_1904_;
v___y_1887_ = v___y_1905_;
v___y_1888_ = v___y_1907_;
v___y_1889_ = v___y_1906_;
v___y_1890_ = v___y_1908_;
v_snapshotTasks_1891_ = v_snapshotTasks_1909_;
v_traceTask_1892_ = v___x_1912_;
goto v___jp_1885_;
}
v___jp_1913_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_opts_1953_; uint8_t v_hasTrace_1954_; 
v___x_1944_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1931_);
v___x_1945_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1945_, 0, v___y_1928_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
lean_ctor_set(v___x_1945_, 2, v___y_1940_);
lean_ctor_set(v___x_1945_, 3, v_traceState_1934_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*4, v_val_1861_);
v___x_1946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v_reportedCmdState_1943_);
lean_ctor_set(v___x_1946_, 2, v_codeQualityEntryTasks_1936_);
v___x_1947_ = lean_io_promise_resolve(v___x_1946_, v_val_1868_);
v___x_1948_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1933_);
lean_inc(v___y_1937_);
v___x_1949_ = l_BaseIO_chainTask___redArg(v___x_1948_, v___y_1925_, v___y_1937_, v___x_1865_);
v___x_1950_ = l_Lean_inheritedTraceOptions;
v___x_1951_ = lean_st_ref_get(v___x_1950_);
v___x_1952_ = l_List_head_x21___redArg(v___x_1869_, v_scopes_1932_);
lean_dec(v_scopes_1932_);
lean_dec_ref(v___x_1869_);
v_opts_1953_ = lean_ctor_get(v___x_1952_, 1);
lean_inc_ref(v_opts_1953_);
lean_dec(v___x_1952_);
v_hasTrace_1954_ = lean_ctor_get_uint8(v_opts_1953_, sizeof(void*)*1);
if (v_hasTrace_1954_ == 0)
{
lean_dec_ref(v_opts_1953_);
lean_dec(v___x_1951_);
lean_dec_ref(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec_ref(v___y_1938_);
lean_dec_ref(v_snapshotTasks_1935_);
lean_dec_ref(v_env_1930_);
lean_dec(v___y_1924_);
lean_dec(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec(v___y_1914_);
lean_dec(v_pos_1873_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___f_1871_);
lean_dec_ref(v___f_1870_);
lean_dec(v___x_1864_);
v___y_1903_ = v___y_1937_;
v___y_1904_ = v___y_1923_;
v___y_1905_ = v___y_1939_;
v___y_1906_ = v___y_1926_;
v___y_1907_ = v___y_1927_;
v___y_1908_ = v___y_1929_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1955_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1951_, v_opts_1953_, v___x_1955_);
lean_dec(v___x_1951_);
if (v___x_1956_ == 0)
{
lean_dec_ref(v_opts_1953_);
lean_dec_ref(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec_ref(v___y_1938_);
lean_dec_ref(v_snapshotTasks_1935_);
lean_dec_ref(v_env_1930_);
lean_dec(v___y_1924_);
lean_dec(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec(v___y_1914_);
lean_dec(v_pos_1873_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___f_1871_);
lean_dec_ref(v___f_1870_);
lean_dec(v___x_1864_);
v___y_1903_ = v___y_1937_;
v___y_1904_ = v___y_1923_;
v___y_1905_ = v___y_1939_;
v___y_1906_ = v___y_1926_;
v___y_1907_ = v___y_1927_;
v___y_1908_ = v___y_1929_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_inc_n(v___y_1937_, 3);
v___x_1957_ = lean_task_map(v___f_1870_, v___y_1942_, v___y_1937_, v___x_1865_);
lean_inc_n(v___y_1939_, 3);
lean_inc_n(v___y_1924_, 2);
lean_inc_n(v___y_1922_, 2);
v___x_1958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1958_, 0, v___y_1922_);
lean_ctor_set(v___x_1958_, 1, v___y_1924_);
lean_ctor_set(v___x_1958_, 2, v___y_1939_);
lean_ctor_set(v___x_1958_, 3, v___x_1957_);
v___x_1959_ = lean_task_map(v___f_1871_, v___y_1941_, v___y_1937_, v___x_1865_);
v___x_1960_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1922_);
lean_ctor_set(v___x_1960_, 1, v___y_1924_);
lean_ctor_set(v___x_1960_, 2, v___y_1939_);
lean_ctor_set(v___x_1960_, 3, v___x_1959_);
v___x_1961_ = lean_task_map(v___f_1872_, v___y_1938_, v___y_1937_, v___x_1865_);
v___x_1962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1962_, 0, v___y_1922_);
lean_ctor_set(v___x_1962_, 1, v___y_1924_);
lean_ctor_set(v___x_1962_, 2, v___y_1939_);
lean_ctor_set(v___x_1962_, 3, v___x_1961_);
v___x_1963_ = lean_unsigned_to_nat(3u);
v___x_1964_ = lean_mk_empty_array_with_capacity(v___x_1963_);
v___x_1965_ = lean_array_push(v___x_1964_, v___x_1958_);
v___x_1966_ = lean_array_push(v___x_1965_, v___x_1960_);
v___x_1967_ = lean_array_push(v___x_1966_, v___x_1962_);
v___x_1968_ = l_Array_append___redArg(v___x_1967_, v_snapshotTasks_1935_);
lean_inc_ref(v___y_1923_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1923_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_box_usize(v___y_1915_);
v___x_1971_ = lean_box(v___x_1865_);
v___x_1972_ = lean_box(v_val_1861_);
v___x_1973_ = lean_box(v___x_1956_);
lean_inc_ref(v___x_1969_);
lean_inc_ref(v___y_1918_);
lean_inc_ref(v_a_1862_);
v___f_1974_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1974_, 0, v_a_1862_);
lean_closure_set(v___f_1974_, 1, v_opts_1953_);
lean_closure_set(v___f_1974_, 2, v___x_1864_);
lean_closure_set(v___f_1974_, 3, v___y_1914_);
lean_closure_set(v___f_1974_, 4, v___y_1920_);
lean_closure_set(v___f_1974_, 5, v___x_1970_);
lean_closure_set(v___f_1974_, 6, v___x_1971_);
lean_closure_set(v___f_1974_, 7, v_env_1930_);
lean_closure_set(v___f_1974_, 8, v___y_1918_);
lean_closure_set(v___f_1974_, 9, v___x_1969_);
lean_closure_set(v___f_1974_, 10, v_pos_1873_);
lean_closure_set(v___f_1974_, 11, v___x_1972_);
lean_closure_set(v___f_1974_, 12, v___y_1919_);
lean_closure_set(v___f_1974_, 13, v___y_1916_);
lean_closure_set(v___f_1974_, 14, v___y_1917_);
lean_closure_set(v___f_1974_, 15, v___x_1950_);
lean_closure_set(v___f_1974_, 16, v___y_1921_);
lean_closure_set(v___f_1974_, 17, v___x_1973_);
v___x_1975_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1969_);
v___x_1976_ = lean_io_bind_task(v___x_1975_, v___f_1974_, v___y_1937_, v_val_1861_);
v___y_1886_ = v___y_1923_;
v___y_1887_ = v___y_1939_;
v___y_1888_ = v___y_1927_;
v___y_1889_ = v___y_1926_;
v___y_1890_ = v___y_1929_;
v_snapshotTasks_1891_ = v_snapshotTasks_1935_;
v_traceTask_1892_ = v___x_1976_;
goto v___jp_1885_;
}
}
}
v___jp_1977_:
{
lean_object* v_env_2001_; lean_object* v_messages_2002_; lean_object* v_scopes_2003_; lean_object* v_infoState_2004_; lean_object* v_traceState_2005_; lean_object* v_snapshotTasks_2006_; lean_object* v_codeQualityEntryTasks_2007_; 
v_env_2001_ = lean_ctor_get(v___y_1993_, 0);
lean_inc_ref(v_env_2001_);
v_messages_2002_ = lean_ctor_get(v___y_1993_, 1);
lean_inc_ref(v_messages_2002_);
v_scopes_2003_ = lean_ctor_get(v___y_1993_, 2);
lean_inc(v_scopes_2003_);
v_infoState_2004_ = lean_ctor_get(v___y_1993_, 8);
lean_inc_ref(v_infoState_2004_);
v_traceState_2005_ = lean_ctor_get(v___y_1993_, 9);
lean_inc_ref(v_traceState_2005_);
v_snapshotTasks_2006_ = lean_ctor_get(v___y_1993_, 10);
lean_inc_ref(v_snapshotTasks_2006_);
v_codeQualityEntryTasks_2007_ = lean_ctor_get(v___y_1993_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2007_);
v___y_1914_ = v___y_1978_;
v___y_1915_ = v___y_1979_;
v___y_1916_ = v___y_1980_;
v___y_1917_ = v___y_1982_;
v___y_1918_ = v___y_1981_;
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
v_env_1930_ = v_env_2001_;
v_messages_1931_ = v_messages_2002_;
v_scopes_1932_ = v_scopes_2003_;
v_infoState_1933_ = v_infoState_2004_;
v_traceState_1934_ = v_traceState_2005_;
v_snapshotTasks_1935_ = v_snapshotTasks_2006_;
v_codeQualityEntryTasks_1936_ = v_codeQualityEntryTasks_2007_;
v___y_1937_ = v___y_1994_;
v___y_1938_ = v___y_1995_;
v___y_1939_ = v___y_1996_;
v___y_1940_ = v___y_1997_;
v___y_1941_ = v___y_1998_;
v___y_1942_ = v___y_1999_;
v_reportedCmdState_1943_ = v_reportedCmdState_2000_;
goto v___jp_1913_;
}
v___jp_2008_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___f_2029_; uint8_t v___x_2030_; 
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___y_2024_);
lean_ctor_set(v___x_2025_, 1, v_val_1867_);
lean_inc_ref(v___y_2013_);
lean_inc_n(v_pos_1873_, 2);
lean_inc(v_revCmds_1859_);
lean_inc(v_fst_1858_);
v___x_2026_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1858_, v_revCmds_1859_, v_cmdState_1874_, v_pos_1873_, v___x_2025_, v___y_2013_, v_a_1862_);
v___x_2027_ = lean_box(v_val_1861_);
v___x_2028_ = lean_box(v___x_1865_);
lean_inc_ref(v_a_1862_);
lean_inc(v___y_2010_);
lean_inc_ref(v___x_1869_);
lean_inc_ref(v___x_2026_);
lean_inc_ref(v___y_2016_);
lean_inc_ref(v___y_2018_);
v___f_2029_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2029_, 0, v___y_2018_);
lean_closure_set(v___f_2029_, 1, v___y_2016_);
lean_closure_set(v___f_2029_, 2, v___x_2027_);
lean_closure_set(v___f_2029_, 3, v_val_1875_);
lean_closure_set(v___f_2029_, 4, v___x_2026_);
lean_closure_set(v___f_2029_, 5, v___x_1869_);
lean_closure_set(v___f_2029_, 6, v___y_2010_);
lean_closure_set(v___f_2029_, 7, v___x_2028_);
lean_closure_set(v___f_2029_, 8, v_a_1862_);
lean_closure_set(v___f_2029_, 9, v_pos_1873_);
lean_closure_set(v___f_2029_, 10, v___x_1876_);
v___x_2030_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1877_, v___x_1878_);
if (v___x_2030_ == 0)
{
lean_inc_ref(v___x_2026_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2018_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc(v___y_2010_);
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2016_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2017_;
v___y_1984_ = v___y_2018_;
v___y_1985_ = v___y_2020_;
v___y_1986_ = v___y_2011_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2009_;
v___y_1989_ = v___f_2029_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___y_2013_;
v___y_1992_ = v___y_2018_;
v___y_1993_ = v___x_2026_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2022_;
v___y_1996_ = v___y_2020_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2023_;
v___y_1999_ = v___y_2019_;
v_reportedCmdState_2000_ = v___x_2026_;
goto v___jp_1977_;
}
else
{
uint8_t v___x_2031_; 
lean_inc(v_fst_1858_);
v___x_2031_ = l_Lean_Parser_isTerminalCommand(v_fst_1858_);
if (v___x_2031_ == 0)
{
if (v___x_2030_ == 0)
{
lean_inc_ref(v___x_2026_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2018_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc(v___y_2010_);
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2016_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2017_;
v___y_1984_ = v___y_2018_;
v___y_1985_ = v___y_2020_;
v___y_1986_ = v___y_2011_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2009_;
v___y_1989_ = v___f_2029_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___y_2013_;
v___y_1992_ = v___y_2018_;
v___y_1993_ = v___x_2026_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2022_;
v___y_1996_ = v___y_2020_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2023_;
v___y_1999_ = v___y_2019_;
v_reportedCmdState_2000_ = v___x_2026_;
goto v___jp_1977_;
}
else
{
lean_object* v_env_2032_; lean_object* v_messages_2033_; lean_object* v_scopes_2034_; lean_object* v_infoState_2035_; lean_object* v_traceState_2036_; lean_object* v_snapshotTasks_2037_; lean_object* v_codeQualityEntryTasks_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_env_2032_ = lean_ctor_get(v___x_2026_, 0);
lean_inc_ref_n(v_env_2032_, 2);
v_messages_2033_ = lean_ctor_get(v___x_2026_, 1);
lean_inc_ref(v_messages_2033_);
v_scopes_2034_ = lean_ctor_get(v___x_2026_, 2);
lean_inc(v_scopes_2034_);
v_infoState_2035_ = lean_ctor_get(v___x_2026_, 8);
lean_inc_ref(v_infoState_2035_);
v_traceState_2036_ = lean_ctor_get(v___x_2026_, 9);
lean_inc_ref(v_traceState_2036_);
v_snapshotTasks_2037_ = lean_ctor_get(v___x_2026_, 10);
lean_inc_ref(v_snapshotTasks_2037_);
v_codeQualityEntryTasks_2038_ = lean_ctor_get(v___x_2026_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2038_);
v___x_2039_ = lean_mk_empty_array_with_capacity(v___y_2017_);
lean_inc_ref(v___x_2039_);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_inc_n(v___y_2010_, 4);
v___x_2041_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
lean_ctor_set(v___x_2041_, 2, v___y_2010_);
lean_ctor_set(v___x_2041_, 3, v___y_2010_);
lean_ctor_set_usize(v___x_2041_, 4, v___y_2012_);
v___x_2042_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2041_, 2);
v___x_2043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2041_);
lean_ctor_set(v___x_2043_, 2, v___x_2042_);
v___x_2044_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2045_ = l_Lean_Options_empty;
v___x_2046_ = lean_box(0);
v___x_2047_ = lean_mk_empty_array_with_capacity(v___y_2010_);
lean_inc_ref_n(v___x_2047_, 3);
lean_inc_n(v___x_1864_, 2);
v___x_2048_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2048_, 0, v___x_2044_);
lean_ctor_set(v___x_2048_, 1, v___x_2045_);
lean_ctor_set(v___x_2048_, 2, v___x_1864_);
lean_ctor_set(v___x_2048_, 3, v___x_2046_);
lean_ctor_set(v___x_2048_, 4, v___x_2046_);
lean_ctor_set(v___x_2048_, 5, v___x_2047_);
lean_ctor_set(v___x_2048_, 6, v___x_2047_);
lean_ctor_set(v___x_2048_, 7, v___x_2046_);
lean_ctor_set(v___x_2048_, 8, v___x_2046_);
lean_ctor_set(v___x_2048_, 9, v___x_2046_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*10, v_val_1861_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*10 + 1, v_val_1861_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*10 + 2, v_val_1861_);
v___x_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2046_);
v___x_2050_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2051_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2052_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1864_);
v___x_2053_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2054_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_ctor_set(v___x_2054_, 2, v___x_2041_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*3, v___x_1865_);
v___x_2055_ = lean_box(0);
lean_inc_ref(v___y_2016_);
v___x_2056_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2056_, 0, v_env_2032_);
lean_ctor_set(v___x_2056_, 1, v___x_2043_);
lean_ctor_set(v___x_2056_, 2, v___x_2049_);
lean_ctor_set(v___x_2056_, 3, v___x_2042_);
lean_ctor_set(v___x_2056_, 4, v___x_2050_);
lean_ctor_set(v___x_2056_, 5, v___y_2010_);
lean_ctor_set(v___x_2056_, 6, v___x_2051_);
lean_ctor_set(v___x_2056_, 7, v___x_2052_);
lean_ctor_set(v___x_2056_, 8, v___x_2054_);
lean_ctor_set(v___x_2056_, 9, v___y_2016_);
lean_ctor_set(v___x_2056_, 10, v___x_2047_);
lean_ctor_set(v___x_2056_, 11, v___x_2055_);
lean_ctor_set(v___x_2056_, 12, v___x_2047_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2018_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
v___y_1914_ = v___y_2010_;
v___y_1915_ = v___y_2012_;
v___y_1916_ = v___y_2014_;
v___y_1917_ = v___y_2015_;
v___y_1918_ = v___y_2016_;
v___y_1919_ = v___y_2018_;
v___y_1920_ = v___y_2017_;
v___y_1921_ = v___y_2020_;
v___y_1922_ = v___y_2011_;
v___y_1923_ = v___y_2015_;
v___y_1924_ = v___y_2009_;
v___y_1925_ = v___f_2029_;
v___y_1926_ = v___y_2021_;
v___y_1927_ = v___y_2013_;
v___y_1928_ = v___y_2018_;
v___y_1929_ = v___x_2026_;
v_env_1930_ = v_env_2032_;
v_messages_1931_ = v_messages_2033_;
v_scopes_1932_ = v_scopes_2034_;
v_infoState_1933_ = v_infoState_2035_;
v_traceState_1934_ = v_traceState_2036_;
v_snapshotTasks_1935_ = v_snapshotTasks_2037_;
v_codeQualityEntryTasks_1936_ = v_codeQualityEntryTasks_2038_;
v___y_1937_ = v___y_2010_;
v___y_1938_ = v___y_2022_;
v___y_1939_ = v___y_2020_;
v___y_1940_ = v___y_2014_;
v___y_1941_ = v___y_2023_;
v___y_1942_ = v___y_2019_;
v_reportedCmdState_1943_ = v___x_2056_;
goto v___jp_1913_;
}
}
else
{
lean_inc_ref(v___x_2026_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2018_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc(v___y_2010_);
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2012_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2016_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2017_;
v___y_1984_ = v___y_2018_;
v___y_1985_ = v___y_2020_;
v___y_1986_ = v___y_2011_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2009_;
v___y_1989_ = v___f_2029_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___y_2013_;
v___y_1992_ = v___y_2018_;
v___y_1993_ = v___x_2026_;
v___y_1994_ = v___y_2010_;
v___y_1995_ = v___y_2022_;
v___y_1996_ = v___y_2020_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2023_;
v___y_1999_ = v___y_2019_;
v_reportedCmdState_2000_ = v___x_2026_;
goto v___jp_1977_;
}
}
}
v___jp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2059_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1863_);
v___x_2060_ = l_IO_CancelToken_new();
v___x_2061_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1864_);
v___x_2062_ = l_Lean_Name_str___override(v___x_1864_, v___x_2061_);
v___x_2063_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2064_ = l_Lean_Name_str___override(v___x_2062_, v___x_2063_);
v___x_2065_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2066_ = l_Lean_Name_str___override(v___x_2064_, v___x_2065_);
v___x_2067_ = l_Lean_Name_str___override(v___x_2066_, v___x_2063_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = l_Lean_Name_num___override(v___x_2067_, v___x_2068_);
v___x_2070_ = l_Lean_Name_str___override(v___x_2069_, v___x_2063_);
v___x_2071_ = l_Lean_Name_str___override(v___x_2070_, v___x_2065_);
v___x_2072_ = l_Lean_Name_str___override(v___x_2071_, v___x_2063_);
v___x_2073_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2074_ = l_Lean_Name_str___override(v___x_2072_, v___x_2073_);
v___x_2075_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2076_ = l_Lean_Name_str___override(v___x_2074_, v___x_2075_);
v___x_2077_ = l_Lean_Name_toString(v___x_2076_, v___x_1865_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_unsigned_to_nat(32u);
v___x_2080_ = ((size_t)5ULL);
v___x_2081_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2077_, 2);
v___x_2082_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2082_, 0, v___x_2077_);
lean_ctor_set(v___x_2082_, 1, v___x_2059_);
lean_ctor_set(v___x_2082_, 2, v___x_2078_);
lean_ctor_set(v___x_2082_, 3, v___x_2081_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*4, v_val_1861_);
v___x_2083_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2084_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2084_, 0, v___x_2077_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
lean_ctor_set(v___x_2084_, 2, v___x_2078_);
lean_ctor_set(v___x_2084_, 3, v___x_2081_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*4, v_val_1861_);
lean_inc(v_fst_1866_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_fst_1866_);
v___x_2086_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2085_);
lean_inc_ref(v___x_2060_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2060_);
v___x_2088_ = l_IO_Promise_result_x21___redArg(v_val_1867_);
lean_inc_ref(v___x_2088_);
lean_inc(v___x_2086_);
lean_inc_ref_n(v___x_2085_, 3);
v___x_2089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2085_);
lean_ctor_set(v___x_2089_, 1, v___x_2086_);
lean_ctor_set(v___x_2089_, 2, v___x_2087_);
lean_ctor_set(v___x_2089_, 3, v___x_2088_);
v___x_2090_ = l_IO_Promise_result_x21___redArg(v_val_1868_);
lean_inc_ref(v___x_2090_);
lean_inc_n(v___x_1856_, 3);
v___x_2091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2085_);
lean_ctor_set(v___x_2091_, 1, v___x_1856_);
lean_ctor_set(v___x_2091_, 2, v___x_2078_);
lean_ctor_set(v___x_2091_, 3, v___x_2090_);
v___x_2092_ = l_IO_Promise_result_x21___redArg(v_val_1875_);
lean_inc_ref(v___x_2092_);
v___x_2093_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2085_);
lean_ctor_set(v___x_2093_, 1, v___x_1856_);
lean_ctor_set(v___x_2093_, 2, v___x_2078_);
lean_ctor_set(v___x_2093_, 3, v___x_2092_);
v___x_2094_ = l_IO_Promise_result_x21___redArg(v_val_1857_);
v___x_2095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2078_);
lean_ctor_set(v___x_2095_, 1, v___x_1856_);
lean_ctor_set(v___x_2095_, 2, v___x_2078_);
lean_ctor_set(v___x_2095_, 3, v___x_2094_);
lean_inc_ref(v___x_2084_);
v___x_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2084_);
lean_ctor_set(v___x_2096_, 1, v___x_2089_);
lean_ctor_set(v___x_2096_, 2, v___x_2091_);
lean_ctor_set(v___x_2096_, 3, v___x_2093_);
lean_ctor_set(v___x_2096_, 4, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2082_);
lean_ctor_set(v___x_2097_, 1, v_fst_1866_);
lean_ctor_set(v___x_2097_, 2, v_snd_1879_);
lean_ctor_set(v___x_2097_, 3, v___x_2096_);
lean_ctor_set(v___x_2097_, 4, v___y_2058_);
v___x_2098_ = lean_io_promise_resolve(v___x_2097_, v_prom_1880_);
if (lean_obj_tag(v_old_x3f_1881_) == 0)
{
v___y_2009_ = v___x_2086_;
v___y_2010_ = v___x_2068_;
v___y_2011_ = v___x_2085_;
v___y_2012_ = v___x_2080_;
v___y_2013_ = v___x_2060_;
v___y_2014_ = v___x_2078_;
v___y_2015_ = v___x_2084_;
v___y_2016_ = v___x_2081_;
v___y_2017_ = v___x_2079_;
v___y_2018_ = v___x_2077_;
v___y_2019_ = v___x_2088_;
v___y_2020_ = v___x_2078_;
v___y_2021_ = v___x_2078_;
v___y_2022_ = v___x_2092_;
v___y_2023_ = v___x_2090_;
v___y_2024_ = v___x_2078_;
goto v___jp_2008_;
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2110_; 
v_val_2099_ = lean_ctor_get(v_old_x3f_1881_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_old_x3f_1881_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2101_ = v_old_x3f_1881_;
v_isShared_2102_ = v_isSharedCheck_2110_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_val_2099_);
lean_dec(v_old_x3f_1881_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2110_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_elabSnap_2103_; lean_object* v_stx_2104_; lean_object* v_elabSnap_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v_elabSnap_2103_ = lean_ctor_get(v_val_2099_, 3);
lean_inc_ref(v_elabSnap_2103_);
v_stx_2104_ = lean_ctor_get(v_val_2099_, 1);
lean_inc(v_stx_2104_);
lean_dec(v_val_2099_);
v_elabSnap_2105_ = lean_ctor_get(v_elabSnap_2103_, 1);
lean_inc_ref(v_elabSnap_2105_);
lean_dec_ref(v_elabSnap_2103_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_stx_2104_);
lean_ctor_set(v___x_2106_, 1, v_elabSnap_2105_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2106_);
v___x_2108_ = v___x_2101_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
v___y_2009_ = v___x_2086_;
v___y_2010_ = v___x_2068_;
v___y_2011_ = v___x_2085_;
v___y_2012_ = v___x_2080_;
v___y_2013_ = v___x_2060_;
v___y_2014_ = v___x_2078_;
v___y_2015_ = v___x_2084_;
v___y_2016_ = v___x_2081_;
v___y_2017_ = v___x_2079_;
v___y_2018_ = v___x_2077_;
v___y_2019_ = v___x_2088_;
v___y_2020_ = v___x_2078_;
v___y_2021_ = v___x_2078_;
v___y_2022_ = v___x_2092_;
v___y_2023_ = v___x_2090_;
v___y_2024_ = v___x_2108_;
goto v___jp_2008_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2124_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2123_);
return v___x_2124_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2128_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2129_, lean_object* v_revCmds_2130_, lean_object* v_fst_2131_, uint8_t v_val_2132_, lean_object* v_a_2133_, lean_object* v_snd_2134_, lean_object* v___x_2135_, uint8_t v___x_2136_, lean_object* v___x_2137_, lean_object* v___f_2138_, lean_object* v___f_2139_, lean_object* v___f_2140_, lean_object* v_pos_2141_, lean_object* v_cmdState_2142_, lean_object* v___x_2143_, lean_object* v_opts_2144_, lean_object* v_prom_2145_, lean_object* v_old_x3f_2146_, lean_object* v_parseCancelTk_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v_snapshotTasks_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v_traceTask_2162_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; size_t v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v_env_2207_; lean_object* v_messages_2208_; lean_object* v_scopes_2209_; lean_object* v_infoState_2210_; lean_object* v_traceState_2211_; lean_object* v_snapshotTasks_2212_; lean_object* v_codeQualityEntryTasks_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v_reportedCmdState_2217_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; size_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v_reportedCmdState_2276_; lean_object* v___x_2284_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; size_t v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v_fst_2415_; lean_object* v_snd_2416_; uint8_t v___x_2428_; 
v___x_2149_ = lean_io_promise_new();
v___x_2150_ = lean_io_promise_new();
v___x_2151_ = lean_io_promise_new();
v___x_2152_ = lean_io_promise_new();
v___x_2284_ = l_Lean_internal_cmdlineSnapshots;
v___x_2428_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2144_, v___x_2284_);
if (v___x_2428_ == 0)
{
lean_inc_ref(v_fst_2131_);
lean_inc(v_fst_2129_);
v_fst_2415_ = v_fst_2129_;
v_snd_2416_ = v_fst_2131_;
goto v___jp_2414_;
}
else
{
uint8_t v___x_2429_; 
lean_inc(v_fst_2129_);
v___x_2429_ = l_Lean_Parser_isTerminalCommand(v_fst_2129_);
if (v___x_2429_ == 0)
{
if (v___x_2428_ == 0)
{
lean_inc_ref(v_fst_2131_);
lean_inc(v_fst_2129_);
v_fst_2415_ = v_fst_2129_;
v_snd_2416_ = v_fst_2131_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_box(0);
v___x_2431_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2415_ = v___x_2430_;
v_snd_2416_ = v___x_2431_;
goto v___jp_2414_;
}
}
else
{
lean_inc_ref(v_fst_2131_);
lean_inc(v_fst_2129_);
v_fst_2415_ = v_fst_2129_;
v_snd_2416_ = v_fst_2131_;
goto v___jp_2414_;
}
}
v___jp_2153_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2163_, 0, v___y_2157_);
lean_ctor_set(v___x_2163_, 1, v___y_2160_);
lean_ctor_set(v___x_2163_, 2, v___y_2158_);
lean_ctor_set(v___x_2163_, 3, v_traceTask_2162_);
v___x_2164_ = lean_array_push(v_snapshotTasks_2156_, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___y_2161_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_io_promise_resolve(v___x_2165_, v___x_2152_);
lean_dec(v___x_2152_);
if (lean_obj_tag(v___y_2154_) == 1)
{
lean_object* v_val_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_val_2167_ = lean_ctor_get(v___y_2154_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v___y_2154_, 1);
v___x_2168_ = lean_box(0);
v___x_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2169_, 0, v_fst_2129_);
lean_ctor_set(v___x_2169_, 1, v_revCmds_2130_);
v___x_2170_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2168_, v_fst_2131_, v___y_2155_, v_val_2167_, v_val_2132_, v___y_2159_, v___x_2169_, v_a_2133_);
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; 
lean_dec_ref(v___y_2159_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v_fst_2131_);
lean_dec(v_revCmds_2130_);
lean_dec(v_fst_2129_);
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
}
v___jp_2172_:
{
lean_object* v_snapshotTasks_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_snapshotTasks_2181_ = lean_ctor_get(v___y_2175_, 10);
lean_inc_ref(v_snapshotTasks_2181_);
v___x_2182_ = lean_mk_empty_array_with_capacity(v___y_2173_);
lean_dec(v___y_2173_);
lean_inc_ref(v___y_2180_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___y_2180_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_task_pure(v___x_2183_);
v___y_2154_ = v___y_2174_;
v___y_2155_ = v___y_2175_;
v_snapshotTasks_2156_ = v_snapshotTasks_2181_;
v___y_2157_ = v___y_2176_;
v___y_2158_ = v___y_2177_;
v___y_2159_ = v___y_2178_;
v___y_2160_ = v___y_2179_;
v___y_2161_ = v___y_2180_;
v_traceTask_2162_ = v___x_2184_;
goto v___jp_2153_;
}
v___jp_2185_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_opts_2227_; uint8_t v_hasTrace_2228_; 
v___x_2218_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2208_);
v___x_2219_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2219_, 0, v___y_2194_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
lean_ctor_set(v___x_2219_, 2, v___y_2198_);
lean_ctor_set(v___x_2219_, 3, v_traceState_2211_);
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*4, v_val_2132_);
v___x_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v_reportedCmdState_2217_);
lean_ctor_set(v___x_2220_, 2, v_codeQualityEntryTasks_2213_);
v___x_2221_ = lean_io_promise_resolve(v___x_2220_, v___x_2150_);
lean_dec(v___x_2150_);
v___x_2222_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2210_);
lean_inc(v___y_2195_);
v___x_2223_ = l_BaseIO_chainTask___redArg(v___x_2222_, v___y_2199_, v___y_2195_, v___x_2136_);
v___x_2224_ = l_Lean_inheritedTraceOptions;
v___x_2225_ = lean_st_ref_get(v___x_2224_);
v___x_2226_ = l_List_head_x21___redArg(v___x_2137_, v_scopes_2209_);
lean_dec(v_scopes_2209_);
lean_dec_ref(v___x_2137_);
v_opts_2227_ = lean_ctor_get(v___x_2226_, 1);
lean_inc_ref(v_opts_2227_);
lean_dec(v___x_2226_);
v_hasTrace_2228_ = lean_ctor_get_uint8(v_opts_2227_, sizeof(void*)*1);
if (v_hasTrace_2228_ == 0)
{
lean_dec_ref(v_opts_2227_);
lean_dec(v___x_2225_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_snapshotTasks_2212_);
lean_dec_ref(v_env_2207_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2196_);
lean_dec(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v_pos_2141_);
lean_dec_ref(v___f_2140_);
lean_dec_ref(v___f_2139_);
lean_dec_ref(v___f_2138_);
lean_dec(v___x_2135_);
v___y_2173_ = v___y_2195_;
v___y_2174_ = v___y_2205_;
v___y_2175_ = v___y_2206_;
v___y_2176_ = v___y_2197_;
v___y_2177_ = v___y_2200_;
v___y_2178_ = v___y_2215_;
v___y_2179_ = v___y_2202_;
v___y_2180_ = v___y_2203_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2230_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2225_, v_opts_2227_, v___x_2229_);
lean_dec(v___x_2225_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v_opts_2227_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v___y_2214_);
lean_dec_ref(v_snapshotTasks_2212_);
lean_dec_ref(v_env_2207_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2196_);
lean_dec(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v_pos_2141_);
lean_dec_ref(v___f_2140_);
lean_dec_ref(v___f_2139_);
lean_dec_ref(v___f_2138_);
lean_dec(v___x_2135_);
v___y_2173_ = v___y_2195_;
v___y_2174_ = v___y_2205_;
v___y_2175_ = v___y_2206_;
v___y_2176_ = v___y_2197_;
v___y_2177_ = v___y_2200_;
v___y_2178_ = v___y_2215_;
v___y_2179_ = v___y_2202_;
v___y_2180_ = v___y_2203_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_inc_n(v___y_2195_, 3);
v___x_2231_ = lean_task_map(v___f_2138_, v___y_2201_, v___y_2195_, v___x_2136_);
lean_inc_n(v___y_2200_, 3);
lean_inc_n(v___y_2196_, 2);
lean_inc_n(v___y_2204_, 2);
v___x_2232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2232_, 0, v___y_2204_);
lean_ctor_set(v___x_2232_, 1, v___y_2196_);
lean_ctor_set(v___x_2232_, 2, v___y_2200_);
lean_ctor_set(v___x_2232_, 3, v___x_2231_);
v___x_2233_ = lean_task_map(v___f_2139_, v___y_2216_, v___y_2195_, v___x_2136_);
v___x_2234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2234_, 0, v___y_2204_);
lean_ctor_set(v___x_2234_, 1, v___y_2196_);
lean_ctor_set(v___x_2234_, 2, v___y_2200_);
lean_ctor_set(v___x_2234_, 3, v___x_2233_);
v___x_2235_ = lean_task_map(v___f_2140_, v___y_2214_, v___y_2195_, v___x_2136_);
v___x_2236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2236_, 0, v___y_2204_);
lean_ctor_set(v___x_2236_, 1, v___y_2196_);
lean_ctor_set(v___x_2236_, 2, v___y_2200_);
lean_ctor_set(v___x_2236_, 3, v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(3u);
v___x_2238_ = lean_mk_empty_array_with_capacity(v___x_2237_);
v___x_2239_ = lean_array_push(v___x_2238_, v___x_2232_);
v___x_2240_ = lean_array_push(v___x_2239_, v___x_2234_);
v___x_2241_ = lean_array_push(v___x_2240_, v___x_2236_);
v___x_2242_ = l_Array_append___redArg(v___x_2241_, v_snapshotTasks_2212_);
lean_inc_ref(v___y_2203_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___y_2203_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_box_usize(v___y_2192_);
v___x_2245_ = lean_box(v___x_2136_);
v___x_2246_ = lean_box(v_val_2132_);
v___x_2247_ = lean_box(v___x_2230_);
lean_inc_ref(v___x_2243_);
lean_inc_ref(v___y_2193_);
lean_inc_ref(v_a_2133_);
v___f_2248_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2248_, 0, v_a_2133_);
lean_closure_set(v___f_2248_, 1, v_opts_2227_);
lean_closure_set(v___f_2248_, 2, v___x_2135_);
lean_closure_set(v___f_2248_, 3, v___y_2188_);
lean_closure_set(v___f_2248_, 4, v___y_2187_);
lean_closure_set(v___f_2248_, 5, v___x_2244_);
lean_closure_set(v___f_2248_, 6, v___x_2245_);
lean_closure_set(v___f_2248_, 7, v_env_2207_);
lean_closure_set(v___f_2248_, 8, v___y_2193_);
lean_closure_set(v___f_2248_, 9, v___x_2243_);
lean_closure_set(v___f_2248_, 10, v_pos_2141_);
lean_closure_set(v___f_2248_, 11, v___x_2246_);
lean_closure_set(v___f_2248_, 12, v___y_2186_);
lean_closure_set(v___f_2248_, 13, v___y_2190_);
lean_closure_set(v___f_2248_, 14, v___y_2189_);
lean_closure_set(v___f_2248_, 15, v___x_2224_);
lean_closure_set(v___f_2248_, 16, v___y_2191_);
lean_closure_set(v___f_2248_, 17, v___x_2247_);
v___x_2249_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2243_);
v___x_2250_ = lean_io_bind_task(v___x_2249_, v___f_2248_, v___y_2195_, v_val_2132_);
v___y_2154_ = v___y_2205_;
v___y_2155_ = v___y_2206_;
v_snapshotTasks_2156_ = v_snapshotTasks_2212_;
v___y_2157_ = v___y_2197_;
v___y_2158_ = v___y_2200_;
v___y_2159_ = v___y_2215_;
v___y_2160_ = v___y_2202_;
v___y_2161_ = v___y_2203_;
v_traceTask_2162_ = v___x_2250_;
goto v___jp_2153_;
}
}
}
v___jp_2251_:
{
lean_object* v_env_2277_; lean_object* v_messages_2278_; lean_object* v_scopes_2279_; lean_object* v_infoState_2280_; lean_object* v_traceState_2281_; lean_object* v_snapshotTasks_2282_; lean_object* v_codeQualityEntryTasks_2283_; 
v_env_2277_ = lean_ctor_get(v___y_2272_, 0);
lean_inc_ref(v_env_2277_);
v_messages_2278_ = lean_ctor_get(v___y_2272_, 1);
lean_inc_ref(v_messages_2278_);
v_scopes_2279_ = lean_ctor_get(v___y_2272_, 2);
lean_inc(v_scopes_2279_);
v_infoState_2280_ = lean_ctor_get(v___y_2272_, 8);
lean_inc_ref(v_infoState_2280_);
v_traceState_2281_ = lean_ctor_get(v___y_2272_, 9);
lean_inc_ref(v_traceState_2281_);
v_snapshotTasks_2282_ = lean_ctor_get(v___y_2272_, 10);
lean_inc_ref(v_snapshotTasks_2282_);
v_codeQualityEntryTasks_2283_ = lean_ctor_get(v___y_2272_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2283_);
v___y_2186_ = v___y_2252_;
v___y_2187_ = v___y_2253_;
v___y_2188_ = v___y_2254_;
v___y_2189_ = v___y_2255_;
v___y_2190_ = v___y_2256_;
v___y_2191_ = v___y_2257_;
v___y_2192_ = v___y_2258_;
v___y_2193_ = v___y_2259_;
v___y_2194_ = v___y_2260_;
v___y_2195_ = v___y_2261_;
v___y_2196_ = v___y_2262_;
v___y_2197_ = v___y_2263_;
v___y_2198_ = v___y_2264_;
v___y_2199_ = v___y_2265_;
v___y_2200_ = v___y_2266_;
v___y_2201_ = v___y_2267_;
v___y_2202_ = v___y_2268_;
v___y_2203_ = v___y_2269_;
v___y_2204_ = v___y_2270_;
v___y_2205_ = v___y_2271_;
v___y_2206_ = v___y_2272_;
v_env_2207_ = v_env_2277_;
v_messages_2208_ = v_messages_2278_;
v_scopes_2209_ = v_scopes_2279_;
v_infoState_2210_ = v_infoState_2280_;
v_traceState_2211_ = v_traceState_2281_;
v_snapshotTasks_2212_ = v_snapshotTasks_2282_;
v_codeQualityEntryTasks_2213_ = v_codeQualityEntryTasks_2283_;
v___y_2214_ = v___y_2273_;
v___y_2215_ = v___y_2274_;
v___y_2216_ = v___y_2275_;
v_reportedCmdState_2217_ = v_reportedCmdState_2276_;
goto v___jp_2185_;
}
v___jp_2285_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___f_2308_; uint8_t v___x_2309_; 
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___y_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2149_);
lean_inc_ref(v___y_2295_);
lean_inc_n(v_pos_2141_, 2);
lean_inc(v_revCmds_2130_);
lean_inc(v_fst_2129_);
v___x_2305_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2129_, v_revCmds_2130_, v_cmdState_2142_, v_pos_2141_, v___x_2304_, v___y_2295_, v_a_2133_);
v___x_2306_ = lean_box(v_val_2132_);
v___x_2307_ = lean_box(v___x_2136_);
lean_inc_ref(v_a_2133_);
lean_inc(v___y_2289_);
lean_inc_ref(v___x_2137_);
lean_inc_ref(v___x_2305_);
lean_inc_ref(v___y_2297_);
lean_inc_ref(v___y_2286_);
v___f_2308_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2308_, 0, v___y_2286_);
lean_closure_set(v___f_2308_, 1, v___y_2297_);
lean_closure_set(v___f_2308_, 2, v___x_2306_);
lean_closure_set(v___f_2308_, 3, v___x_2151_);
lean_closure_set(v___f_2308_, 4, v___x_2305_);
lean_closure_set(v___f_2308_, 5, v___x_2137_);
lean_closure_set(v___f_2308_, 6, v___y_2289_);
lean_closure_set(v___f_2308_, 7, v___x_2307_);
lean_closure_set(v___f_2308_, 8, v_a_2133_);
lean_closure_set(v___f_2308_, 9, v_pos_2141_);
lean_closure_set(v___f_2308_, 10, v___x_2143_);
v___x_2309_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2144_, v___x_2284_);
if (v___x_2309_ == 0)
{
lean_inc_ref(v___x_2305_);
lean_inc(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2290_);
lean_inc(v___y_2289_);
lean_inc_ref(v___y_2286_);
v___y_2252_ = v___y_2286_;
v___y_2253_ = v___y_2287_;
v___y_2254_ = v___y_2289_;
v___y_2255_ = v___y_2290_;
v___y_2256_ = v___y_2292_;
v___y_2257_ = v___y_2293_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2297_;
v___y_2260_ = v___y_2286_;
v___y_2261_ = v___y_2289_;
v___y_2262_ = v___y_2291_;
v___y_2263_ = v___y_2298_;
v___y_2264_ = v___y_2292_;
v___y_2265_ = v___f_2308_;
v___y_2266_ = v___y_2293_;
v___y_2267_ = v___y_2296_;
v___y_2268_ = v___y_2299_;
v___y_2269_ = v___y_2290_;
v___y_2270_ = v___y_2288_;
v___y_2271_ = v___y_2300_;
v___y_2272_ = v___x_2305_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2295_;
v___y_2275_ = v___y_2302_;
v_reportedCmdState_2276_ = v___x_2305_;
goto v___jp_2251_;
}
else
{
uint8_t v___x_2310_; 
lean_inc(v_fst_2129_);
v___x_2310_ = l_Lean_Parser_isTerminalCommand(v_fst_2129_);
if (v___x_2310_ == 0)
{
if (v___x_2309_ == 0)
{
lean_inc_ref(v___x_2305_);
lean_inc(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2290_);
lean_inc(v___y_2289_);
lean_inc_ref(v___y_2286_);
v___y_2252_ = v___y_2286_;
v___y_2253_ = v___y_2287_;
v___y_2254_ = v___y_2289_;
v___y_2255_ = v___y_2290_;
v___y_2256_ = v___y_2292_;
v___y_2257_ = v___y_2293_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2297_;
v___y_2260_ = v___y_2286_;
v___y_2261_ = v___y_2289_;
v___y_2262_ = v___y_2291_;
v___y_2263_ = v___y_2298_;
v___y_2264_ = v___y_2292_;
v___y_2265_ = v___f_2308_;
v___y_2266_ = v___y_2293_;
v___y_2267_ = v___y_2296_;
v___y_2268_ = v___y_2299_;
v___y_2269_ = v___y_2290_;
v___y_2270_ = v___y_2288_;
v___y_2271_ = v___y_2300_;
v___y_2272_ = v___x_2305_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2295_;
v___y_2275_ = v___y_2302_;
v_reportedCmdState_2276_ = v___x_2305_;
goto v___jp_2251_;
}
else
{
lean_object* v_env_2311_; lean_object* v_messages_2312_; lean_object* v_scopes_2313_; lean_object* v_infoState_2314_; lean_object* v_traceState_2315_; lean_object* v_snapshotTasks_2316_; lean_object* v_codeQualityEntryTasks_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_env_2311_ = lean_ctor_get(v___x_2305_, 0);
lean_inc_ref_n(v_env_2311_, 2);
v_messages_2312_ = lean_ctor_get(v___x_2305_, 1);
lean_inc_ref(v_messages_2312_);
v_scopes_2313_ = lean_ctor_get(v___x_2305_, 2);
lean_inc(v_scopes_2313_);
v_infoState_2314_ = lean_ctor_get(v___x_2305_, 8);
lean_inc_ref(v_infoState_2314_);
v_traceState_2315_ = lean_ctor_get(v___x_2305_, 9);
lean_inc_ref(v_traceState_2315_);
v_snapshotTasks_2316_ = lean_ctor_get(v___x_2305_, 10);
lean_inc_ref(v_snapshotTasks_2316_);
v_codeQualityEntryTasks_2317_ = lean_ctor_get(v___x_2305_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2317_);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___y_2287_);
lean_inc_ref(v___x_2318_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_inc_n(v___y_2289_, 4);
v___x_2320_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v___x_2318_);
lean_ctor_set(v___x_2320_, 2, v___y_2289_);
lean_ctor_set(v___x_2320_, 3, v___y_2289_);
lean_ctor_set_usize(v___x_2320_, 4, v___y_2294_);
v___x_2321_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2320_, 2);
v___x_2322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2320_);
lean_ctor_set(v___x_2322_, 2, v___x_2321_);
v___x_2323_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2324_ = l_Lean_Options_empty;
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_mk_empty_array_with_capacity(v___y_2289_);
lean_inc_ref_n(v___x_2326_, 3);
lean_inc_n(v___x_2135_, 2);
v___x_2327_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2327_, 0, v___x_2323_);
lean_ctor_set(v___x_2327_, 1, v___x_2324_);
lean_ctor_set(v___x_2327_, 2, v___x_2135_);
lean_ctor_set(v___x_2327_, 3, v___x_2325_);
lean_ctor_set(v___x_2327_, 4, v___x_2325_);
lean_ctor_set(v___x_2327_, 5, v___x_2326_);
lean_ctor_set(v___x_2327_, 6, v___x_2326_);
lean_ctor_set(v___x_2327_, 7, v___x_2325_);
lean_ctor_set(v___x_2327_, 8, v___x_2325_);
lean_ctor_set(v___x_2327_, 9, v___x_2325_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*10, v_val_2132_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*10 + 1, v_val_2132_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*10 + 2, v_val_2132_);
v___x_2328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___x_2325_);
v___x_2329_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2330_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2331_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2135_);
v___x_2332_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2333_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
lean_ctor_set(v___x_2333_, 2, v___x_2320_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*3, v___x_2136_);
v___x_2334_ = lean_box(0);
lean_inc_ref(v___y_2297_);
v___x_2335_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2335_, 0, v_env_2311_);
lean_ctor_set(v___x_2335_, 1, v___x_2322_);
lean_ctor_set(v___x_2335_, 2, v___x_2328_);
lean_ctor_set(v___x_2335_, 3, v___x_2321_);
lean_ctor_set(v___x_2335_, 4, v___x_2329_);
lean_ctor_set(v___x_2335_, 5, v___y_2289_);
lean_ctor_set(v___x_2335_, 6, v___x_2330_);
lean_ctor_set(v___x_2335_, 7, v___x_2331_);
lean_ctor_set(v___x_2335_, 8, v___x_2333_);
lean_ctor_set(v___x_2335_, 9, v___y_2297_);
lean_ctor_set(v___x_2335_, 10, v___x_2326_);
lean_ctor_set(v___x_2335_, 11, v___x_2334_);
lean_ctor_set(v___x_2335_, 12, v___x_2326_);
lean_inc(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2290_);
lean_inc_ref(v___y_2286_);
v___y_2186_ = v___y_2286_;
v___y_2187_ = v___y_2287_;
v___y_2188_ = v___y_2289_;
v___y_2189_ = v___y_2290_;
v___y_2190_ = v___y_2292_;
v___y_2191_ = v___y_2293_;
v___y_2192_ = v___y_2294_;
v___y_2193_ = v___y_2297_;
v___y_2194_ = v___y_2286_;
v___y_2195_ = v___y_2289_;
v___y_2196_ = v___y_2291_;
v___y_2197_ = v___y_2298_;
v___y_2198_ = v___y_2292_;
v___y_2199_ = v___f_2308_;
v___y_2200_ = v___y_2293_;
v___y_2201_ = v___y_2296_;
v___y_2202_ = v___y_2299_;
v___y_2203_ = v___y_2290_;
v___y_2204_ = v___y_2288_;
v___y_2205_ = v___y_2300_;
v___y_2206_ = v___x_2305_;
v_env_2207_ = v_env_2311_;
v_messages_2208_ = v_messages_2312_;
v_scopes_2209_ = v_scopes_2313_;
v_infoState_2210_ = v_infoState_2314_;
v_traceState_2211_ = v_traceState_2315_;
v_snapshotTasks_2212_ = v_snapshotTasks_2316_;
v_codeQualityEntryTasks_2213_ = v_codeQualityEntryTasks_2317_;
v___y_2214_ = v___y_2301_;
v___y_2215_ = v___y_2295_;
v___y_2216_ = v___y_2302_;
v_reportedCmdState_2217_ = v___x_2335_;
goto v___jp_2185_;
}
}
else
{
lean_inc_ref(v___x_2305_);
lean_inc(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2290_);
lean_inc(v___y_2289_);
lean_inc_ref(v___y_2286_);
v___y_2252_ = v___y_2286_;
v___y_2253_ = v___y_2287_;
v___y_2254_ = v___y_2289_;
v___y_2255_ = v___y_2290_;
v___y_2256_ = v___y_2292_;
v___y_2257_ = v___y_2293_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2297_;
v___y_2260_ = v___y_2286_;
v___y_2261_ = v___y_2289_;
v___y_2262_ = v___y_2291_;
v___y_2263_ = v___y_2298_;
v___y_2264_ = v___y_2292_;
v___y_2265_ = v___f_2308_;
v___y_2266_ = v___y_2293_;
v___y_2267_ = v___y_2296_;
v___y_2268_ = v___y_2299_;
v___y_2269_ = v___y_2290_;
v___y_2270_ = v___y_2288_;
v___y_2271_ = v___y_2300_;
v___y_2272_ = v___x_2305_;
v___y_2273_ = v___y_2301_;
v___y_2274_ = v___y_2295_;
v___y_2275_ = v___y_2302_;
v_reportedCmdState_2276_ = v___x_2305_;
goto v___jp_2251_;
}
}
}
v___jp_2336_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2342_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2134_);
v___x_2343_ = l_IO_CancelToken_new();
v___x_2344_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2135_);
v___x_2345_ = l_Lean_Name_str___override(v___x_2135_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2347_ = l_Lean_Name_str___override(v___x_2345_, v___x_2346_);
v___x_2348_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2349_ = l_Lean_Name_str___override(v___x_2347_, v___x_2348_);
v___x_2350_ = l_Lean_Name_str___override(v___x_2349_, v___x_2346_);
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = l_Lean_Name_num___override(v___x_2350_, v___x_2351_);
v___x_2353_ = l_Lean_Name_str___override(v___x_2352_, v___x_2346_);
v___x_2354_ = l_Lean_Name_str___override(v___x_2353_, v___x_2348_);
v___x_2355_ = l_Lean_Name_str___override(v___x_2354_, v___x_2346_);
v___x_2356_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2357_ = l_Lean_Name_str___override(v___x_2355_, v___x_2356_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2359_ = l_Lean_Name_str___override(v___x_2357_, v___x_2358_);
v___x_2360_ = l_Lean_Name_toString(v___x_2359_, v___x_2136_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_unsigned_to_nat(32u);
v___x_2363_ = lean_mk_empty_array_with_capacity(v___x_2362_);
lean_dec_ref(v___x_2363_);
v___x_2364_ = ((size_t)5ULL);
v___x_2365_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2360_, 2);
v___x_2366_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2366_, 0, v___x_2360_);
lean_ctor_set(v___x_2366_, 1, v___x_2342_);
lean_ctor_set(v___x_2366_, 2, v___x_2361_);
lean_ctor_set(v___x_2366_, 3, v___x_2365_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*4, v_val_2132_);
v___x_2367_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2368_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2360_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
lean_ctor_set(v___x_2368_, 2, v___x_2361_);
lean_ctor_set(v___x_2368_, 3, v___x_2365_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*4, v_val_2132_);
lean_inc(v___y_2338_);
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___y_2338_);
v___x_2370_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2369_);
lean_inc_ref(v___x_2343_);
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2343_);
v___x_2372_ = l_IO_Promise_result_x21___redArg(v___x_2149_);
lean_inc_ref(v___x_2372_);
lean_inc(v___x_2370_);
lean_inc_ref_n(v___x_2369_, 3);
v___x_2373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2369_);
lean_ctor_set(v___x_2373_, 1, v___x_2370_);
lean_ctor_set(v___x_2373_, 2, v___x_2371_);
lean_ctor_set(v___x_2373_, 3, v___x_2372_);
v___x_2374_ = l_IO_Promise_result_x21___redArg(v___x_2150_);
lean_inc_ref(v___x_2374_);
lean_inc_n(v___y_2340_, 3);
v___x_2375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2369_);
lean_ctor_set(v___x_2375_, 1, v___y_2340_);
lean_ctor_set(v___x_2375_, 2, v___x_2361_);
lean_ctor_set(v___x_2375_, 3, v___x_2374_);
v___x_2376_ = l_IO_Promise_result_x21___redArg(v___x_2151_);
lean_inc_ref(v___x_2376_);
v___x_2377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2369_);
lean_ctor_set(v___x_2377_, 1, v___y_2340_);
lean_ctor_set(v___x_2377_, 2, v___x_2361_);
lean_ctor_set(v___x_2377_, 3, v___x_2376_);
v___x_2378_ = l_IO_Promise_result_x21___redArg(v___x_2152_);
v___x_2379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2361_);
lean_ctor_set(v___x_2379_, 1, v___y_2340_);
lean_ctor_set(v___x_2379_, 2, v___x_2361_);
lean_ctor_set(v___x_2379_, 3, v___x_2378_);
lean_inc_ref(v___x_2368_);
v___x_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2368_);
lean_ctor_set(v___x_2380_, 1, v___x_2373_);
lean_ctor_set(v___x_2380_, 2, v___x_2375_);
lean_ctor_set(v___x_2380_, 3, v___x_2377_);
lean_ctor_set(v___x_2380_, 4, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2366_);
lean_ctor_set(v___x_2381_, 1, v___y_2338_);
lean_ctor_set(v___x_2381_, 2, v___y_2339_);
lean_ctor_set(v___x_2381_, 3, v___x_2380_);
lean_ctor_set(v___x_2381_, 4, v___y_2341_);
v___x_2382_ = lean_io_promise_resolve(v___x_2381_, v_prom_2145_);
if (lean_obj_tag(v_old_x3f_2146_) == 0)
{
v___y_2286_ = v___x_2360_;
v___y_2287_ = v___x_2362_;
v___y_2288_ = v___x_2369_;
v___y_2289_ = v___x_2351_;
v___y_2290_ = v___x_2368_;
v___y_2291_ = v___x_2370_;
v___y_2292_ = v___x_2361_;
v___y_2293_ = v___x_2361_;
v___y_2294_ = v___x_2364_;
v___y_2295_ = v___x_2343_;
v___y_2296_ = v___x_2372_;
v___y_2297_ = v___x_2365_;
v___y_2298_ = v___x_2361_;
v___y_2299_ = v___y_2340_;
v___y_2300_ = v___y_2337_;
v___y_2301_ = v___x_2376_;
v___y_2302_ = v___x_2374_;
v___y_2303_ = v___x_2361_;
goto v___jp_2285_;
}
else
{
lean_object* v_val_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2394_; 
v_val_2383_ = lean_ctor_get(v_old_x3f_2146_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_old_x3f_2146_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2385_ = v_old_x3f_2146_;
v_isShared_2386_ = v_isSharedCheck_2394_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_val_2383_);
lean_dec(v_old_x3f_2146_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2394_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v_elabSnap_2387_; lean_object* v_stx_2388_; lean_object* v_elabSnap_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v_elabSnap_2387_ = lean_ctor_get(v_val_2383_, 3);
lean_inc_ref(v_elabSnap_2387_);
v_stx_2388_ = lean_ctor_get(v_val_2383_, 1);
lean_inc(v_stx_2388_);
lean_dec(v_val_2383_);
v_elabSnap_2389_ = lean_ctor_get(v_elabSnap_2387_, 1);
lean_inc_ref(v_elabSnap_2389_);
lean_dec_ref(v_elabSnap_2387_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_stx_2388_);
lean_ctor_set(v___x_2390_, 1, v_elabSnap_2389_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2390_);
v___x_2392_ = v___x_2385_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
v___y_2286_ = v___x_2360_;
v___y_2287_ = v___x_2362_;
v___y_2288_ = v___x_2369_;
v___y_2289_ = v___x_2351_;
v___y_2290_ = v___x_2368_;
v___y_2291_ = v___x_2370_;
v___y_2292_ = v___x_2361_;
v___y_2293_ = v___x_2361_;
v___y_2294_ = v___x_2364_;
v___y_2295_ = v___x_2343_;
v___y_2296_ = v___x_2372_;
v___y_2297_ = v___x_2365_;
v___y_2298_ = v___x_2361_;
v___y_2299_ = v___y_2340_;
v___y_2300_ = v___y_2337_;
v___y_2301_ = v___x_2376_;
v___y_2302_ = v___x_2374_;
v___y_2303_ = v___x_2392_;
goto v___jp_2285_;
}
}
}
}
v___jp_2395_:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2398_);
lean_inc(v_fst_2129_);
v___x_2400_ = l_Lean_Parser_isTerminalCommand(v_fst_2129_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v_toProcessingContext_2402_; lean_object* v_pos_2403_; lean_object* v_endPos_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2401_ = lean_io_promise_new();
v_toProcessingContext_2402_ = lean_ctor_get(v_a_2133_, 0);
v_pos_2403_ = lean_ctor_get(v_fst_2131_, 0);
v_endPos_2404_ = lean_ctor_get(v_toProcessingContext_2402_, 3);
lean_inc(v___x_2401_);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2401_);
v___x_2406_ = lean_box(0);
lean_inc(v_endPos_2404_);
lean_inc(v_pos_2403_);
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v_pos_2403_);
lean_ctor_set(v___x_2407_, 1, v_endPos_2404_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_parseCancelTk_2147_);
v___x_2410_ = l_IO_Promise_result_x21___redArg(v___x_2401_);
lean_dec(v___x_2401_);
v___x_2411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2406_);
lean_ctor_set(v___x_2411_, 1, v___x_2408_);
lean_ctor_set(v___x_2411_, 2, v___x_2409_);
lean_ctor_set(v___x_2411_, 3, v___x_2410_);
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
v___y_2337_ = v___x_2405_;
v___y_2338_ = v___y_2396_;
v___y_2339_ = v___y_2397_;
v___y_2340_ = v___x_2399_;
v___y_2341_ = v___x_2412_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2413_; 
lean_dec_ref(v_parseCancelTk_2147_);
v___x_2413_ = lean_box(0);
v___y_2337_ = v___x_2413_;
v___y_2338_ = v___y_2396_;
v___y_2339_ = v___y_2397_;
v___y_2340_ = v___x_2399_;
v___y_2341_ = v___x_2413_;
goto v___jp_2336_;
}
}
v___jp_2414_:
{
lean_object* v___x_2417_; 
lean_inc(v_fst_2129_);
v___x_2417_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2129_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_box(0);
v___y_2396_ = v_fst_2415_;
v___y_2397_ = v_snd_2416_;
v___y_2398_ = v___x_2418_;
goto v___jp_2395_;
}
else
{
lean_object* v_val_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
v_val_2419_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2421_ = v___x_2417_;
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_val_2419_);
lean_dec(v___x_2417_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_inc(v_val_2419_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_val_2419_);
lean_ctor_set(v___x_2423_, 1, v_val_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
v___y_2396_ = v_fst_2415_;
v___y_2397_ = v_snd_2416_;
v___y_2398_ = v___x_2425_;
goto v___jp_2395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2432_ = _args[0];
lean_object* v_revCmds_2433_ = _args[1];
lean_object* v_fst_2434_ = _args[2];
lean_object* v_val_2435_ = _args[3];
lean_object* v_a_2436_ = _args[4];
lean_object* v_snd_2437_ = _args[5];
lean_object* v___x_2438_ = _args[6];
lean_object* v___x_2439_ = _args[7];
lean_object* v___x_2440_ = _args[8];
lean_object* v___f_2441_ = _args[9];
lean_object* v___f_2442_ = _args[10];
lean_object* v___f_2443_ = _args[11];
lean_object* v_pos_2444_ = _args[12];
lean_object* v_cmdState_2445_ = _args[13];
lean_object* v___x_2446_ = _args[14];
lean_object* v_opts_2447_ = _args[15];
lean_object* v_prom_2448_ = _args[16];
lean_object* v_old_x3f_2449_ = _args[17];
lean_object* v_parseCancelTk_2450_ = _args[18];
lean_object* v___y_2451_ = _args[19];
_start:
{
uint8_t v_val_37622__boxed_2452_; uint8_t v___x_37625__boxed_2453_; lean_object* v_res_2454_; 
v_val_37622__boxed_2452_ = lean_unbox(v_val_2435_);
v___x_37625__boxed_2453_ = lean_unbox(v___x_2439_);
v_res_2454_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2432_, v_revCmds_2433_, v_fst_2434_, v_val_37622__boxed_2452_, v_a_2436_, v_snd_2437_, v___x_2438_, v___x_37625__boxed_2453_, v___x_2440_, v___f_2441_, v___f_2442_, v___f_2443_, v_pos_2444_, v_cmdState_2445_, v___x_2446_, v_opts_2447_, v_prom_2448_, v_old_x3f_2449_, v_parseCancelTk_2450_);
lean_dec(v_prom_2448_);
lean_dec_ref(v_opts_2447_);
lean_dec_ref(v_a_2436_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2457_, lean_object* v_parserState_2458_, lean_object* v_cmdState_2459_, lean_object* v_prom_2460_, uint8_t v_sync_2461_, lean_object* v_parseCancelTk_2462_, lean_object* v_revCmds_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v___y_2469_; lean_object* v_toSnapshot_2471_; lean_object* v_stx_2472_; lean_object* v_parserState_2473_; lean_object* v_elabSnap_2474_; lean_object* v_val_2475_; lean_object* v_newParserState_2476_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; uint8_t v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; uint8_t v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v_fst_2552_; lean_object* v_snd_2553_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; uint8_t v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___x_2648_; 
v___f_2507_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2508_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2509_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2510_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2511_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2648_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2457_) == 1)
{
lean_object* v_val_2681_; lean_object* v_nextCmdSnap_x3f_2682_; 
v_val_2681_ = lean_ctor_get(v_old_x3f_2457_, 0);
v_nextCmdSnap_x3f_2682_ = lean_ctor_get(v_val_2681_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2682_) == 0)
{
goto v___jp_2649_;
}
else
{
lean_object* v_toSnapshot_2683_; lean_object* v_stx_2684_; lean_object* v_parserState_2685_; lean_object* v_elabSnap_2686_; lean_object* v_val_2687_; lean_object* v___x_2688_; 
v_toSnapshot_2683_ = lean_ctor_get(v_val_2681_, 0);
v_stx_2684_ = lean_ctor_get(v_val_2681_, 1);
v_parserState_2685_ = lean_ctor_get(v_val_2681_, 2);
v_elabSnap_2686_ = lean_ctor_get(v_val_2681_, 3);
v_val_2687_ = lean_ctor_get(v_nextCmdSnap_x3f_2682_, 0);
lean_inc(v_val_2687_);
v___x_2688_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2687_);
if (lean_obj_tag(v___x_2688_) == 1)
{
lean_object* v_val_2689_; lean_object* v_nextCmdSnap_x3f_2690_; 
v_val_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v_nextCmdSnap_x3f_2690_ = lean_ctor_get(v_val_2689_, 4);
lean_inc(v_nextCmdSnap_x3f_2690_);
lean_dec(v_val_2689_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2690_) == 0)
{
goto v___jp_2649_;
}
else
{
lean_object* v_val_2691_; lean_object* v___x_2692_; 
v_val_2691_ = lean_ctor_get(v_nextCmdSnap_x3f_2690_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2690_, 1);
v___x_2692_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2691_);
if (lean_obj_tag(v___x_2692_) == 1)
{
lean_object* v_val_2693_; lean_object* v_parserState_2694_; lean_object* v_pos_2695_; uint8_t v___x_2696_; 
v_val_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_val_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v_parserState_2694_ = lean_ctor_get(v_val_2693_, 2);
lean_inc_ref(v_parserState_2694_);
lean_dec(v_val_2693_);
v_pos_2695_ = lean_ctor_get(v_parserState_2694_, 0);
lean_inc(v_pos_2695_);
lean_dec_ref(v_parserState_2694_);
v___x_2696_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2695_, v_a_2464_);
lean_dec(v_pos_2695_);
if (v___x_2696_ == 0)
{
goto v___jp_2649_;
}
else
{
lean_inc(v_val_2687_);
lean_inc_ref(v_elabSnap_2686_);
lean_inc_ref_n(v_parserState_2685_, 2);
lean_inc(v_stx_2684_);
lean_inc_ref(v_toSnapshot_2683_);
lean_dec_ref_known(v_old_x3f_2457_, 1);
lean_dec_ref(v_parseCancelTk_2462_);
lean_dec_ref(v_cmdState_2459_);
lean_dec_ref(v_parserState_2458_);
v_toSnapshot_2471_ = v_toSnapshot_2683_;
v_stx_2472_ = v_stx_2684_;
v_parserState_2473_ = v_parserState_2685_;
v_elabSnap_2474_ = v_elabSnap_2686_;
v_val_2475_ = v_val_2687_;
v_newParserState_2476_ = v_parserState_2685_;
goto v___jp_2470_;
}
}
else
{
lean_dec(v___x_2692_);
goto v___jp_2649_;
}
}
}
else
{
lean_dec(v___x_2688_);
goto v___jp_2649_;
}
}
}
else
{
goto v___jp_2649_;
}
v___jp_2466_:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_box(0);
return v___x_2467_;
}
v___jp_2468_:
{
goto v___jp_2466_;
}
v___jp_2470_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_resultSnap_2479_; lean_object* v_task_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2503_; 
v___x_2477_ = lean_io_promise_new();
v___x_2478_ = l_IO_CancelToken_new();
v_resultSnap_2479_ = lean_ctor_get(v_elabSnap_2474_, 2);
lean_inc_ref(v_resultSnap_2479_);
v_task_2480_ = lean_ctor_get(v_resultSnap_2479_, 3);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_resultSnap_2479_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; 
v_unused_2504_ = lean_ctor_get(v_resultSnap_2479_, 2);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_resultSnap_2479_, 1);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_resultSnap_2479_, 0);
lean_dec(v_unused_2506_);
v___x_2482_ = v_resultSnap_2479_;
v_isShared_2483_ = v_isSharedCheck_2503_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_task_2480_);
lean_dec(v_resultSnap_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2503_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v_toProcessingContext_2489_; lean_object* v_pos_2490_; lean_object* v_endPos_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2484_ = lean_box(v_sync_2461_);
lean_inc_ref(v_a_2464_);
lean_inc_ref(v___x_2478_);
lean_inc(v___x_2477_);
lean_inc_ref(v_newParserState_2476_);
lean_inc(v_stx_2472_);
v___f_2485_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2485_, 0, v_val_2475_);
lean_closure_set(v___f_2485_, 1, v_stx_2472_);
lean_closure_set(v___f_2485_, 2, v_revCmds_2463_);
lean_closure_set(v___f_2485_, 3, v_newParserState_2476_);
lean_closure_set(v___f_2485_, 4, v___x_2477_);
lean_closure_set(v___f_2485_, 5, v___x_2484_);
lean_closure_set(v___f_2485_, 6, v___x_2478_);
lean_closure_set(v___f_2485_, 7, v_a_2464_);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = 1;
v___x_2488_ = l_BaseIO_chainTask___redArg(v_task_2480_, v___f_2485_, v___x_2486_, v___x_2487_);
v_toProcessingContext_2489_ = lean_ctor_get(v_a_2464_, 0);
v_pos_2490_ = lean_ctor_get(v_newParserState_2476_, 0);
lean_inc(v_pos_2490_);
lean_dec_ref(v_newParserState_2476_);
v_endPos_2491_ = lean_ctor_get(v_toProcessingContext_2489_, 3);
v___x_2492_ = lean_box(0);
lean_inc(v_endPos_2491_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_pos_2490_);
lean_ctor_set(v___x_2493_, 1, v_endPos_2491_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2478_);
v___x_2496_ = l_IO_Promise_result_x21___redArg(v___x_2477_);
lean_dec(v___x_2477_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 3, v___x_2496_);
lean_ctor_set(v___x_2482_, 2, v___x_2495_);
lean_ctor_set(v___x_2482_, 1, v___x_2494_);
lean_ctor_set(v___x_2482_, 0, v___x_2492_);
v___x_2498_ = v___x_2482_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2500_, 0, v_toSnapshot_2471_);
lean_ctor_set(v___x_2500_, 1, v_stx_2472_);
lean_ctor_set(v___x_2500_, 2, v_parserState_2473_);
lean_ctor_set(v___x_2500_, 3, v_elabSnap_2474_);
lean_ctor_set(v___x_2500_, 4, v___x_2499_);
v___x_2501_ = lean_io_promise_resolve(v___x_2500_, v_prom_2460_);
lean_dec(v_prom_2460_);
return v___x_2501_;
}
}
}
v___jp_2512_:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2529_);
v___x_2531_ = l_Lean_Parser_isTerminalCommand(v___y_2520_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_io_promise_new();
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
v___x_2534_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2530_, v___y_2525_, v___y_2526_, v_revCmds_2463_, v___y_2519_, v___y_2523_, v_a_2464_, v___y_2515_, v___y_2518_, v___y_2516_, v___y_2527_, v___y_2517_, v___y_2528_, v___x_2510_, v___f_2509_, v___f_2508_, v___f_2507_, v___y_2513_, v_cmdState_2459_, v___y_2514_, v___x_2511_, v___y_2522_, v___y_2521_, v___y_2524_, v_prom_2460_, v_old_x3f_2457_, v_parseCancelTk_2462_, v___x_2533_);
lean_dec(v_prom_2460_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2528_);
lean_dec(v___y_2525_);
v___y_2469_ = v___x_2534_;
goto v___jp_2468_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2530_, v___y_2525_, v___y_2526_, v_revCmds_2463_, v___y_2519_, v___y_2523_, v_a_2464_, v___y_2515_, v___y_2518_, v___y_2516_, v___y_2527_, v___y_2517_, v___y_2528_, v___x_2510_, v___f_2509_, v___f_2508_, v___f_2507_, v___y_2513_, v_cmdState_2459_, v___y_2514_, v___x_2511_, v___y_2522_, v___y_2521_, v___y_2524_, v_prom_2460_, v_old_x3f_2457_, v_parseCancelTk_2462_, v___x_2535_);
lean_dec(v_prom_2460_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2528_);
lean_dec(v___y_2525_);
v___y_2469_ = v___x_2536_;
goto v___jp_2468_;
}
}
v___jp_2537_:
{
lean_object* v___x_2554_; 
lean_inc(v___y_2551_);
v___x_2554_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2551_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_box(0);
v___y_2513_ = v___y_2538_;
v___y_2514_ = v___y_2539_;
v___y_2515_ = v___y_2540_;
v___y_2516_ = v___y_2541_;
v___y_2517_ = v___y_2542_;
v___y_2518_ = v___y_2543_;
v___y_2519_ = v___y_2544_;
v___y_2520_ = v___y_2551_;
v___y_2521_ = v___y_2545_;
v___y_2522_ = v___y_2546_;
v___y_2523_ = v___y_2547_;
v___y_2524_ = v_snd_2553_;
v___y_2525_ = v___y_2548_;
v___y_2526_ = v___y_2549_;
v___y_2527_ = v_fst_2552_;
v___y_2528_ = v___y_2550_;
v___y_2529_ = v___x_2555_;
goto v___jp_2512_;
}
else
{
lean_object* v_val_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
v_val_2556_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v___x_2554_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_val_2556_);
lean_dec(v___x_2554_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_inc(v_val_2556_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_val_2556_);
lean_ctor_set(v___x_2560_, 1, v_val_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
v___y_2513_ = v___y_2538_;
v___y_2514_ = v___y_2539_;
v___y_2515_ = v___y_2540_;
v___y_2516_ = v___y_2541_;
v___y_2517_ = v___y_2542_;
v___y_2518_ = v___y_2543_;
v___y_2519_ = v___y_2544_;
v___y_2520_ = v___y_2551_;
v___y_2521_ = v___y_2545_;
v___y_2522_ = v___y_2546_;
v___y_2523_ = v___y_2547_;
v___y_2524_ = v_snd_2553_;
v___y_2525_ = v___y_2548_;
v___y_2526_ = v___y_2549_;
v___y_2527_ = v_fst_2552_;
v___y_2528_ = v___y_2550_;
v___y_2529_ = v___x_2562_;
goto v___jp_2512_;
}
}
}
}
v___jp_2565_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2570_ = l_Lean_Name_str___override(v___y_2567_, v___x_2569_);
v___x_2571_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2572_ = l_Lean_Name_str___override(v___x_2570_, v___x_2571_);
v___x_2573_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2574_ = l_Lean_Name_str___override(v___x_2572_, v___x_2573_);
v___x_2575_ = l_Lean_Name_str___override(v___x_2574_, v___x_2571_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = l_Lean_Name_num___override(v___x_2575_, v___x_2576_);
v___x_2578_ = l_Lean_Name_str___override(v___x_2577_, v___x_2571_);
v___x_2579_ = l_Lean_Name_str___override(v___x_2578_, v___x_2573_);
v___x_2580_ = l_Lean_Name_str___override(v___x_2579_, v___x_2571_);
v___x_2581_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2582_ = l_Lean_Name_str___override(v___x_2580_, v___x_2581_);
v___x_2583_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2584_ = l_Lean_Name_str___override(v___x_2582_, v___x_2583_);
v___x_2585_ = l_Lean_Name_toString(v___x_2584_, v___y_2566_);
v___x_2586_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2589_ = 0;
v___x_2590_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2590_, 0, v___x_2585_);
lean_ctor_set(v___x_2590_, 1, v___x_2586_);
lean_ctor_set(v___x_2590_, 2, v___x_2587_);
lean_ctor_set(v___x_2590_, 3, v___x_2588_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*4, v___x_2589_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2593_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2590_, 3);
v___x_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2590_);
lean_ctor_set(v___x_2594_, 1, v_cmdState_2459_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
v___x_2595_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2587_, v___x_2594_);
v___x_2596_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2587_, v___x_2590_);
v___x_2597_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2590_);
lean_ctor_set(v___x_2598_, 1, v___x_2592_);
lean_ctor_set(v___x_2598_, 2, v___x_2595_);
lean_ctor_set(v___x_2598_, 3, v___x_2596_);
lean_ctor_set(v___x_2598_, 4, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2590_);
lean_ctor_set(v___x_2599_, 1, v___x_2591_);
lean_ctor_set(v___x_2599_, 2, v___y_2568_);
lean_ctor_set(v___x_2599_, 3, v___x_2598_);
lean_ctor_set(v___x_2599_, 4, v___x_2587_);
v___x_2600_ = lean_io_promise_resolve(v___x_2599_, v_prom_2460_);
lean_dec(v_prom_2460_);
v___x_2601_ = lean_box(0);
return v___x_2601_;
}
v___jp_2602_:
{
v___y_2566_ = v___y_2603_;
v___y_2567_ = v___y_2604_;
v___y_2568_ = v___y_2605_;
goto v___jp_2565_;
}
v___jp_2607_:
{
uint8_t v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = l_IO_CancelToken_isSet(v_parseCancelTk_2462_);
v___x_2619_ = 1;
if (v___x_2618_ == 0)
{
lean_dec(v___y_2616_);
if (v_sync_2461_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2620_ = lean_io_promise_new();
v___x_2621_ = lean_io_promise_new();
v___x_2622_ = lean_io_promise_new();
v___x_2623_ = lean_io_promise_new();
v___x_2624_ = l_Lean_internal_cmdlineSnapshots;
v___x_2625_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2614_, v___x_2624_);
lean_dec_ref(v___y_2614_);
if (v___x_2625_ == 0)
{
lean_inc(v___y_2615_);
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___x_2622_;
v___y_2540_ = v___y_2610_;
v___y_2541_ = v___x_2619_;
v___y_2542_ = v___x_2620_;
v___y_2543_ = v___y_2612_;
v___y_2544_ = v___y_2613_;
v___y_2545_ = v___x_2624_;
v___y_2546_ = v___y_2609_;
v___y_2547_ = v___x_2618_;
v___y_2548_ = v___x_2623_;
v___y_2549_ = v___y_2611_;
v___y_2550_ = v___x_2621_;
v___y_2551_ = v___y_2615_;
v_fst_2552_ = v___y_2615_;
v_snd_2553_ = v___y_2617_;
goto v___jp_2537_;
}
else
{
uint8_t v___x_2626_; 
lean_inc(v___y_2615_);
v___x_2626_ = l_Lean_Parser_isTerminalCommand(v___y_2615_);
if (v___x_2626_ == 0)
{
if (v___x_2625_ == 0)
{
lean_inc(v___y_2615_);
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___x_2622_;
v___y_2540_ = v___y_2610_;
v___y_2541_ = v___x_2619_;
v___y_2542_ = v___x_2620_;
v___y_2543_ = v___y_2612_;
v___y_2544_ = v___y_2613_;
v___y_2545_ = v___x_2624_;
v___y_2546_ = v___y_2609_;
v___y_2547_ = v___x_2618_;
v___y_2548_ = v___x_2623_;
v___y_2549_ = v___y_2611_;
v___y_2550_ = v___x_2621_;
v___y_2551_ = v___y_2615_;
v_fst_2552_ = v___y_2615_;
v_snd_2553_ = v___y_2617_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v___y_2617_);
v___x_2627_ = lean_box(0);
v___x_2628_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___x_2622_;
v___y_2540_ = v___y_2610_;
v___y_2541_ = v___x_2619_;
v___y_2542_ = v___x_2620_;
v___y_2543_ = v___y_2612_;
v___y_2544_ = v___y_2613_;
v___y_2545_ = v___x_2624_;
v___y_2546_ = v___y_2609_;
v___y_2547_ = v___x_2618_;
v___y_2548_ = v___x_2623_;
v___y_2549_ = v___y_2611_;
v___y_2550_ = v___x_2621_;
v___y_2551_ = v___y_2615_;
v_fst_2552_ = v___x_2627_;
v_snd_2553_ = v___x_2628_;
goto v___jp_2537_;
}
}
else
{
lean_inc(v___y_2615_);
v___y_2538_ = v___y_2608_;
v___y_2539_ = v___x_2622_;
v___y_2540_ = v___y_2610_;
v___y_2541_ = v___x_2619_;
v___y_2542_ = v___x_2620_;
v___y_2543_ = v___y_2612_;
v___y_2544_ = v___y_2613_;
v___y_2545_ = v___x_2624_;
v___y_2546_ = v___y_2609_;
v___y_2547_ = v___x_2618_;
v___y_2548_ = v___x_2623_;
v___y_2549_ = v___y_2611_;
v___y_2550_ = v___x_2621_;
v___y_2551_ = v___y_2615_;
v_fst_2552_ = v___y_2615_;
v_snd_2553_ = v___y_2617_;
goto v___jp_2537_;
}
}
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
v___x_2629_ = lean_box(v___x_2618_);
v___x_2630_ = lean_box(v___x_2619_);
lean_inc_ref(v_a_2464_);
v___f_2631_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2631_, 0, v___y_2611_);
lean_closure_set(v___f_2631_, 1, v_revCmds_2463_);
lean_closure_set(v___f_2631_, 2, v___y_2613_);
lean_closure_set(v___f_2631_, 3, v___x_2629_);
lean_closure_set(v___f_2631_, 4, v_a_2464_);
lean_closure_set(v___f_2631_, 5, v___y_2610_);
lean_closure_set(v___f_2631_, 6, v___y_2612_);
lean_closure_set(v___f_2631_, 7, v___x_2630_);
lean_closure_set(v___f_2631_, 8, v___x_2510_);
lean_closure_set(v___f_2631_, 9, v___f_2509_);
lean_closure_set(v___f_2631_, 10, v___f_2508_);
lean_closure_set(v___f_2631_, 11, v___f_2507_);
lean_closure_set(v___f_2631_, 12, v___y_2608_);
lean_closure_set(v___f_2631_, 13, v_cmdState_2459_);
lean_closure_set(v___f_2631_, 14, v___x_2511_);
lean_closure_set(v___f_2631_, 15, v___y_2609_);
lean_closure_set(v___f_2631_, 16, v_prom_2460_);
lean_closure_set(v___f_2631_, 17, v_old_x3f_2457_);
lean_closure_set(v___f_2631_, 18, v_parseCancelTk_2462_);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2633_ = lean_io_as_task(v___f_2631_, v___x_2632_);
lean_dec_ref(v___x_2633_);
goto v___jp_2466_;
}
}
else
{
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec(v_revCmds_2463_);
lean_dec_ref(v_parseCancelTk_2462_);
if (lean_obj_tag(v_old_x3f_2457_) == 1)
{
lean_object* v_val_2634_; lean_object* v___x_2635_; lean_object* v_children_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v_val_2634_ = lean_ctor_get(v_old_x3f_2457_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v_old_x3f_2457_, 1);
v___x_2635_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2634_);
v_children_2636_ = lean_ctor_get(v___x_2635_, 1);
lean_inc_ref(v_children_2636_);
lean_dec_ref(v___x_2635_);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_array_get_size(v_children_2636_);
v___x_2639_ = lean_nat_dec_lt(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec_ref(v_children_2636_);
v___y_2566_ = v___x_2619_;
v___y_2567_ = v___y_2616_;
v___y_2568_ = v___y_2617_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_nat_dec_le(v___x_2638_, v___x_2638_);
if (v___x_2641_ == 0)
{
if (v___x_2639_ == 0)
{
lean_dec_ref(v_children_2636_);
v___y_2566_ = v___x_2619_;
v___y_2567_ = v___y_2616_;
v___y_2568_ = v___y_2617_;
goto v___jp_2565_;
}
else
{
size_t v___x_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = lean_usize_of_nat(v___x_2638_);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2636_, v___x_2642_, v___x_2643_, v___x_2640_);
lean_dec_ref(v_children_2636_);
v___y_2603_ = v___x_2619_;
v___y_2604_ = v___y_2616_;
v___y_2605_ = v___y_2617_;
v___y_2606_ = v___x_2644_;
goto v___jp_2602_;
}
}
else
{
size_t v___x_2645_; size_t v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = lean_usize_of_nat(v___x_2638_);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2636_, v___x_2645_, v___x_2646_, v___x_2640_);
lean_dec_ref(v_children_2636_);
v___y_2603_ = v___x_2619_;
v___y_2604_ = v___y_2616_;
v___y_2605_ = v___y_2617_;
v___y_2606_ = v___x_2647_;
goto v___jp_2602_;
}
}
}
else
{
lean_dec(v_old_x3f_2457_);
v___y_2566_ = v___x_2619_;
v___y_2567_ = v___y_2616_;
v___y_2568_ = v___y_2617_;
goto v___jp_2565_;
}
}
}
v___jp_2649_:
{
lean_object* v_env_2650_; lean_object* v_scopes_2651_; lean_object* v___x_2652_; lean_object* v_opts_2653_; lean_object* v_currNamespace_2654_; lean_object* v_openDecls_2655_; lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_snd_2661_; 
v_env_2650_ = lean_ctor_get(v_cmdState_2459_, 0);
v_scopes_2651_ = lean_ctor_get(v_cmdState_2459_, 2);
v___x_2652_ = l_List_head_x21___redArg(v___x_2510_, v_scopes_2651_);
v_opts_2653_ = lean_ctor_get(v___x_2652_, 1);
lean_inc_ref_n(v_opts_2653_, 2);
v_currNamespace_2654_ = lean_ctor_get(v___x_2652_, 2);
lean_inc(v_currNamespace_2654_);
v_openDecls_2655_ = lean_ctor_get(v___x_2652_, 3);
lean_inc(v_openDecls_2655_);
lean_dec(v___x_2652_);
lean_inc_ref(v_env_2650_);
v___x_2656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2656_, 0, v_env_2650_);
lean_ctor_set(v___x_2656_, 1, v_opts_2653_);
lean_ctor_set(v___x_2656_, 2, v_currNamespace_2654_);
lean_ctor_set(v___x_2656_, 3, v_openDecls_2655_);
lean_inc_ref(v_parserState_2458_);
lean_inc_ref(v_a_2464_);
v___f_2657_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2657_, 0, v_a_2464_);
lean_closure_set(v___f_2657_, 1, v___x_2656_);
lean_closure_set(v___f_2657_, 2, v_parserState_2458_);
v___x_2658_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2659_ = lean_box(0);
v___x_2660_ = lean_profileit(v___x_2658_, v_opts_2653_, v___f_2657_, v___x_2659_);
v_snd_2661_ = lean_ctor_get(v___x_2660_, 1);
lean_inc(v_snd_2661_);
if (lean_obj_tag(v_old_x3f_2457_) == 1)
{
lean_object* v_val_2662_; lean_object* v_fst_2663_; lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v_pos_2666_; lean_object* v_toSnapshot_2667_; lean_object* v_stx_2668_; lean_object* v_parserState_2669_; lean_object* v_elabSnap_2670_; lean_object* v_nextCmdSnap_x3f_2671_; uint8_t v___x_2672_; 
v_val_2662_ = lean_ctor_get(v_old_x3f_2457_, 0);
v_fst_2663_ = lean_ctor_get(v___x_2660_, 0);
lean_inc_n(v_fst_2663_, 2);
lean_dec(v___x_2660_);
v_fst_2664_ = lean_ctor_get(v_snd_2661_, 0);
lean_inc(v_fst_2664_);
v_snd_2665_ = lean_ctor_get(v_snd_2661_, 1);
lean_inc(v_snd_2665_);
lean_dec(v_snd_2661_);
v_pos_2666_ = lean_ctor_get(v_parserState_2458_, 0);
lean_inc(v_pos_2666_);
lean_dec_ref(v_parserState_2458_);
v_toSnapshot_2667_ = lean_ctor_get(v_val_2662_, 0);
v_stx_2668_ = lean_ctor_get(v_val_2662_, 1);
v_parserState_2669_ = lean_ctor_get(v_val_2662_, 2);
v_elabSnap_2670_ = lean_ctor_get(v_val_2662_, 3);
v_nextCmdSnap_x3f_2671_ = lean_ctor_get(v_val_2662_, 4);
lean_inc(v_stx_2668_);
v___x_2672_ = l_Lean_Syntax_eqWithInfo(v_fst_2663_, v_stx_2668_);
if (v___x_2672_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2671_) == 0)
{
lean_inc(v_fst_2664_);
lean_inc(v_fst_2663_);
lean_inc_ref(v_opts_2653_);
v___y_2608_ = v_pos_2666_;
v___y_2609_ = v_opts_2653_;
v___y_2610_ = v_snd_2665_;
v___y_2611_ = v_fst_2663_;
v___y_2612_ = v___x_2659_;
v___y_2613_ = v_fst_2664_;
v___y_2614_ = v_opts_2653_;
v___y_2615_ = v_fst_2663_;
v___y_2616_ = v___x_2659_;
v___y_2617_ = v_fst_2664_;
goto v___jp_2607_;
}
else
{
lean_object* v_val_2673_; lean_object* v___x_2674_; 
v_val_2673_ = lean_ctor_get(v_nextCmdSnap_x3f_2671_, 0);
lean_inc(v_val_2673_);
v___x_2674_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2648_, v_val_2673_);
lean_inc(v_fst_2664_);
lean_inc(v_fst_2663_);
lean_inc_ref(v_opts_2653_);
v___y_2608_ = v_pos_2666_;
v___y_2609_ = v_opts_2653_;
v___y_2610_ = v_snd_2665_;
v___y_2611_ = v_fst_2663_;
v___y_2612_ = v___x_2659_;
v___y_2613_ = v_fst_2664_;
v___y_2614_ = v_opts_2653_;
v___y_2615_ = v_fst_2663_;
v___y_2616_ = v___x_2659_;
v___y_2617_ = v_fst_2664_;
goto v___jp_2607_;
}
}
else
{
lean_inc(v_val_2662_);
lean_dec(v_pos_2666_);
lean_dec(v_snd_2665_);
lean_dec(v_fst_2663_);
lean_dec_ref_known(v_old_x3f_2457_, 1);
lean_dec_ref(v_opts_2653_);
lean_dec_ref(v_parseCancelTk_2462_);
lean_dec_ref(v_cmdState_2459_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2671_) == 1)
{
lean_object* v_val_2675_; 
lean_inc_ref(v_nextCmdSnap_x3f_2671_);
lean_inc_ref(v_elabSnap_2670_);
lean_inc_ref(v_parserState_2669_);
lean_inc(v_stx_2668_);
lean_inc_ref(v_toSnapshot_2667_);
lean_dec(v_val_2662_);
v_val_2675_ = lean_ctor_get(v_nextCmdSnap_x3f_2671_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2671_, 1);
v_toSnapshot_2471_ = v_toSnapshot_2667_;
v_stx_2472_ = v_stx_2668_;
v_parserState_2473_ = v_parserState_2669_;
v_elabSnap_2474_ = v_elabSnap_2670_;
v_val_2475_ = v_val_2675_;
v_newParserState_2476_ = v_fst_2664_;
goto v___jp_2470_;
}
else
{
lean_object* v___x_2676_; 
lean_dec(v_fst_2664_);
lean_dec(v_revCmds_2463_);
v___x_2676_ = lean_io_promise_resolve(v_val_2662_, v_prom_2460_);
lean_dec(v_prom_2460_);
return v___x_2676_;
}
}
}
else
{
lean_object* v_fst_2677_; lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v_pos_2680_; 
v_fst_2677_ = lean_ctor_get(v___x_2660_, 0);
lean_inc_n(v_fst_2677_, 2);
lean_dec(v___x_2660_);
v_fst_2678_ = lean_ctor_get(v_snd_2661_, 0);
lean_inc_n(v_fst_2678_, 2);
v_snd_2679_ = lean_ctor_get(v_snd_2661_, 1);
lean_inc(v_snd_2679_);
lean_dec(v_snd_2661_);
v_pos_2680_ = lean_ctor_get(v_parserState_2458_, 0);
lean_inc(v_pos_2680_);
lean_dec_ref(v_parserState_2458_);
lean_inc_ref(v_opts_2653_);
v___y_2608_ = v_pos_2680_;
v___y_2609_ = v_opts_2653_;
v___y_2610_ = v_snd_2679_;
v___y_2611_ = v_fst_2677_;
v___y_2612_ = v___x_2659_;
v___y_2613_ = v_fst_2678_;
v___y_2614_ = v_opts_2653_;
v___y_2615_ = v_fst_2677_;
v___y_2616_ = v___x_2659_;
v___y_2617_ = v_fst_2678_;
goto v___jp_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2697_, lean_object* v_stx_2698_, lean_object* v_revCmds_2699_, lean_object* v_newParserState_2700_, lean_object* v_val_2701_, uint8_t v_sync_2702_, lean_object* v_val_2703_, lean_object* v_a_2704_, lean_object* v_oldNext_2705_){
_start:
{
lean_object* v_cmdState_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_cmdState_2707_ = lean_ctor_get(v_oldResult_2697_, 1);
lean_inc_ref(v_cmdState_2707_);
lean_dec_ref(v_oldResult_2697_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_oldNext_2705_);
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_stx_2698_);
lean_ctor_set(v___x_2709_, 1, v_revCmds_2699_);
v___x_2710_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2708_, v_newParserState_2700_, v_cmdState_2707_, v_val_2701_, v_sync_2702_, v_val_2703_, v___x_2709_, v_a_2704_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2711_ = _args[0];
lean_object* v_val_2712_ = _args[1];
lean_object* v_fst_2713_ = _args[2];
lean_object* v_revCmds_2714_ = _args[3];
lean_object* v_fst_2715_ = _args[4];
lean_object* v_val_2716_ = _args[5];
lean_object* v_a_2717_ = _args[6];
lean_object* v_snd_2718_ = _args[7];
lean_object* v___x_2719_ = _args[8];
lean_object* v___x_2720_ = _args[9];
lean_object* v_fst_2721_ = _args[10];
lean_object* v_val_2722_ = _args[11];
lean_object* v_val_2723_ = _args[12];
lean_object* v___x_2724_ = _args[13];
lean_object* v___f_2725_ = _args[14];
lean_object* v___f_2726_ = _args[15];
lean_object* v___f_2727_ = _args[16];
lean_object* v_pos_2728_ = _args[17];
lean_object* v_cmdState_2729_ = _args[18];
lean_object* v_val_2730_ = _args[19];
lean_object* v___x_2731_ = _args[20];
lean_object* v_opts_2732_ = _args[21];
lean_object* v___x_2733_ = _args[22];
lean_object* v_snd_2734_ = _args[23];
lean_object* v_prom_2735_ = _args[24];
lean_object* v_old_x3f_2736_ = _args[25];
lean_object* v_parseCancelTk_2737_ = _args[26];
lean_object* v_next_x3f_2738_ = _args[27];
lean_object* v___y_2739_ = _args[28];
_start:
{
uint8_t v_val_37412__boxed_2740_; uint8_t v___x_37415__boxed_2741_; lean_object* v_res_2742_; 
v_val_37412__boxed_2740_ = lean_unbox(v_val_2716_);
v___x_37415__boxed_2741_ = lean_unbox(v___x_2720_);
v_res_2742_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2711_, v_val_2712_, v_fst_2713_, v_revCmds_2714_, v_fst_2715_, v_val_37412__boxed_2740_, v_a_2717_, v_snd_2718_, v___x_2719_, v___x_37415__boxed_2741_, v_fst_2721_, v_val_2722_, v_val_2723_, v___x_2724_, v___f_2725_, v___f_2726_, v___f_2727_, v_pos_2728_, v_cmdState_2729_, v_val_2730_, v___x_2731_, v_opts_2732_, v___x_2733_, v_snd_2734_, v_prom_2735_, v_old_x3f_2736_, v_parseCancelTk_2737_, v_next_x3f_2738_);
lean_dec(v_prom_2735_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v_opts_2732_);
lean_dec(v_val_2723_);
lean_dec_ref(v_a_2717_);
lean_dec(v_val_2712_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2743_, lean_object* v_parserState_2744_, lean_object* v_cmdState_2745_, lean_object* v_prom_2746_, lean_object* v_sync_2747_, lean_object* v_parseCancelTk_2748_, lean_object* v_revCmds_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
uint8_t v_sync_boxed_2752_; lean_object* v_res_2753_; 
v_sync_boxed_2752_ = lean_unbox(v_sync_2747_);
v_res_2753_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2743_, v_parserState_2744_, v_cmdState_2745_, v_prom_2746_, v_sync_boxed_2752_, v_parseCancelTk_2748_, v_revCmds_2749_, v_a_2750_);
lean_dec_ref(v_a_2750_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2754_, size_t v_i_2755_, size_t v_stop_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2754_, v_i_2755_, v_stop_2756_, v_b_2757_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2761_, lean_object* v_i_2762_, lean_object* v_stop_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
size_t v_i_boxed_2767_; size_t v_stop_boxed_2768_; lean_object* v_res_2769_; 
v_i_boxed_2767_ = lean_unbox_usize(v_i_2762_);
lean_dec(v_i_2762_);
v_stop_boxed_2768_ = lean_unbox_usize(v_stop_2763_);
lean_dec(v_stop_2763_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2761_, v_i_boxed_2767_, v_stop_boxed_2768_, v_b_2764_, v___y_2765_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v_as_2761_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2770_, lean_object* v_opt_2771_){
_start:
{
lean_object* v_name_2772_; lean_object* v_map_2773_; lean_object* v___x_2774_; 
v_name_2772_ = lean_ctor_get(v_opt_2771_, 0);
v_map_2773_ = lean_ctor_get(v_opts_2770_, 0);
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2773_, v_name_2772_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_box(0);
return v___x_2775_;
}
else
{
lean_object* v_val_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2785_; 
v_val_2776_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2778_ = v___x_2774_;
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_val_2776_);
lean_dec(v___x_2774_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
if (lean_obj_tag(v_val_2776_) == 0)
{
lean_object* v_v_2780_; lean_object* v___x_2782_; 
v_v_2780_ = lean_ctor_get(v_val_2776_, 0);
lean_inc_ref(v_v_2780_);
lean_dec_ref_known(v_val_2776_, 1);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v_v_2780_);
v___x_2782_ = v___x_2778_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_v_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
lean_object* v___x_2784_; 
lean_del_object(v___x_2778_);
lean_dec(v_val_2776_);
v___x_2784_ = lean_box(0);
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2786_, lean_object* v_opt_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2786_, v_opt_2787_);
lean_dec_ref(v_opt_2787_);
lean_dec_ref(v_opts_2786_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2789_, lean_object* v_x_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2789_);
v___x_2792_ = lean_box(0);
v___x_2793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2793_, 0, v_x_2790_);
lean_ctor_set(v___x_2793_, 1, v___x_2791_);
lean_ctor_set(v___x_2793_, 2, v___x_2792_);
return v___x_2793_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2800_ = l_Lean_Array_toPArray_x27___redArg(v___x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
if (lean_obj_tag(v_a_2801_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = l_List_reverse___redArg(v_a_2802_);
return v___x_2803_;
}
else
{
lean_object* v_head_2804_; lean_object* v_tail_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2818_; 
v_head_2804_ = lean_ctor_get(v_a_2801_, 0);
v_tail_2805_ = lean_ctor_get(v_a_2801_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2801_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2807_ = v_a_2801_;
v_isShared_2808_ = v_isSharedCheck_2818_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_tail_2805_);
lean_inc(v_head_2804_);
lean_dec(v_a_2801_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2818_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2809_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v_head_2804_);
v___x_2811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
v___x_2812_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v_a_2802_);
lean_ctor_set(v___x_2807_, 0, v___x_2813_);
v___x_2815_ = v___x_2807_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_a_2802_);
v___x_2815_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
v_a_2801_ = v_tail_2805_;
v_a_2802_ = v___x_2815_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2819_; double v___x_2820_; 
v___x_2819_ = lean_unsigned_to_nat(1000000000u);
v___x_2820_ = lean_float_of_nat(v___x_2819_);
return v___x_2820_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2838_ = l_Lean_MessageData_ofFormat(v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2839_, lean_object* v_stx_2840_, lean_object* v_origStx_2841_, lean_object* v_toProcessingContext_2842_, lean_object* v___x_2843_, lean_object* v_fileMap_2844_, lean_object* v_parserState_2845_, lean_object* v_a_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, lean_object* v___x_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_toProcessingContext_2852_; lean_object* v___x_2853_; 
v_toProcessingContext_2852_ = lean_ctor_get(v___y_2850_, 0);
lean_inc_ref(v_toProcessingContext_2852_);
lean_inc(v_stx_2840_);
v___x_2853_ = lean_apply_3(v_setupImports_2839_, v_stx_2840_, v_toProcessingContext_2852_, lean_box(0));
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_3067_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_3067_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_3067_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
if (lean_obj_tag(v_a_2854_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; 
lean_dec_ref(v___x_2849_);
lean_dec(v___x_2847_);
lean_dec_ref(v_parserState_2845_);
lean_dec_ref(v_fileMap_2844_);
lean_dec(v___x_2843_);
lean_dec_ref(v_toProcessingContext_2842_);
lean_dec(v_origStx_2841_);
lean_dec(v_stx_2840_);
v_a_2858_ = lean_ctor_get(v_a_2854_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v_a_2854_, 1);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v_a_2858_);
v___x_2860_ = v___x_2856_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_3066_; 
v_a_2862_ = lean_ctor_get(v_a_2854_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_a_2854_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_2864_ = v_a_2854_;
v_isShared_2865_ = v_isSharedCheck_3066_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v_a_2854_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_3066_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v_mainModuleName_2867_; lean_object* v_package_x3f_2868_; uint8_t v_isModule_2869_; lean_object* v_imports_2870_; lean_object* v_opts_2871_; uint32_t v_trustLevel_2872_; lean_object* v_importArts_2873_; lean_object* v_plugins_2874_; double v___x_2875_; double v___x_2876_; double v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2882_; 
v___x_2866_ = lean_io_mono_nanos_now();
v_mainModuleName_2867_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_mainModuleName_2867_);
v_package_x3f_2868_ = lean_ctor_get(v_a_2862_, 1);
lean_inc(v_package_x3f_2868_);
v_isModule_2869_ = lean_ctor_get_uint8(v_a_2862_, sizeof(void*)*6 + 4);
v_imports_2870_ = lean_ctor_get(v_a_2862_, 2);
lean_inc_ref(v_imports_2870_);
v_opts_2871_ = lean_ctor_get(v_a_2862_, 3);
lean_inc_ref(v_opts_2871_);
v_trustLevel_2872_ = lean_ctor_get_uint32(v_a_2862_, sizeof(void*)*6);
v_importArts_2873_ = lean_ctor_get(v_a_2862_, 4);
lean_inc(v_importArts_2873_);
v_plugins_2874_ = lean_ctor_get(v_a_2862_, 5);
lean_inc_ref(v_plugins_2874_);
lean_dec(v_a_2862_);
v___x_2875_ = lean_float_of_nat(v___x_2866_);
v___x_2876_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2877_ = lean_float_div(v___x_2875_, v___x_2876_);
v___x_2878_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2840_);
v___x_2879_ = l_Lean_MessageLog_empty;
v___x_2880_ = 1;
lean_inc(v_stx_2840_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v_stx_2840_);
v___x_2882_ = v___x_2864_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_stx_2840_);
v___x_2882_ = v_reuseFailAlloc_3065_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_origStx_2841_);
lean_inc_ref(v___x_2882_);
lean_inc_ref(v_opts_2871_);
v___x_2884_ = l_Lean_Elab_processHeaderCore(v___x_2878_, v_imports_2870_, v_isModule_2869_, v_opts_2871_, v___x_2879_, v_toProcessingContext_2842_, v_trustLevel_2872_, v_plugins_2874_, v___x_2880_, v_mainModuleName_2867_, v_package_x3f_2868_, v_importArts_2873_, v___x_2882_, v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_3056_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_3056_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_3056_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_fst_2889_; lean_object* v_snd_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_3055_; 
v_fst_2889_ = lean_ctor_get(v_a_2885_, 0);
v_snd_2890_ = lean_ctor_get(v_a_2885_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_a_2885_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_2892_ = v_a_2885_;
v_isShared_2893_ = v_isSharedCheck_3055_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_snd_2890_);
lean_inc(v_fst_2889_);
lean_dec(v_a_2885_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_3055_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; double v___x_2895_; double v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v_traceState_2914_; 
v___x_2894_ = lean_io_mono_nanos_now();
v___x_2895_ = lean_float_of_nat(v___x_2894_);
v___x_2896_ = lean_float_div(v___x_2895_, v___x_2876_);
lean_inc(v_snd_2890_);
v___x_2897_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2890_);
v___x_2898_ = l_Lean_MessageLog_hasErrors(v_snd_2890_);
if (v___x_2898_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_2856_);
lean_dec_ref(v___x_2849_);
v___x_3024_ = l_Lean_trace_profiler_output;
v___x_3025_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2871_, v___x_3024_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = l_Lean_trace_profiler_serve;
v___x_3027_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2871_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2914_ = v___x_3028_;
goto v___jp_2913_;
}
else
{
goto v___jp_3008_;
}
}
else
{
lean_dec_ref_known(v___x_3025_, 1);
goto v___jp_3008_;
}
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint64_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
lean_del_object(v___x_2892_);
lean_dec(v_snd_2890_);
lean_dec(v_fst_2889_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v_opts_2871_);
lean_dec(v___x_2847_);
lean_dec_ref(v_parserState_2845_);
lean_dec_ref(v_fileMap_2844_);
lean_dec(v_stx_2840_);
v___x_3029_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3030_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3031_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2843_, 2);
v___x_3032_ = l_Lean_Name_num___override(v___x_3031_, v___x_2843_);
v___x_3033_ = l_Lean_Name_str___override(v___x_3032_, v___x_3029_);
v___x_3034_ = l_Lean_Name_str___override(v___x_3033_, v___x_3030_);
v___x_3035_ = l_Lean_Name_str___override(v___x_3034_, v___x_3029_);
v___x_3036_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3037_ = l_Lean_Name_str___override(v___x_3035_, v___x_3036_);
v___x_3038_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3039_ = l_Lean_Name_str___override(v___x_3037_, v___x_3038_);
v___x_3040_ = l_Lean_Name_toString(v___x_3039_, v___x_2880_);
v___x_3041_ = lean_box(0);
v___x_3042_ = 0ULL;
v___x_3043_ = lean_unsigned_to_nat(32u);
v___x_3044_ = lean_mk_empty_array_with_capacity(v___x_3043_);
v___x_3045_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3046_ = ((size_t)5ULL);
v___x_3047_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3044_);
lean_ctor_set(v___x_3047_, 2, v___x_2843_);
lean_ctor_set(v___x_3047_, 3, v___x_2843_);
lean_ctor_set_usize(v___x_3047_, 4, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set_uint64(v___x_3048_, sizeof(void*)*1, v___x_3042_);
v___x_3049_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3040_);
lean_ctor_set(v___x_3049_, 1, v___x_2897_);
lean_ctor_set(v___x_3049_, 2, v___x_3041_);
lean_ctor_set(v___x_3049_, 3, v___x_3048_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*4, v___x_2898_);
v___x_3050_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2849_);
v___x_3051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
lean_ctor_set(v___x_3051_, 2, v___x_3041_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_3051_);
v___x_3053_ = v___x_2856_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
v___jp_2899_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___y_2905_);
v___x_2907_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2907_, 0, v___y_2904_);
lean_ctor_set(v___x_2907_, 1, v___x_2897_);
lean_ctor_set(v___x_2907_, 2, v___x_2906_);
lean_ctor_set(v___x_2907_, 3, v___y_2902_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*4, v___x_2898_);
v___x_2908_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2903_, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2909_, 0, v___y_2900_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
lean_ctor_set(v___x_2909_, 2, v___y_2901_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2909_);
v___x_2911_ = v___x_2887_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
v___jp_2913_:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Language_Lean_reparseOptions(v_opts_2871_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v_env_2918_; lean_object* v_messages_2919_; lean_object* v_scopes_2920_; lean_object* v_usedQuotCtxts_2921_; lean_object* v_nextMacroScope_2922_; lean_object* v_maxRecDepth_2923_; lean_object* v_ngen_2924_; lean_object* v_auxDeclNGen_2925_; lean_object* v_snapshotTasks_2926_; lean_object* v_prevLinterStates_2927_; lean_object* v_codeQualityEntryTasks_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2997_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
lean_inc(v_fst_2889_);
v___x_2917_ = l_Lean_Elab_Command_mkState(v_fst_2889_, v_snd_2890_, v_a_2916_);
v_env_2918_ = lean_ctor_get(v___x_2917_, 0);
v_messages_2919_ = lean_ctor_get(v___x_2917_, 1);
v_scopes_2920_ = lean_ctor_get(v___x_2917_, 2);
v_usedQuotCtxts_2921_ = lean_ctor_get(v___x_2917_, 3);
v_nextMacroScope_2922_ = lean_ctor_get(v___x_2917_, 4);
v_maxRecDepth_2923_ = lean_ctor_get(v___x_2917_, 5);
v_ngen_2924_ = lean_ctor_get(v___x_2917_, 6);
v_auxDeclNGen_2925_ = lean_ctor_get(v___x_2917_, 7);
v_snapshotTasks_2926_ = lean_ctor_get(v___x_2917_, 10);
v_prevLinterStates_2927_ = lean_ctor_get(v___x_2917_, 11);
v_codeQualityEntryTasks_2928_ = lean_ctor_get(v___x_2917_, 12);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; lean_object* v_unused_2999_; 
v_unused_2998_ = lean_ctor_get(v___x_2917_, 9);
lean_dec(v_unused_2998_);
v_unused_2999_ = lean_ctor_get(v___x_2917_, 8);
lean_dec(v_unused_2999_);
v___x_2930_ = v___x_2917_;
v_isShared_2931_ = v_isSharedCheck_2997_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2928_);
lean_inc(v_prevLinterStates_2927_);
lean_inc(v_snapshotTasks_2926_);
lean_inc(v_auxDeclNGen_2925_);
lean_inc(v_ngen_2924_);
lean_inc(v_maxRecDepth_2923_);
lean_inc(v_nextMacroScope_2922_);
lean_inc(v_usedQuotCtxts_2921_);
lean_inc(v_scopes_2920_);
lean_inc(v_messages_2919_);
lean_inc(v_env_2918_);
lean_dec(v___x_2917_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2997_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2932_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2933_ = lean_box(0);
v___x_2934_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_inc_n(v___x_2843_, 4);
v___x_2935_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2843_);
lean_ctor_set(v___x_2935_, 1, v___x_2843_);
lean_ctor_set(v___x_2935_, 2, v___x_2843_);
lean_ctor_set(v___x_2935_, 3, v___x_2843_);
lean_ctor_set(v___x_2935_, 4, v___x_2932_);
lean_ctor_set(v___x_2935_, 5, v___x_2932_);
lean_ctor_set(v___x_2935_, 6, v___x_2932_);
lean_ctor_set(v___x_2935_, 7, v___x_2932_);
lean_ctor_set(v___x_2935_, 8, v___x_2932_);
lean_ctor_set(v___x_2935_, 9, v___x_2932_);
lean_ctor_set(v___x_2935_, 10, v___x_2932_);
lean_ctor_set(v___x_2935_, 11, v___x_2934_);
v___x_2936_ = l_Lean_Options_empty;
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2940_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2941_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2941_, 0, v_fst_2889_);
lean_ctor_set(v___x_2941_, 1, v___x_2933_);
lean_ctor_set(v___x_2941_, 2, v_fileMap_2844_);
lean_ctor_set(v___x_2941_, 3, v___x_2935_);
lean_ctor_set(v___x_2941_, 4, v___x_2936_);
lean_ctor_set(v___x_2941_, 5, v___x_2937_);
lean_ctor_set(v___x_2941_, 6, v___x_2938_);
lean_ctor_set(v___x_2941_, 7, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2840_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 1, v_stx_2840_);
lean_ctor_set(v___x_2892_, 0, v___x_2943_);
v___x_2945_ = v___x_2892_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_stx_2840_);
v___x_2945_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
v___x_2947_ = lean_unsigned_to_nat(2u);
v___x_2948_ = l_Lean_Syntax_getArg(v_stx_2840_, v___x_2947_);
lean_dec(v_stx_2840_);
v___x_2949_ = l_Lean_Syntax_getArgs(v___x_2948_);
lean_dec(v___x_2948_);
v___x_2950_ = lean_array_to_list(v___x_2949_);
v___x_2951_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2950_, v___x_2938_);
v___x_2952_ = l_Lean_List_toPArray_x27___redArg(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2946_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2942_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_mk_empty_array_with_capacity(v___x_2939_);
v___x_2956_ = lean_array_push(v___x_2955_, v___x_2954_);
v___x_2957_ = l_Lean_Array_toPArray_x27___redArg(v___x_2956_);
lean_dec_ref(v___x_2956_);
lean_inc_ref(v___x_2957_);
v___x_2958_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2958_, 0, v___x_2932_);
lean_ctor_set(v___x_2958_, 1, v___x_2932_);
lean_ctor_set(v___x_2958_, 2, v___x_2957_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*3, v___x_2880_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 9, v_traceState_2914_);
lean_ctor_set(v___x_2930_, 8, v___x_2958_);
v___x_2960_ = v___x_2930_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_env_2918_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_messages_2919_);
lean_ctor_set(v_reuseFailAlloc_2995_, 2, v_scopes_2920_);
lean_ctor_set(v_reuseFailAlloc_2995_, 3, v_usedQuotCtxts_2921_);
lean_ctor_set(v_reuseFailAlloc_2995_, 4, v_nextMacroScope_2922_);
lean_ctor_set(v_reuseFailAlloc_2995_, 5, v_maxRecDepth_2923_);
lean_ctor_set(v_reuseFailAlloc_2995_, 6, v_ngen_2924_);
lean_ctor_set(v_reuseFailAlloc_2995_, 7, v_auxDeclNGen_2925_);
lean_ctor_set(v_reuseFailAlloc_2995_, 8, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2995_, 9, v_traceState_2914_);
lean_ctor_set(v_reuseFailAlloc_2995_, 10, v_snapshotTasks_2926_);
lean_ctor_set(v_reuseFailAlloc_2995_, 11, v_prevLinterStates_2927_);
lean_ctor_set(v_reuseFailAlloc_2995_, 12, v_codeQualityEntryTasks_2928_);
v___x_2960_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v_size_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; uint64_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2961_ = lean_io_promise_new();
v___x_2962_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_2962_);
lean_inc(v___x_2961_);
lean_inc_ref(v___x_2960_);
v___x_2963_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2933_, v_parserState_2845_, v___x_2960_, v___x_2961_, v___x_2880_, v___x_2962_, v___x_2938_, v_a_2846_);
v___x_2964_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2965_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2966_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2843_, 3);
v___x_2967_ = l_Lean_Name_num___override(v___x_2966_, v___x_2843_);
v___x_2968_ = lean_unsigned_to_nat(32u);
v___x_2969_ = lean_mk_empty_array_with_capacity(v___x_2968_);
v___x_2970_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2971_ = ((size_t)5ULL);
v___x_2972_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2969_);
lean_ctor_set(v___x_2972_, 2, v___x_2843_);
lean_ctor_set(v___x_2972_, 3, v___x_2843_);
lean_ctor_set_usize(v___x_2972_, 4, v___x_2971_);
v_size_2973_ = lean_ctor_get(v___x_2957_, 2);
v___x_2974_ = l_Lean_Name_str___override(v___x_2967_, v___x_2964_);
v___x_2975_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2847_);
v___x_2976_ = l_Lean_Name_str___override(v___x_2974_, v___x_2965_);
v___x_2977_ = l_Lean_Name_str___override(v___x_2976_, v___x_2964_);
v___x_2978_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2979_ = l_Lean_Name_str___override(v___x_2977_, v___x_2978_);
v___x_2980_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2981_ = l_Lean_Name_str___override(v___x_2979_, v___x_2980_);
v___x_2982_ = l_Lean_Name_toString(v___x_2981_, v___x_2880_);
v___x_2983_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2984_ = 0ULL;
v___x_2985_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2985_, 0, v___x_2972_);
lean_ctor_set_uint64(v___x_2985_, sizeof(void*)*1, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2962_);
v___x_2987_ = l_IO_Promise_result_x21___redArg(v___x_2961_);
lean_dec(v___x_2961_);
v___x_2988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2847_);
lean_ctor_set(v___x_2988_, 1, v___x_2975_);
lean_ctor_set(v___x_2988_, 2, v___x_2986_);
lean_ctor_set(v___x_2988_, 3, v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2960_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_inc_ref(v___x_2985_);
lean_inc_ref(v___x_2982_);
v___x_2991_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2991_, 0, v___x_2982_);
lean_ctor_set(v___x_2991_, 1, v___x_2983_);
lean_ctor_set(v___x_2991_, 2, v___x_2933_);
lean_ctor_set(v___x_2991_, 3, v___x_2985_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*4, v___x_2898_);
v___x_2992_ = lean_nat_dec_lt(v___x_2843_, v_size_2973_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
lean_dec_ref(v___x_2957_);
lean_dec(v___x_2843_);
v___x_2993_ = l_outOfBounds___redArg(v___x_2848_);
v___y_2900_ = v___x_2991_;
v___y_2901_ = v___x_2990_;
v___y_2902_ = v___x_2985_;
v___y_2903_ = v___x_2882_;
v___y_2904_ = v___x_2982_;
v___y_2905_ = v___x_2993_;
goto v___jp_2899_;
}
else
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2848_, v___x_2957_, v___x_2843_);
lean_dec(v___x_2843_);
lean_dec_ref(v___x_2957_);
v___y_2900_ = v___x_2991_;
v___y_2901_ = v___x_2990_;
v___y_2902_ = v___x_2985_;
v___y_2903_ = v___x_2882_;
v___y_2904_ = v___x_2982_;
v___y_2905_ = v___x_2994_;
goto v___jp_2899_;
}
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_traceState_2914_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2892_);
lean_dec(v_snd_2890_);
lean_dec(v_fst_2889_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2882_);
lean_dec(v___x_2847_);
lean_dec_ref(v_parserState_2845_);
lean_dec_ref(v_fileMap_2844_);
lean_dec(v___x_2843_);
lean_dec(v_stx_2840_);
v_a_3000_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2915_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2915_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
v___jp_3008_:
{
uint64_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3009_ = 0ULL;
v___x_3010_ = lean_box(0);
v___x_3011_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_3012_ = lean_box(0);
v___x_3013_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3014_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3014_, 0, v___x_3011_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
lean_ctor_set(v___x_3014_, 2, v___x_3013_);
lean_ctor_set_float(v___x_3014_, sizeof(void*)*3, v___x_2877_);
lean_ctor_set_float(v___x_3014_, sizeof(void*)*3 + 8, v___x_2896_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*3 + 16, v___x_2880_);
v___x_3015_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3016_ = lean_mk_empty_array_with_capacity(v___x_2843_);
v___x_3017_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3014_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
lean_ctor_set(v___x_3017_, 2, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3010_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_unsigned_to_nat(1u);
v___x_3020_ = lean_mk_empty_array_with_capacity(v___x_3019_);
v___x_3021_ = lean_array_push(v___x_3020_, v___x_3018_);
v___x_3022_ = l_Lean_Array_toPArray_x27___redArg(v___x_3021_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set_uint64(v___x_3023_, sizeof(void*)*1, v___x_3009_);
v_traceState_2914_ = v___x_3023_;
goto v___jp_2913_;
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___x_2882_);
lean_dec_ref(v_opts_2871_);
lean_del_object(v___x_2856_);
lean_dec_ref(v___x_2849_);
lean_dec(v___x_2847_);
lean_dec_ref(v_parserState_2845_);
lean_dec_ref(v_fileMap_2844_);
lean_dec(v___x_2843_);
lean_dec(v_stx_2840_);
v_a_3057_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_2884_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_2884_);
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
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___x_2849_);
lean_dec(v___x_2847_);
lean_dec_ref(v_parserState_2845_);
lean_dec_ref(v_fileMap_2844_);
lean_dec(v___x_2843_);
lean_dec_ref(v_toProcessingContext_2842_);
lean_dec(v_origStx_2841_);
lean_dec(v_stx_2840_);
v_a_3068_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2853_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2853_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3076_, lean_object* v_stx_3077_, lean_object* v_origStx_3078_, lean_object* v_toProcessingContext_3079_, lean_object* v___x_3080_, lean_object* v_fileMap_3081_, lean_object* v_parserState_3082_, lean_object* v_a_3083_, lean_object* v___x_3084_, lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3076_, v_stx_3077_, v_origStx_3078_, v_toProcessingContext_3079_, v___x_3080_, v_fileMap_3081_, v_parserState_3082_, v_a_3083_, v___x_3084_, v___x_3085_, v___x_3086_, v___y_3087_);
lean_dec_ref(v___y_3087_);
lean_dec_ref(v___x_3085_);
lean_dec_ref(v_a_3083_);
return v_res_3089_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___f_3091_; 
v___x_3090_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3091_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3091_, 0, v___x_3090_);
return v___f_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3092_, lean_object* v_stx_3093_, lean_object* v_origStx_3094_, lean_object* v_parserState_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_toProcessingContext_3098_; lean_object* v_fileMap_3099_; lean_object* v_endPos_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_toProcessingContext_3098_ = lean_ctor_get(v_a_3096_, 0);
v_fileMap_3099_ = lean_ctor_get(v_toProcessingContext_3098_, 2);
v_endPos_3100_ = lean_ctor_get(v_toProcessingContext_3098_, 3);
v___x_3101_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3102_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3103_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3096_, 2);
lean_inc_ref(v_fileMap_3099_);
lean_inc_ref(v_toProcessingContext_3098_);
v___f_3106_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3106_, 0, v_setupImports_3092_);
lean_closure_set(v___f_3106_, 1, v_stx_3093_);
lean_closure_set(v___f_3106_, 2, v_origStx_3094_);
lean_closure_set(v___f_3106_, 3, v_toProcessingContext_3098_);
lean_closure_set(v___f_3106_, 4, v___x_3105_);
lean_closure_set(v___f_3106_, 5, v_fileMap_3099_);
lean_closure_set(v___f_3106_, 6, v_parserState_3095_);
lean_closure_set(v___f_3106_, 7, v_a_3096_);
lean_closure_set(v___f_3106_, 8, v___x_3104_);
lean_closure_set(v___f_3106_, 9, v___x_3103_);
lean_closure_set(v___f_3106_, 10, v___x_3101_);
lean_inc(v_endPos_3100_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v_endPos_3100_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3109_, 0, lean_box(0));
lean_closure_set(v___x_3109_, 1, v___f_3102_);
lean_closure_set(v___x_3109_, 2, v___f_3106_);
lean_closure_set(v___x_3109_, 3, v_a_3096_);
v___x_3110_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3104_, v___x_3104_, v___x_3108_, v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3111_, lean_object* v_stx_3112_, lean_object* v_origStx_3113_, lean_object* v_parserState_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3111_, v_stx_3112_, v_origStx_3113_, v_parserState_3114_, v_a_3115_);
lean_dec_ref(v_a_3115_);
return v_res_3117_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3118_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = 1;
v___x_3125_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3126_ = l_Lean_Name_toString(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3127_ = 0;
v___x_3128_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3129_ = lean_box(0);
v___x_3130_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3131_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3132_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___x_3130_);
lean_ctor_set(v___x_3132_, 2, v___x_3129_);
lean_ctor_set(v___x_3132_, 3, v___x_3128_);
lean_ctor_set_uint8(v___x_3132_, sizeof(void*)*4, v___x_3127_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3133_, lean_object* v_cmdState_3134_, lean_object* v_a_3135_, lean_object* v_toSnapshot_3136_, lean_object* v_newStx_3137_, lean_object* v_oldCmd_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_diagnostics_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3168_; 
v___x_3140_ = lean_io_promise_new();
v___x_3141_ = l_IO_CancelToken_new();
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_oldCmd_3138_);
v___x_3143_ = 1;
v___x_3144_ = lean_box(0);
lean_inc_ref(v___x_3141_);
lean_inc(v___x_3140_);
lean_inc_ref(v_cmdState_3134_);
v___x_3145_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3142_, v_newParserState_3133_, v_cmdState_3134_, v___x_3140_, v___x_3143_, v___x_3141_, v___x_3144_, v_a_3135_);
v_diagnostics_3146_ = lean_ctor_get(v_toSnapshot_3136_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_toSnapshot_3136_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; lean_object* v_unused_3170_; lean_object* v_unused_3171_; 
v_unused_3169_ = lean_ctor_get(v_toSnapshot_3136_, 3);
lean_dec(v_unused_3169_);
v_unused_3170_ = lean_ctor_get(v_toSnapshot_3136_, 2);
lean_dec(v_unused_3170_);
v_unused_3171_ = lean_ctor_get(v_toSnapshot_3136_, 0);
lean_dec(v_unused_3171_);
v___x_3148_ = v_toSnapshot_3136_;
v_isShared_3149_ = v_isSharedCheck_3168_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_diagnostics_3146_);
lean_dec(v_toSnapshot_3136_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3168_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
v___x_3150_ = lean_box(0);
v___x_3151_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3152_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3153_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3141_);
v___x_3155_ = l_IO_Promise_result_x21___redArg(v___x_3140_);
lean_dec(v___x_3140_);
v___x_3156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3150_);
lean_ctor_set(v___x_3156_, 1, v___x_3151_);
lean_ctor_set(v___x_3156_, 2, v___x_3154_);
lean_ctor_set(v___x_3156_, 3, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_cmdState_3134_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___x_3159_ = 0;
v___x_3160_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v_newStx_3137_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 3, v___x_3153_);
lean_ctor_set(v___x_3148_, 2, v___x_3150_);
lean_ctor_set(v___x_3148_, 0, v___x_3152_);
v___x_3163_ = v___x_3148_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_diagnostics_3146_);
lean_ctor_set(v_reuseFailAlloc_3167_, 2, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3167_, 3, v___x_3153_);
v___x_3163_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_ctor_set_uint8(v___x_3163_, sizeof(void*)*4, v___x_3159_);
v___x_3164_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3161_, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3160_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
lean_ctor_set(v___x_3165_, 2, v___x_3158_);
v___x_3166_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3150_, v___x_3165_);
return v___x_3166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3172_, lean_object* v_cmdState_3173_, lean_object* v_a_3174_, lean_object* v_toSnapshot_3175_, lean_object* v_newStx_3176_, lean_object* v_oldCmd_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3172_, v_cmdState_3173_, v_a_3174_, v_toSnapshot_3175_, v_newStx_3176_, v_oldCmd_3177_);
lean_dec_ref(v_a_3174_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3180_, lean_object* v_a_3181_, lean_object* v_newStx_3182_, lean_object* v___x_3183_, lean_object* v_oldProcessed_3184_){
_start:
{
lean_object* v_result_x3f_3186_; 
v_result_x3f_3186_ = lean_ctor_get(v_oldProcessed_3184_, 2);
if (lean_obj_tag(v_result_x3f_3186_) == 1)
{
lean_object* v_val_3187_; lean_object* v_firstCmdSnap_3188_; lean_object* v_toSnapshot_3189_; lean_object* v_cmdState_3190_; lean_object* v_stx_x3f_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; 
v_val_3187_ = lean_ctor_get(v_result_x3f_3186_, 0);
lean_inc(v_val_3187_);
v_firstCmdSnap_3188_ = lean_ctor_get(v_val_3187_, 1);
lean_inc_ref(v_firstCmdSnap_3188_);
v_toSnapshot_3189_ = lean_ctor_get(v_oldProcessed_3184_, 0);
lean_inc_ref(v_toSnapshot_3189_);
lean_dec_ref(v_oldProcessed_3184_);
v_cmdState_3190_ = lean_ctor_get(v_val_3187_, 0);
lean_inc_ref(v_cmdState_3190_);
lean_dec(v_val_3187_);
v_stx_x3f_3191_ = lean_ctor_get(v_firstCmdSnap_3188_, 0);
lean_inc(v_stx_x3f_3191_);
lean_inc_ref(v_a_3181_);
v___f_3192_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3192_, 0, v_newParserState_3180_);
lean_closure_set(v___f_3192_, 1, v_cmdState_3190_);
lean_closure_set(v___f_3192_, 2, v_a_3181_);
lean_closure_set(v___f_3192_, 3, v_toSnapshot_3189_);
lean_closure_set(v___f_3192_, 4, v_newStx_3182_);
v___x_3193_ = lean_box(0);
v___x_3194_ = 1;
v___x_3195_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3188_, v___f_3192_, v_stx_x3f_3191_, v___x_3183_, v___x_3193_, v___x_3194_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec(v___x_3183_);
lean_dec_ref(v_newParserState_3180_);
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_newStx_3182_);
v___x_3197_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3196_, v_oldProcessed_3184_);
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3198_, lean_object* v_a_3199_, lean_object* v_newStx_3200_, lean_object* v___x_3201_, lean_object* v_oldProcessed_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3198_, v_a_3199_, v_newStx_3200_, v___x_3201_, v_oldProcessed_3202_);
lean_dec_ref(v_a_3199_);
return v_res_3204_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3205_ = 0;
v___x_3206_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3207_ = lean_box(0);
v___x_3208_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3209_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v___x_3208_);
lean_ctor_set(v___x_3210_, 2, v___x_3207_);
lean_ctor_set(v___x_3210_, 3, v___x_3206_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*4, v___x_3205_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3211_, lean_object* v_a_3212_, lean_object* v_old_3213_, lean_object* v_newStx_3214_, lean_object* v_newParserState_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_result_x3f_3218_; 
v_result_x3f_3218_ = lean_ctor_get(v_old_3213_, 4);
lean_inc(v_result_x3f_3218_);
if (lean_obj_tag(v_result_x3f_3218_) == 1)
{
lean_object* v_val_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3273_; 
v_val_3219_ = lean_ctor_get(v_result_x3f_3218_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_result_x3f_3218_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3221_ = v_result_x3f_3218_;
v_isShared_3222_ = v_isSharedCheck_3273_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_val_3219_);
lean_dec(v_result_x3f_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3273_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_processedSnap_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3271_; 
v_processedSnap_3223_ = lean_ctor_get(v_val_3219_, 1);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_val_3219_);
if (v_isSharedCheck_3271_ == 0)
{
lean_object* v_unused_3272_; 
v_unused_3272_ = lean_ctor_get(v_val_3219_, 0);
lean_dec(v_unused_3272_);
v___x_3225_ = v_val_3219_;
v_isShared_3226_ = v_isSharedCheck_3271_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_processedSnap_3223_);
lean_dec(v_val_3219_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3271_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_toSnapshot_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3266_; 
v_toSnapshot_3227_ = lean_ctor_get(v_old_3213_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_old_3213_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; lean_object* v_unused_3268_; lean_object* v_unused_3269_; lean_object* v_unused_3270_; 
v_unused_3267_ = lean_ctor_get(v_old_3213_, 4);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_old_3213_, 3);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_old_3213_, 2);
lean_dec(v_unused_3269_);
v_unused_3270_ = lean_ctor_get(v_old_3213_, 1);
lean_dec(v_unused_3270_);
v___x_3229_ = v_old_3213_;
v_isShared_3230_ = v_isSharedCheck_3266_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_toSnapshot_3227_);
lean_dec(v_old_3213_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3266_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_pos_3231_; lean_object* v_endPos_3232_; lean_object* v_stx_x3f_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v_diagnostics_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3262_; 
v_pos_3231_ = lean_ctor_get(v_newParserState_3215_, 0);
v_endPos_3232_ = lean_ctor_get(v_toProcessingContext_3211_, 3);
v_stx_x3f_3233_ = lean_ctor_get(v_processedSnap_3223_, 0);
lean_inc(v_stx_x3f_3233_);
lean_inc(v_endPos_3232_);
lean_inc(v_pos_3231_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_pos_3231_);
lean_ctor_set(v___x_3234_, 1, v_endPos_3232_);
v___x_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
lean_inc_ref(v___x_3235_);
lean_inc(v_newStx_3214_);
lean_inc_ref(v_a_3212_);
lean_inc_ref(v_newParserState_3215_);
v___f_3236_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3236_, 0, v_newParserState_3215_);
lean_closure_set(v___f_3236_, 1, v_a_3212_);
lean_closure_set(v___f_3236_, 2, v_newStx_3214_);
lean_closure_set(v___f_3236_, 3, v___x_3235_);
v___x_3237_ = lean_box(0);
v___x_3238_ = 1;
v___x_3239_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3223_, v___f_3236_, v_stx_x3f_3233_, v___x_3235_, v___x_3237_, v___x_3238_);
v_diagnostics_3240_ = lean_ctor_get(v_toSnapshot_3227_, 1);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_toSnapshot_3227_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; lean_object* v_unused_3264_; lean_object* v_unused_3265_; 
v_unused_3263_ = lean_ctor_get(v_toSnapshot_3227_, 3);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_toSnapshot_3227_, 2);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_toSnapshot_3227_, 0);
lean_dec(v_unused_3265_);
v___x_3242_ = v_toSnapshot_3227_;
v_isShared_3243_ = v_isSharedCheck_3262_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_diagnostics_3240_);
lean_dec(v_toSnapshot_3227_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3262_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3244_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3245_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 1, v___x_3239_);
lean_ctor_set(v___x_3225_, 0, v_newParserState_3215_);
v___x_3247_ = v___x_3225_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_newParserState_3215_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v___x_3239_);
v___x_3247_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3249_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3247_);
v___x_3249_ = v___x_3221_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
uint8_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3250_ = 0;
v___x_3251_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3214_);
v___x_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3252_, 0, v_newStx_3214_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 3, v___x_3245_);
lean_ctor_set(v___x_3242_, 2, v___x_3237_);
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3254_ = v___x_3242_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_diagnostics_3240_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3259_, 3, v___x_3245_);
v___x_3254_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*4, v___x_3250_);
v___x_3255_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3252_, v___x_3254_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3249_);
lean_ctor_set(v___x_3229_, 3, v_newStx_3214_);
lean_ctor_set(v___x_3229_, 2, v_toProcessingContext_3211_);
lean_ctor_set(v___x_3229_, 1, v___x_3255_);
lean_ctor_set(v___x_3229_, 0, v___x_3251_);
v___x_3257_ = v___x_3229_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_toProcessingContext_3211_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v_newStx_3214_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v___x_3249_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
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
lean_dec(v_result_x3f_3218_);
lean_dec_ref(v_newParserState_3215_);
lean_dec(v_newStx_3214_);
lean_dec_ref(v_toProcessingContext_3211_);
return v_old_3213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3274_, lean_object* v_a_3275_, lean_object* v_old_3276_, lean_object* v_newStx_3277_, lean_object* v_newParserState_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3274_, v_a_3275_, v_old_3276_, v_newStx_3277_, v_newParserState_3278_, v___y_3279_);
lean_dec_ref(v___y_3279_);
lean_dec_ref(v_a_3275_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3282_, lean_object* v_setupImports_3283_, lean_object* v_old_x3f_3284_, lean_object* v___x_3285_, lean_object* v___f_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
lean_inc_ref(v_toProcessingContext_3282_);
v___x_3289_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3282_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3358_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3358_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3358_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_snd_3294_; lean_object* v_fst_3295_; lean_object* v_fst_3296_; lean_object* v_snd_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3357_; 
v_snd_3294_ = lean_ctor_get(v_a_3290_, 1);
lean_inc(v_snd_3294_);
v_fst_3295_ = lean_ctor_get(v_a_3290_, 0);
lean_inc(v_fst_3295_);
lean_dec(v_a_3290_);
v_fst_3296_ = lean_ctor_get(v_snd_3294_, 0);
v_snd_3297_ = lean_ctor_get(v_snd_3294_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_snd_3294_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3299_ = v_snd_3294_;
v_isShared_3300_ = v_isSharedCheck_3357_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_snd_3297_);
lean_inc(v_fst_3296_);
lean_dec(v_snd_3294_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3357_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
uint8_t v___x_3301_; 
v___x_3301_ = l_Lean_MessageLog_hasErrors(v_snd_3297_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; lean_object* v___y_3304_; 
lean_inc(v_fst_3295_);
v___x_3302_ = l_Lean_Syntax_unsetTrailing(v_fst_3295_);
if (lean_obj_tag(v_old_x3f_3284_) == 1)
{
lean_object* v_val_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3340_; 
v_val_3325_ = lean_ctor_get(v_old_x3f_3284_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_old_x3f_3284_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3327_ = v_old_x3f_3284_;
v_isShared_3328_ = v_isSharedCheck_3340_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_val_3325_);
lean_dec(v_old_x3f_3284_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3340_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_stx_3329_; lean_object* v_result_x3f_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v_stx_3329_ = lean_ctor_get(v_val_3325_, 3);
v_result_x3f_3330_ = lean_ctor_get(v_val_3325_, 4);
lean_inc(v_stx_3329_);
v___x_3331_ = l_Lean_Syntax_unsetTrailing(v_stx_3329_);
lean_inc(v___x_3302_);
v___x_3332_ = l_Lean_Syntax_eqWithInfo(v___x_3302_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_inc(v_result_x3f_3330_);
lean_del_object(v___x_3327_);
lean_dec(v_val_3325_);
lean_dec_ref(v___f_3286_);
if (lean_obj_tag(v_result_x3f_3330_) == 0)
{
lean_dec_ref(v___x_3285_);
v___y_3304_ = v___y_3287_;
goto v___jp_3303_;
}
else
{
lean_object* v_val_3333_; lean_object* v_processedSnap_3334_; lean_object* v___x_3335_; 
v_val_3333_ = lean_ctor_get(v_result_x3f_3330_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v_result_x3f_3330_, 1);
v_processedSnap_3334_ = lean_ctor_get(v_val_3333_, 1);
lean_inc_ref(v_processedSnap_3334_);
lean_dec(v_val_3333_);
v___x_3335_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3285_, v_processedSnap_3334_);
v___y_3304_ = v___y_3287_;
goto v___jp_3303_;
}
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3338_; 
lean_dec(v___x_3302_);
lean_del_object(v___x_3299_);
lean_dec(v_snd_3297_);
lean_del_object(v___x_3292_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_setupImports_3283_);
lean_dec_ref(v_toProcessingContext_3282_);
lean_inc_ref(v___y_3287_);
v___x_3336_ = lean_apply_5(v___f_3286_, v_val_3325_, v_fst_3295_, v_fst_3296_, v___y_3287_, lean_box(0));
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3336_);
v___x_3338_ = v___x_3327_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_dec_ref(v___f_3286_);
lean_dec_ref(v___x_3285_);
lean_dec(v_old_x3f_3284_);
v___y_3304_ = v___y_3287_;
goto v___jp_3303_;
}
v___jp_3303_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3305_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3297_);
lean_inc(v_fst_3296_);
lean_inc(v_fst_3295_);
v___x_3306_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3283_, v___x_3302_, v_fst_3295_, v_fst_3296_, v___y_3304_);
v___x_3307_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3308_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_unsigned_to_nat(32u);
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_3310_);
lean_dec_ref(v___x_3311_);
v___x_3312_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 1, v___x_3306_);
v___x_3314_ = v___x_3299_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_fst_3296_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3306_);
v___x_3314_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3316_, 0, v___x_3307_);
lean_ctor_set(v___x_3316_, 1, v___x_3308_);
lean_ctor_set(v___x_3316_, 2, v___x_3309_);
lean_ctor_set(v___x_3316_, 3, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*4, v___x_3301_);
lean_inc(v_fst_3295_);
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v_fst_3295_);
v___x_3318_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3318_, 0, v___x_3307_);
lean_ctor_set(v___x_3318_, 1, v___x_3305_);
lean_ctor_set(v___x_3318_, 2, v___x_3309_);
lean_ctor_set(v___x_3318_, 3, v___x_3312_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*4, v___x_3301_);
v___x_3319_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3317_, v___x_3318_);
v___x_3320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3316_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
lean_ctor_set(v___x_3320_, 2, v_toProcessingContext_3282_);
lean_ctor_set(v___x_3320_, 3, v_fst_3295_);
lean_ctor_set(v___x_3320_, 4, v___x_3315_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3320_);
v___x_3322_ = v___x_3292_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
lean_del_object(v___x_3299_);
lean_dec(v_fst_3296_);
lean_dec_ref(v___f_3286_);
lean_dec_ref(v___x_3285_);
lean_dec(v_old_x3f_3284_);
lean_dec_ref(v_setupImports_3283_);
v___x_3341_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3297_);
v___x_3342_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3343_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_unsigned_to_nat(32u);
v___x_3346_ = lean_mk_empty_array_with_capacity(v___x_3345_);
lean_dec_ref(v___x_3346_);
v___x_3347_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3348_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3348_, 0, v___x_3342_);
lean_ctor_set(v___x_3348_, 1, v___x_3343_);
lean_ctor_set(v___x_3348_, 2, v___x_3344_);
lean_ctor_set(v___x_3348_, 3, v___x_3347_);
lean_ctor_set_uint8(v___x_3348_, sizeof(void*)*4, v___x_3301_);
lean_inc(v_fst_3295_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_fst_3295_);
v___x_3350_ = 0;
v___x_3351_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3351_, 0, v___x_3342_);
lean_ctor_set(v___x_3351_, 1, v___x_3341_);
lean_ctor_set(v___x_3351_, 2, v___x_3344_);
lean_ctor_set(v___x_3351_, 3, v___x_3347_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*4, v___x_3350_);
v___x_3352_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3349_, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3348_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
lean_ctor_set(v___x_3353_, 2, v_toProcessingContext_3282_);
lean_ctor_set(v___x_3353_, 3, v_fst_3295_);
lean_ctor_set(v___x_3353_, 4, v___x_3344_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3353_);
v___x_3355_ = v___x_3292_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v___f_3286_);
lean_dec_ref(v___x_3285_);
lean_dec(v_old_x3f_3284_);
lean_dec_ref(v_setupImports_3283_);
lean_dec_ref(v_toProcessingContext_3282_);
v_a_3359_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3289_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3289_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3367_, lean_object* v_setupImports_3368_, lean_object* v_old_x3f_3369_, lean_object* v___x_3370_, lean_object* v___f_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3367_, v_setupImports_3368_, v_old_x3f_3369_, v___x_3370_, v___f_3371_, v___y_3372_);
lean_dec_ref(v___y_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3375_, lean_object* v_toProcessingContext_3376_, lean_object* v_x_3377_){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3378_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3375_);
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3381_, 0, v_x_3377_);
lean_ctor_set(v___x_3381_, 1, v___x_3378_);
lean_ctor_set(v___x_3381_, 2, v_toProcessingContext_3376_);
lean_ctor_set(v___x_3381_, 3, v___x_3379_);
lean_ctor_set(v___x_3381_, 4, v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3382_, lean_object* v_old_x3f_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_toProcessingContext_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___f_3391_; 
v_toProcessingContext_3386_ = lean_ctor_get(v_a_3384_, 0);
v___x_3387_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3388_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3384_);
lean_inc_ref_n(v_toProcessingContext_3386_, 3);
v___f_3389_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3389_, 0, v_toProcessingContext_3386_);
lean_closure_set(v___f_3389_, 1, v_a_3384_);
lean_inc(v_old_x3f_3383_);
v___f_3390_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3390_, 0, v_toProcessingContext_3386_);
lean_closure_set(v___f_3390_, 1, v_setupImports_3382_);
lean_closure_set(v___f_3390_, 2, v_old_x3f_3383_);
lean_closure_set(v___f_3390_, 3, v___x_3388_);
lean_closure_set(v___f_3390_, 4, v___f_3389_);
v___f_3391_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3391_, 0, v___x_3387_);
lean_closure_set(v___f_3391_, 1, v_toProcessingContext_3386_);
if (lean_obj_tag(v_old_x3f_3383_) == 1)
{
lean_object* v_val_3392_; lean_object* v_result_x3f_3393_; 
v_val_3392_ = lean_ctor_get(v_old_x3f_3383_, 0);
lean_inc(v_val_3392_);
lean_dec_ref_known(v_old_x3f_3383_, 1);
v_result_x3f_3393_ = lean_ctor_get(v_val_3392_, 4);
if (lean_obj_tag(v_result_x3f_3393_) == 1)
{
lean_object* v_stx_3394_; lean_object* v_val_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_stx_3394_ = lean_ctor_get(v_val_3392_, 3);
lean_inc(v_stx_3394_);
v_val_3395_ = lean_ctor_get(v_result_x3f_3393_, 0);
lean_inc(v_val_3392_);
v___x_3396_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3392_);
v___x_3397_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3396_);
if (lean_obj_tag(v___x_3397_) == 1)
{
lean_object* v_val_3398_; 
v_val_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v___x_3397_, 1);
if (lean_obj_tag(v_val_3398_) == 1)
{
lean_object* v_val_3399_; lean_object* v_firstCmdSnap_3400_; lean_object* v___x_3401_; 
v_val_3399_ = lean_ctor_get(v_val_3398_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v_val_3398_, 1);
v_firstCmdSnap_3400_ = lean_ctor_get(v_val_3399_, 1);
lean_inc_ref(v_firstCmdSnap_3400_);
lean_dec(v_val_3399_);
v___x_3401_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3400_);
if (lean_obj_tag(v___x_3401_) == 1)
{
lean_object* v_val_3402_; lean_object* v_nextCmdSnap_x3f_3403_; 
v_val_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v_nextCmdSnap_x3f_3403_ = lean_ctor_get(v_val_3402_, 4);
lean_inc(v_nextCmdSnap_x3f_3403_);
lean_dec(v_val_3402_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3403_) == 0)
{
lean_object* v___x_3404_; 
lean_dec(v_stx_3394_);
lean_dec(v_val_3392_);
v___x_3404_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3404_;
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3406_; 
v_val_3405_ = lean_ctor_get(v_nextCmdSnap_x3f_3403_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3403_, 1);
v___x_3406_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3405_);
if (lean_obj_tag(v___x_3406_) == 1)
{
lean_object* v_val_3407_; lean_object* v_parserState_3408_; lean_object* v_pos_3409_; uint8_t v___x_3410_; 
v_val_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v_parserState_3408_ = lean_ctor_get(v_val_3407_, 2);
lean_inc_ref(v_parserState_3408_);
lean_dec(v_val_3407_);
v_pos_3409_ = lean_ctor_get(v_parserState_3408_, 0);
lean_inc(v_pos_3409_);
lean_dec_ref(v_parserState_3408_);
v___x_3410_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3409_, v_a_3384_);
lean_dec(v_pos_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_dec(v_stx_3394_);
lean_dec(v_val_3392_);
v___x_3411_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3411_;
}
else
{
lean_object* v_parserState_3412_; lean_object* v___x_3413_; 
lean_dec_ref(v___f_3391_);
lean_dec_ref(v___f_3390_);
v_parserState_3412_ = lean_ctor_get(v_val_3395_, 0);
lean_inc_ref(v_parserState_3412_);
lean_inc_ref(v_toProcessingContext_3386_);
v___x_3413_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3386_, v_a_3384_, v_val_3392_, v_stx_3394_, v_parserState_3412_, v_a_3384_);
return v___x_3413_;
}
}
else
{
lean_object* v___x_3414_; 
lean_dec(v___x_3406_);
lean_dec(v_stx_3394_);
lean_dec(v_val_3392_);
v___x_3414_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3414_;
}
}
}
else
{
lean_object* v___x_3415_; 
lean_dec(v___x_3401_);
lean_dec(v_stx_3394_);
lean_dec(v_val_3392_);
v___x_3415_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3415_;
}
}
else
{
lean_object* v___x_3416_; 
lean_dec(v_val_3398_);
lean_dec(v_stx_3394_);
lean_dec(v_val_3392_);
v___x_3416_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3416_;
}
}
else
{
lean_object* v___x_3417_; 
lean_dec(v___x_3397_);
lean_dec(v_stx_3394_);
lean_dec(v_val_3392_);
v___x_3417_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3417_;
}
}
else
{
lean_object* v___x_3418_; 
lean_dec(v_val_3392_);
v___x_3418_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3418_;
}
}
else
{
lean_object* v___x_3419_; 
lean_dec(v_old_x3f_3383_);
v___x_3419_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3391_, v___f_3390_, v_a_3384_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3420_, lean_object* v_old_x3f_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3420_, v_old_x3f_3421_, v_a_3422_);
lean_dec_ref(v_a_3422_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3425_, lean_object* v_old_x3f_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; 
lean_inc(v_old_x3f_3426_);
v___x_3429_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3429_, 0, v_setupImports_3425_);
lean_closure_set(v___x_3429_, 1, v_old_x3f_3426_);
if (lean_obj_tag(v_old_x3f_3426_) == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_box(0);
v___x_3431_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3429_, v___x_3430_, v_a_3427_);
return v___x_3431_;
}
else
{
lean_object* v_val_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3441_; 
v_val_3432_ = lean_ctor_get(v_old_x3f_3426_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_old_x3f_3426_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3434_ = v_old_x3f_3426_;
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_val_3432_);
lean_dec(v_old_x3f_3426_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v_ictx_3436_; lean_object* v___x_3438_; 
v_ictx_3436_ = lean_ctor_get(v_val_3432_, 2);
lean_inc_ref(v_ictx_3436_);
lean_dec(v_val_3432_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_ictx_3436_);
v___x_3438_ = v___x_3434_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_ictx_3436_);
v___x_3438_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3429_, v___x_3438_, v_a_3427_);
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3442_, lean_object* v_old_x3f_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Language_Lean_process(v_setupImports_3442_, v_old_x3f_3443_, v_a_3444_);
lean_dec_ref(v_a_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3447_, lean_object* v_parserState_3448_, lean_object* v_commandState_3449_, lean_object* v_old_x3f_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3460_; 
v___x_3452_ = lean_io_promise_new();
v___x_3453_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3450_) == 0)
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_box(0);
v___y_3460_ = v___x_3475_;
goto v___jp_3459_;
}
else
{
lean_object* v_val_3476_; lean_object* v_snd_3477_; lean_object* v___x_3478_; 
v_val_3476_ = lean_ctor_get(v_old_x3f_3450_, 0);
v_snd_3477_ = lean_ctor_get(v_val_3476_, 1);
lean_inc(v_snd_3477_);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_snd_3477_);
v___y_3460_ = v___x_3478_;
goto v___jp_3459_;
}
v___jp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3455_, v___y_3456_, v_inputCtx_3447_);
lean_dec(v___x_3457_);
v___x_3458_ = l_IO_Promise_result_x21___redArg(v___x_3452_);
lean_dec(v___x_3452_);
return v___x_3458_;
}
v___jp_3459_:
{
uint8_t v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3461_ = 1;
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_box(v___x_3461_);
lean_inc(v___x_3452_);
v___x_3464_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3464_, 0, v___y_3460_);
lean_closure_set(v___x_3464_, 1, v_parserState_3448_);
lean_closure_set(v___x_3464_, 2, v_commandState_3449_);
lean_closure_set(v___x_3464_, 3, v___x_3452_);
lean_closure_set(v___x_3464_, 4, v___x_3463_);
lean_closure_set(v___x_3464_, 5, v___x_3453_);
lean_closure_set(v___x_3464_, 6, v___x_3462_);
if (lean_obj_tag(v_old_x3f_3450_) == 0)
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_box(0);
v___y_3455_ = v___x_3464_;
v___y_3456_ = v___x_3465_;
goto v___jp_3454_;
}
else
{
lean_object* v_val_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3474_; 
v_val_3466_ = lean_ctor_get(v_old_x3f_3450_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_old_x3f_3450_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3468_ = v_old_x3f_3450_;
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_val_3466_);
lean_dec(v_old_x3f_3450_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v_fst_3470_; lean_object* v___x_3472_; 
v_fst_3470_ = lean_ctor_get(v_val_3466_, 0);
lean_inc(v_fst_3470_);
lean_dec(v_val_3466_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v_fst_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_fst_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
v___y_3455_ = v___x_3464_;
v___y_3456_ = v___x_3472_;
goto v___jp_3454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3479_, lean_object* v_parserState_3480_, lean_object* v_commandState_3481_, lean_object* v_old_x3f_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3479_, v_parserState_3480_, v_commandState_3481_, v_old_x3f_3482_);
lean_dec_ref(v_inputCtx_3479_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3485_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3486_; 
v_nextCmdSnap_x3f_3486_ = lean_ctor_get(v_snap_3485_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3486_) == 1)
{
lean_object* v_val_3487_; lean_object* v___x_3488_; 
lean_inc_ref(v_nextCmdSnap_x3f_3486_);
lean_dec_ref(v_snap_3485_);
v_val_3487_ = lean_ctor_get(v_nextCmdSnap_x3f_3486_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3486_, 1);
v___x_3488_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3487_);
v_snap_3485_ = v___x_3488_;
goto _start;
}
else
{
lean_object* v_elabSnap_3490_; lean_object* v_resultSnap_3491_; lean_object* v___x_3492_; lean_object* v_cmdState_3493_; lean_object* v___x_3494_; 
v_elabSnap_3490_ = lean_ctor_get(v_snap_3485_, 3);
lean_inc_ref(v_elabSnap_3490_);
lean_dec_ref(v_snap_3485_);
v_resultSnap_3491_ = lean_ctor_get(v_elabSnap_3490_, 2);
lean_inc_ref(v_resultSnap_3491_);
lean_dec_ref(v_elabSnap_3490_);
v___x_3492_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3491_);
v_cmdState_3493_ = lean_ctor_get(v___x_3492_, 1);
lean_inc_ref(v_cmdState_3493_);
lean_dec(v___x_3492_);
v___x_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3494_, 0, v_cmdState_3493_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3495_){
_start:
{
lean_object* v_result_x3f_3496_; 
v_result_x3f_3496_ = lean_ctor_get(v_snap_3495_, 4);
lean_inc(v_result_x3f_3496_);
lean_dec_ref(v_snap_3495_);
if (lean_obj_tag(v_result_x3f_3496_) == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_box(0);
return v___x_3497_;
}
else
{
lean_object* v_val_3498_; lean_object* v_processedSnap_3499_; lean_object* v___x_3500_; lean_object* v_result_x3f_3501_; 
v_val_3498_ = lean_ctor_get(v_result_x3f_3496_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_result_x3f_3496_, 1);
v_processedSnap_3499_ = lean_ctor_get(v_val_3498_, 1);
lean_inc_ref(v_processedSnap_3499_);
lean_dec(v_val_3498_);
v___x_3500_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3499_);
v_result_x3f_3501_ = lean_ctor_get(v___x_3500_, 2);
lean_inc(v_result_x3f_3501_);
lean_dec(v___x_3500_);
if (lean_obj_tag(v_result_x3f_3501_) == 0)
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_box(0);
return v___x_3502_;
}
else
{
lean_object* v_val_3503_; lean_object* v_firstCmdSnap_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_val_3503_ = lean_ctor_get(v_result_x3f_3501_, 0);
lean_inc(v_val_3503_);
lean_dec_ref_known(v_result_x3f_3501_, 1);
v_firstCmdSnap_3504_ = lean_ctor_get(v_val_3503_, 1);
lean_inc_ref(v_firstCmdSnap_3504_);
lean_dec(v_val_3503_);
v___x_3505_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3504_);
v___x_3506_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3505_);
return v___x_3506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3507_, lean_object* v_snap_3508_, lean_object* v_acc_3509_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3510_; lean_object* v_acc_3511_; 
v_nextCmdSnap_x3f_3510_ = lean_ctor_get(v_snap_3508_, 4);
lean_inc(v_nextCmdSnap_x3f_3510_);
lean_inc(v_f_3507_);
v_acc_3511_ = lean_apply_2(v_f_3507_, v_acc_3509_, v_snap_3508_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3510_) == 1)
{
lean_object* v_val_3512_; lean_object* v___x_3513_; 
v_val_3512_ = lean_ctor_get(v_nextCmdSnap_x3f_3510_, 0);
lean_inc(v_val_3512_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3510_, 1);
v___x_3513_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3512_);
v_snap_3508_ = v___x_3513_;
v_acc_3509_ = v_acc_3511_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3510_);
lean_dec(v_f_3507_);
return v_acc_3511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3515_, lean_object* v_f_3516_, lean_object* v_snap_3517_, lean_object* v_acc_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3516_, v_snap_3517_, v_acc_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3520_, lean_object* v_init_3521_, lean_object* v_f_3522_){
_start:
{
lean_object* v_result_x3f_3523_; 
v_result_x3f_3523_ = lean_ctor_get(v_snap_3520_, 4);
lean_inc(v_result_x3f_3523_);
lean_dec_ref(v_snap_3520_);
if (lean_obj_tag(v_result_x3f_3523_) == 0)
{
lean_object* v___x_3524_; 
lean_dec(v_f_3522_);
lean_dec(v_init_3521_);
v___x_3524_ = lean_box(0);
return v___x_3524_;
}
else
{
lean_object* v_val_3525_; lean_object* v_processedSnap_3526_; lean_object* v___x_3527_; lean_object* v_result_x3f_3528_; 
v_val_3525_ = lean_ctor_get(v_result_x3f_3523_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v_result_x3f_3523_, 1);
v_processedSnap_3526_ = lean_ctor_get(v_val_3525_, 1);
lean_inc_ref(v_processedSnap_3526_);
lean_dec(v_val_3525_);
v___x_3527_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3526_);
v_result_x3f_3528_ = lean_ctor_get(v___x_3527_, 2);
lean_inc(v_result_x3f_3528_);
lean_dec(v___x_3527_);
if (lean_obj_tag(v_result_x3f_3528_) == 0)
{
lean_object* v___x_3529_; 
lean_dec(v_f_3522_);
lean_dec(v_init_3521_);
v___x_3529_ = lean_box(0);
return v___x_3529_;
}
else
{
lean_object* v_val_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3540_; 
v_val_3530_ = lean_ctor_get(v_result_x3f_3528_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_result_x3f_3528_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3532_ = v_result_x3f_3528_;
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_val_3530_);
lean_dec(v_result_x3f_3528_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3540_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_firstCmdSnap_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_firstCmdSnap_3534_ = lean_ctor_get(v_val_3530_, 1);
lean_inc_ref(v_firstCmdSnap_3534_);
lean_dec(v_val_3530_);
v___x_3535_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3534_);
v___x_3536_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3522_, v___x_3535_, v_init_3521_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3536_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3541_, lean_object* v_snap_3542_, lean_object* v_init_3543_, lean_object* v_f_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3542_, v_init_3543_, v_f_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = 1;
v___x_3552_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3553_ = l_Lean_Name_toString(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3554_ = 0;
v___x_3555_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3556_ = lean_box(0);
v___x_3557_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3558_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3559_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
lean_ctor_set(v___x_3559_, 1, v___x_3557_);
lean_ctor_set(v___x_3559_, 2, v___x_3556_);
lean_ctor_set(v___x_3559_, 3, v___x_3555_);
lean_ctor_set_uint8(v___x_3559_, sizeof(void*)*4, v___x_3554_);
return v___x_3559_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3561_ = lean_box(0);
v___x_3562_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3563_){
_start:
{
lean_object* v_result_x3f_3564_; 
v_result_x3f_3564_ = lean_ctor_get(v_snap_3563_, 4);
lean_inc(v_result_x3f_3564_);
if (lean_obj_tag(v_result_x3f_3564_) == 1)
{
lean_object* v_val_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3640_; 
v_val_3565_ = lean_ctor_get(v_result_x3f_3564_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_result_x3f_3564_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3567_ = v_result_x3f_3564_;
v_isShared_3568_ = v_isSharedCheck_3640_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_val_3565_);
lean_dec(v_result_x3f_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3640_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v_toSnapshot_3569_; lean_object* v_metaSnap_3570_; lean_object* v_ictx_3571_; lean_object* v_stx_3572_; lean_object* v_parserState_3573_; lean_object* v_processedSnap_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3639_; 
v_toSnapshot_3569_ = lean_ctor_get(v_snap_3563_, 0);
v_metaSnap_3570_ = lean_ctor_get(v_snap_3563_, 1);
v_ictx_3571_ = lean_ctor_get(v_snap_3563_, 2);
v_stx_3572_ = lean_ctor_get(v_snap_3563_, 3);
v_parserState_3573_ = lean_ctor_get(v_val_3565_, 0);
v_processedSnap_3574_ = lean_ctor_get(v_val_3565_, 1);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_val_3565_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3576_ = v_val_3565_;
v_isShared_3577_ = v_isSharedCheck_3639_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_processedSnap_3574_);
lean_inc(v_parserState_3573_);
lean_dec(v_val_3565_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3639_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_processed_3578_; lean_object* v_result_x3f_3579_; 
v_processed_3578_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3574_);
v_result_x3f_3579_ = lean_ctor_get(v_processed_3578_, 2);
lean_inc(v_result_x3f_3579_);
if (lean_obj_tag(v_result_x3f_3579_) == 1)
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3633_; 
lean_inc(v_stx_3572_);
lean_inc_ref(v_ictx_3571_);
lean_inc_ref(v_metaSnap_3570_);
lean_inc_ref(v_toSnapshot_3569_);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_snap_3563_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; lean_object* v_unused_3635_; lean_object* v_unused_3636_; lean_object* v_unused_3637_; lean_object* v_unused_3638_; 
v_unused_3634_ = lean_ctor_get(v_snap_3563_, 4);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_snap_3563_, 3);
lean_dec(v_unused_3635_);
v_unused_3636_ = lean_ctor_get(v_snap_3563_, 2);
lean_dec(v_unused_3636_);
v_unused_3637_ = lean_ctor_get(v_snap_3563_, 1);
lean_dec(v_unused_3637_);
v_unused_3638_ = lean_ctor_get(v_snap_3563_, 0);
lean_dec(v_unused_3638_);
v___x_3581_ = v_snap_3563_;
v_isShared_3582_ = v_isSharedCheck_3633_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_snap_3563_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3633_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_val_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3632_; 
v_val_3583_ = lean_ctor_get(v_result_x3f_3579_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_result_x3f_3579_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3585_ = v_result_x3f_3579_;
v_isShared_3586_ = v_isSharedCheck_3632_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_val_3583_);
lean_dec(v_result_x3f_3579_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3632_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_toSnapshot_3587_; lean_object* v_metaSnap_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3630_; 
v_toSnapshot_3587_ = lean_ctor_get(v_processed_3578_, 0);
v_metaSnap_3588_ = lean_ctor_get(v_processed_3578_, 1);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_processed_3578_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v_processed_3578_, 2);
lean_dec(v_unused_3631_);
v___x_3590_ = v_processed_3578_;
v_isShared_3591_ = v_isSharedCheck_3630_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_metaSnap_3588_);
lean_inc(v_toSnapshot_3587_);
lean_dec(v_processed_3578_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3630_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v_cmdState_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3628_; 
v_cmdState_3592_ = lean_ctor_get(v_val_3583_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_val_3583_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v_val_3583_, 1);
lean_dec(v_unused_3629_);
v___x_3594_ = v_val_3583_;
v_isShared_3595_ = v_isSharedCheck_3628_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_cmdState_3592_);
lean_dec(v_val_3583_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3628_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_resultSnap_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v_elabSnap_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v_termCmd_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3596_ = lean_box(0);
v___x_3597_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3598_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3592_);
v_resultSnap_3599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3599_, 0, v___x_3597_);
lean_ctor_set(v_resultSnap_3599_, 1, v_cmdState_3592_);
lean_ctor_set(v_resultSnap_3599_, 2, v___x_3598_);
v___x_3600_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3601_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3596_, v_resultSnap_3599_);
v___x_3602_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3603_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3604_, 0, v___x_3597_);
lean_ctor_set(v_elabSnap_3604_, 1, v___x_3600_);
lean_ctor_set(v_elabSnap_3604_, 2, v___x_3601_);
lean_ctor_set(v_elabSnap_3604_, 3, v___x_3602_);
lean_ctor_set(v_elabSnap_3604_, 4, v___x_3603_);
v___x_3605_ = lean_box(0);
v___x_3606_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3607_, 0, v___x_3597_);
lean_ctor_set(v_termCmd_3607_, 1, v___x_3605_);
lean_ctor_set(v_termCmd_3607_, 2, v___x_3606_);
lean_ctor_set(v_termCmd_3607_, 3, v_elabSnap_3604_);
lean_ctor_set(v_termCmd_3607_, 4, v___x_3596_);
v___x_3608_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3596_, v_termCmd_3607_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 1, v___x_3608_);
v___x_3610_ = v___x_3594_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_cmdState_3592_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3610_);
v___x_3612_ = v___x_3585_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v_newProcessed_3614_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 2, v___x_3612_);
v_newProcessed_3614_ = v___x_3590_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_toSnapshot_3587_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_metaSnap_3588_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v___x_3612_);
v_newProcessed_3614_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3615_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3596_, v_newProcessed_3614_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3615_);
v___x_3617_ = v___x_3576_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_parserState_3573_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3617_);
v___x_3619_ = v___x_3567_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3621_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v___x_3619_);
v___x_3621_ = v___x_3581_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_toSnapshot_3569_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_metaSnap_3570_);
lean_ctor_set(v_reuseFailAlloc_3622_, 2, v_ictx_3571_);
lean_ctor_set(v_reuseFailAlloc_3622_, 3, v_stx_3572_);
lean_ctor_set(v_reuseFailAlloc_3622_, 4, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
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
lean_dec(v_result_x3f_3579_);
lean_dec(v_processed_3578_);
lean_del_object(v___x_3576_);
lean_dec_ref(v_parserState_3573_);
lean_del_object(v___x_3567_);
return v_snap_3563_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3564_);
return v_snap_3563_;
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

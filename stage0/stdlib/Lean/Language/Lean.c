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
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
lean_ctor_set(v___x_617_, 3, v___x_616_);
lean_ctor_set(v___x_617_, 4, v___x_615_);
lean_ctor_set(v___x_617_, 5, v___x_615_);
lean_ctor_set(v___x_617_, 6, v___x_615_);
lean_ctor_set(v___x_617_, 7, v___x_615_);
lean_ctor_set(v___x_617_, 8, v___x_615_);
lean_ctor_set(v___x_617_, 9, v___x_615_);
lean_ctor_set(v___x_617_, 10, v___x_615_);
lean_ctor_set(v___x_617_, 11, v___x_614_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_unsigned_to_nat(32u);
v___x_619_ = lean_mk_empty_array_with_capacity(v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_621_ = ((size_t)5ULL);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_unsigned_to_nat(32u);
v___x_624_ = lean_mk_empty_array_with_capacity(v___x_623_);
v___x_625_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_626_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_622_);
lean_ctor_set(v___x_626_, 3, v___x_622_);
lean_ctor_set_usize(v___x_626_, 4, v___x_621_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_box(1);
v___x_628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_629_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
lean_ctor_set(v___x_630_, 2, v___x_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v_env_635_; uint8_t v___x_636_; lean_object* v_env_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_scopes_640_; lean_object* v___x_641_; lean_object* v_opts_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_634_ = lean_st_ref_get(v___y_632_);
v_env_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_635_);
lean_dec(v___x_634_);
v___x_636_ = 0;
v_env_637_ = l_Lean_Environment_setRecordingDeps(v_env_635_, v___x_636_);
v___x_638_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_639_ = lean_st_ref_get(v___y_632_);
v_scopes_640_ = lean_ctor_get(v___x_639_, 2);
lean_inc(v_scopes_640_);
lean_dec(v___x_639_);
v___x_641_ = l_List_head_x21___redArg(v___x_638_, v_scopes_640_);
lean_dec(v_scopes_640_);
v_opts_642_ = lean_ctor_get(v___x_641_, 1);
lean_inc_ref(v_opts_642_);
lean_dec(v___x_641_);
v___x_643_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_644_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_645_, 0, v_env_637_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_644_);
lean_ctor_set(v___x_645_, 3, v_opts_642_);
v___x_646_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_msgData_631_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_648_, v___y_649_);
lean_dec(v___y_649_);
return v_res_651_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_653_) == 1)
{
lean_object* v_pre_654_; 
v_pre_654_ = lean_ctor_get(v_x_653_, 0);
if (lean_obj_tag(v_pre_654_) == 0)
{
lean_object* v_str_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_str_655_ = lean_ctor_get(v_x_653_, 1);
v___x_656_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_657_ = lean_string_dec_eq(v_str_655_, v___x_656_);
if (v___x_657_ == 0)
{
return v___x_657_;
}
else
{
return v_suppressElabErrors_652_;
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
else
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_suppressElabErrors_boxed_662_; uint8_t v_res_663_; lean_object* v_r_664_; 
v_suppressElabErrors_boxed_662_ = lean_unbox(v_suppressElabErrors_660_);
v_res_663_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_662_, v_x_661_);
lean_dec(v_x_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_666_, lean_object* v_msgData_667_, uint8_t v_severity_668_, uint8_t v_isSilent_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_739_; uint8_t v___y_740_; uint8_t v___y_741_; lean_object* v___y_742_; uint8_t v___y_765_; uint8_t v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; uint8_t v___y_772_; uint8_t v___y_773_; uint8_t v___x_788_; uint8_t v___y_790_; uint8_t v___x_800_; 
v___x_788_ = 2;
v___x_800_ = l_Lean_instBEqMessageSeverity_beq(v_severity_668_, v___x_788_);
if (v___x_800_ == 0)
{
v___y_790_ = v___x_800_;
goto v___jp_789_;
}
else
{
uint8_t v___x_801_; 
lean_inc_ref(v_msgData_667_);
v___x_801_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_667_);
if (v___x_801_ == 0)
{
v___y_790_ = v___x_801_;
goto v___jp_789_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v_msgData_667_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
v___jp_673_:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Elab_Command_getScope___redArg(v___y_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v_currNamespace_684_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
v_currNamespace_684_ = lean_ctor_get(v_a_683_, 2);
lean_inc(v_currNamespace_684_);
lean_dec(v_a_683_);
v___x_685_ = l_Lean_Elab_Command_getScope___redArg(v___y_681_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_721_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_721_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_721_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_721_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_openDecls_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_env_695_; lean_object* v_messages_696_; lean_object* v_scopes_697_; lean_object* v_usedQuotCtxts_698_; lean_object* v_nextMacroScope_699_; lean_object* v_maxRecDepth_700_; lean_object* v_ngen_701_; lean_object* v_auxDeclNGen_702_; lean_object* v_infoState_703_; lean_object* v_traceState_704_; lean_object* v_snapshotTasks_705_; lean_object* v_prevLinterStates_706_; lean_object* v_codeQualityEntryTasks_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_720_; 
v_openDecls_690_ = lean_ctor_get(v_a_686_, 3);
lean_inc(v_openDecls_690_);
lean_dec(v_a_686_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_currNamespace_684_);
lean_ctor_set(v___x_691_, 1, v_openDecls_690_);
v___x_692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc_ref(v___y_675_);
v___x_693_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_693_, 0, v___y_675_);
lean_ctor_set(v___x_693_, 1, v___y_676_);
lean_ctor_set(v___x_693_, 2, v___y_678_);
lean_ctor_set(v___x_693_, 3, v___y_679_);
lean_ctor_set(v___x_693_, 4, v___x_692_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*5, v___y_674_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*5 + 1, v___y_677_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*5 + 2, v_isSilent_669_);
v___x_694_ = lean_st_ref_take(v___y_681_);
v_env_695_ = lean_ctor_get(v___x_694_, 0);
v_messages_696_ = lean_ctor_get(v___x_694_, 1);
v_scopes_697_ = lean_ctor_get(v___x_694_, 2);
v_usedQuotCtxts_698_ = lean_ctor_get(v___x_694_, 3);
v_nextMacroScope_699_ = lean_ctor_get(v___x_694_, 4);
v_maxRecDepth_700_ = lean_ctor_get(v___x_694_, 5);
v_ngen_701_ = lean_ctor_get(v___x_694_, 6);
v_auxDeclNGen_702_ = lean_ctor_get(v___x_694_, 7);
v_infoState_703_ = lean_ctor_get(v___x_694_, 8);
v_traceState_704_ = lean_ctor_get(v___x_694_, 9);
v_snapshotTasks_705_ = lean_ctor_get(v___x_694_, 10);
v_prevLinterStates_706_ = lean_ctor_get(v___x_694_, 11);
v_codeQualityEntryTasks_707_ = lean_ctor_get(v___x_694_, 12);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_720_ == 0)
{
v___x_709_ = v___x_694_;
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_codeQualityEntryTasks_707_);
lean_inc(v_prevLinterStates_706_);
lean_inc(v_snapshotTasks_705_);
lean_inc(v_traceState_704_);
lean_inc(v_infoState_703_);
lean_inc(v_auxDeclNGen_702_);
lean_inc(v_ngen_701_);
lean_inc(v_maxRecDepth_700_);
lean_inc(v_nextMacroScope_699_);
lean_inc(v_usedQuotCtxts_698_);
lean_inc(v_scopes_697_);
lean_inc(v_messages_696_);
lean_inc(v_env_695_);
lean_dec(v___x_694_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = lean_box(0);
v___x_712_ = l_Lean_MessageLog_add(v___x_693_, v_messages_696_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___x_712_);
v___x_714_ = v___x_709_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_scopes_697_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_usedQuotCtxts_698_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_nextMacroScope_699_);
lean_ctor_set(v_reuseFailAlloc_719_, 5, v_maxRecDepth_700_);
lean_ctor_set(v_reuseFailAlloc_719_, 6, v_ngen_701_);
lean_ctor_set(v_reuseFailAlloc_719_, 7, v_auxDeclNGen_702_);
lean_ctor_set(v_reuseFailAlloc_719_, 8, v_infoState_703_);
lean_ctor_set(v_reuseFailAlloc_719_, 9, v_traceState_704_);
lean_ctor_set(v_reuseFailAlloc_719_, 10, v_snapshotTasks_705_);
lean_ctor_set(v_reuseFailAlloc_719_, 11, v_prevLinterStates_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 12, v_codeQualityEntryTasks_707_);
v___x_714_ = v_reuseFailAlloc_719_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_st_ref_put(v___y_681_, v___x_714_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_711_);
v___x_717_ = v___x_688_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_711_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_currNamespace_684_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_676_);
v_a_722_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_685_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_685_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
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
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___y_680_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_676_);
v_a_730_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_682_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_682_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
v___jp_738_:
{
lean_object* v_fileName_743_; lean_object* v_fileMap_744_; uint8_t v_suppressElabErrors_745_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_763_; 
v_fileName_743_ = lean_ctor_get(v___y_670_, 0);
v_fileMap_744_ = lean_ctor_get(v___y_670_, 1);
v_suppressElabErrors_745_ = lean_ctor_get_uint8(v___y_670_, sizeof(void*)*10);
v___x_746_ = lean_box(v_suppressElabErrors_745_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 2, 1);
lean_closure_set(v___f_747_, 0, v___x_746_);
v___x_748_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_667_);
v___x_749_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_748_, v___y_671_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_763_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_763_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_763_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_inc_ref_n(v_fileMap_744_, 2);
v___x_754_ = l_Lean_FileMap_toPosition(v_fileMap_744_, v___y_739_);
lean_dec(v___y_739_);
v___x_755_ = l_Lean_FileMap_toPosition(v_fileMap_744_, v___y_742_);
lean_dec(v___y_742_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_745_ == 0)
{
lean_del_object(v___x_752_);
lean_dec_ref(v___f_747_);
v___y_674_ = v___y_740_;
v___y_675_ = v_fileName_743_;
v___y_676_ = v___x_754_;
v___y_677_ = v___y_741_;
v___y_678_ = v___x_756_;
v___y_679_ = v___x_757_;
v___y_680_ = v_a_750_;
v___y_681_ = v___y_671_;
goto v___jp_673_;
}
else
{
uint8_t v___x_758_; 
lean_inc(v_a_750_);
v___x_758_ = l_Lean_MessageData_hasTag(v___f_747_, v_a_750_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec_ref_known(v___x_756_, 1);
lean_dec_ref(v___x_754_);
lean_dec(v_a_750_);
v___x_759_ = lean_box(0);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_759_);
v___x_761_ = v___x_752_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_del_object(v___x_752_);
v___y_674_ = v___y_740_;
v___y_675_ = v_fileName_743_;
v___y_676_ = v___x_754_;
v___y_677_ = v___y_741_;
v___y_678_ = v___x_756_;
v___y_679_ = v___x_757_;
v___y_680_ = v_a_750_;
v___y_681_ = v___y_671_;
goto v___jp_673_;
}
}
}
}
v___jp_764_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Syntax_getTailPos_x3f(v___y_767_, v___y_765_);
lean_dec(v___y_767_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_inc(v___y_768_);
v___y_739_ = v___y_768_;
v___y_740_ = v___y_765_;
v___y_741_ = v___y_766_;
v___y_742_ = v___y_768_;
goto v___jp_738_;
}
else
{
lean_object* v_val_770_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_769_, 1);
v___y_739_ = v___y_768_;
v___y_740_ = v___y_765_;
v___y_741_ = v___y_766_;
v___y_742_ = v_val_770_;
goto v___jp_738_;
}
}
v___jp_771_:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Elab_Command_getRef___redArg(v___y_670_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v_ref_776_; lean_object* v___x_777_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v_ref_776_ = l_Lean_replaceRef(v_ref_666_, v_a_775_);
lean_dec(v_a_775_);
v___x_777_ = l_Lean_Syntax_getPos_x3f(v_ref_776_, v___y_772_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___y_765_ = v___y_772_;
v___y_766_ = v___y_773_;
v___y_767_ = v_ref_776_;
v___y_768_ = v___x_778_;
goto v___jp_764_;
}
else
{
lean_object* v_val_779_; 
v_val_779_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v___x_777_, 1);
v___y_765_ = v___y_772_;
v___y_766_ = v___y_773_;
v___y_767_ = v_ref_776_;
v___y_768_ = v_val_779_;
goto v___jp_764_;
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_msgData_667_);
v_a_780_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_774_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_774_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
v___jp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_scopes_793_; lean_object* v___x_794_; lean_object* v_opts_795_; uint8_t v___x_796_; uint8_t v___x_797_; 
v___x_791_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_792_ = lean_st_ref_get(v___y_671_);
v_scopes_793_ = lean_ctor_get(v___x_792_, 2);
lean_inc(v_scopes_793_);
lean_dec(v___x_792_);
v___x_794_ = l_List_head_x21___redArg(v___x_791_, v_scopes_793_);
lean_dec(v_scopes_793_);
v_opts_795_ = lean_ctor_get(v___x_794_, 1);
lean_inc_ref(v_opts_795_);
lean_dec(v___x_794_);
v___x_796_ = 1;
v___x_797_ = l_Lean_instBEqMessageSeverity_beq(v_severity_668_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_opts_795_);
v___y_772_ = v___y_790_;
v___y_773_ = v_severity_668_;
goto v___jp_771_;
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = l_Lean_warningAsError;
v___x_799_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_795_, v___x_798_);
lean_dec_ref(v_opts_795_);
if (v___x_799_ == 0)
{
v___y_772_ = v___y_790_;
v___y_773_ = v_severity_668_;
goto v___jp_771_;
}
else
{
v___y_772_ = v___y_790_;
v___y_773_ = v___x_788_;
goto v___jp_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_804_, lean_object* v_msgData_805_, lean_object* v_severity_806_, lean_object* v_isSilent_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v_severity_boxed_811_; uint8_t v_isSilent_boxed_812_; lean_object* v_res_813_; 
v_severity_boxed_811_ = lean_unbox(v_severity_806_);
v_isSilent_boxed_812_ = lean_unbox(v_isSilent_807_);
v_res_813_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_804_, v_msgData_805_, v_severity_boxed_811_, v_isSilent_boxed_812_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v_ref_804_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_814_, uint8_t v_severity_815_, uint8_t v_isSilent_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Elab_Command_getRef___redArg(v___y_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_821_, v_msgData_814_, v_severity_815_, v_isSilent_816_, v___y_817_, v___y_818_);
lean_dec(v_a_821_);
return v___x_822_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_msgData_814_);
v_a_823_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_820_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_831_, lean_object* v_severity_832_, lean_object* v_isSilent_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v_severity_boxed_837_; uint8_t v_isSilent_boxed_838_; lean_object* v_res_839_; 
v_severity_boxed_837_ = lean_unbox(v_severity_832_);
v_isSilent_boxed_838_ = lean_unbox(v_isSilent_833_);
v_res_839_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_831_, v_severity_boxed_837_, v_isSilent_boxed_838_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
uint8_t v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = 2;
v___x_845_ = 0;
v___x_846_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_840_, v___x_844_, v___x_845_, v___y_841_, v___y_842_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_852_, lean_object* v_msgData_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = 2;
v___x_858_ = 0;
v___x_859_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_852_, v_msgData_853_, v___x_857_, v___x_858_, v___y_854_, v___y_855_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_860_, lean_object* v_msgData_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_860_, v_msgData_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v_ref_860_);
return v_res_865_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
if (lean_obj_tag(v_ex_869_) == 0)
{
lean_object* v_ref_876_; lean_object* v_msg_877_; lean_object* v___x_878_; 
v_ref_876_ = lean_ctor_get(v_ex_869_, 0);
lean_inc(v_ref_876_);
v_msg_877_ = lean_ctor_get(v_ex_869_, 1);
lean_inc_ref(v_msg_877_);
lean_dec_ref_known(v_ex_869_, 2);
v___x_878_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_876_, v_msg_877_, v___y_870_, v___y_871_);
lean_dec(v_ref_876_);
return v___x_878_;
}
else
{
lean_object* v_id_879_; uint8_t v___x_880_; 
v_id_879_ = lean_ctor_get(v_ex_869_, 0);
lean_inc(v_id_879_);
v___x_880_ = l_Lean_Elab_isAbortExceptionId(v_id_879_);
if (v___x_880_ == 0)
{
uint8_t v___x_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_906_; 
v___x_881_ = l_Lean_Exception_isInterrupt(v_ex_869_);
v_isSharedCheck_906_ = !lean_is_exclusive(v_ex_869_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_907_ = lean_ctor_get(v_ex_869_, 1);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_ex_869_, 0);
lean_dec(v_unused_908_);
v___x_883_ = v_ex_869_;
v_isShared_884_ = v_isSharedCheck_906_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_ex_869_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_906_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (v___x_881_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_InternalExceptionId_getName(v_id_879_);
lean_dec(v_id_879_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_del_object(v___x_883_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_888_ = l_Lean_MessageData_ofName(v_a_886_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_889_, v___y_870_, v___y_871_);
return v___x_890_;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_905_; 
v_a_891_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_905_ == 0)
{
v___x_893_ = v___x_885_;
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_885_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_ref_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_ref_895_ = lean_ctor_get(v___y_870_, 7);
v___x_896_ = lean_io_error_to_string(v_a_891_);
v___x_897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
v___x_898_ = l_Lean_MessageData_ofFormat(v___x_897_);
lean_inc(v_ref_895_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
lean_ctor_set(v___x_883_, 1, v___x_898_);
lean_ctor_set(v___x_883_, 0, v_ref_895_);
v___x_900_ = v___x_883_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_ref_895_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_900_);
v___x_902_ = v___x_893_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_del_object(v___x_883_);
lean_dec(v_id_879_);
goto v___jp_873_;
}
}
}
else
{
lean_dec(v_id_879_);
lean_dec_ref_known(v_ex_869_, 2);
goto v___jp_873_;
}
}
v___jp_873_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
v___x_918_ = lean_apply_3(v_x_914_, v___y_915_, v___y_916_, lean_box(0));
if (lean_obj_tag(v___x_918_) == 0)
{
return v___x_918_;
}
else
{
lean_object* v_a_919_; uint8_t v___x_920_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
v___x_920_ = l_Lean_Exception_isInterrupt(v_a_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_dec_ref_known(v___x_918_, 1);
v___x_921_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_919_, v___y_915_, v___y_916_);
return v___x_921_;
}
else
{
lean_dec(v_a_919_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_927_, lean_object* v___x_928_, lean_object* v_val_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_a_933_; lean_object* v___x_935_; 
v___x_935_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_927_, v___x_928_, v_val_929_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v_a_933_ = v_a_936_;
goto v___jp_932_;
}
else
{
lean_object* v___x_937_; 
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = lean_box(0);
v_a_933_ = v___x_937_;
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v_a_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_938_, lean_object* v___x_939_, lean_object* v_val_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_938_, v___x_939_, v_val_940_, v___y_941_);
lean_dec_ref(v___y_941_);
lean_dec(v_val_940_);
lean_dec_ref(v___x_939_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_944_, lean_object* v_x_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_get_set_stderr(v_h_944_);
lean_inc_ref(v___y_946_);
v___x_949_ = lean_apply_2(v_x_945_, v___y_946_, lean_box(0));
v___x_950_ = lean_get_set_stderr(v___x_948_);
lean_dec_ref(v___x_950_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_951_, lean_object* v_x_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_951_, v_x_952_, v___y_953_);
lean_dec_ref(v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_956_, lean_object* v_h_957_, lean_object* v_x_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_957_, v_x_958_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_962_, lean_object* v_h_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_962_, v_h_963_, v_x_964_, v___y_965_);
lean_dec_ref(v___y_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_968_, lean_object* v_x_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_get_set_stdin(v_h_968_);
lean_inc_ref(v___y_970_);
v___x_973_ = lean_apply_2(v_x_969_, v___y_970_, lean_box(0));
v___x_974_ = lean_get_set_stdin(v___x_972_);
lean_dec_ref(v___x_974_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_975_, v_x_976_, v___y_977_);
lean_dec_ref(v___y_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_982_ = lean_panic_fn_borrowed(v___x_981_, v_msg_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_983_, lean_object* v_x_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_get_set_stdout(v_h_983_);
lean_inc_ref(v___y_985_);
v___x_988_ = lean_apply_2(v_x_984_, v___y_985_, lean_box(0));
v___x_989_ = lean_get_set_stdout(v___x_987_);
lean_dec_ref(v___x_989_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_990_, v_x_991_, v___y_992_);
lean_dec_ref(v___y_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_995_, lean_object* v_h_996_, lean_object* v_x_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_996_, v_x_997_, v___y_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_h_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1001_, v_h_1002_, v_x_1003_, v___y_1004_);
lean_dec_ref(v___y_1004_);
return v_res_1006_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = l_ByteArray_empty;
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1014_ = lean_unsigned_to_nat(46u);
v___x_1015_ = lean_unsigned_to_nat(193u);
v___x_1016_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1017_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1018_ = l_mkPanicMessageWithDecl(v___x_1017_, v___x_1016_, v___x_1015_, v___x_1014_, v___x_1013_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1019_, uint8_t v_isolateStderr_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___y_1033_; 
v___x_1027_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1028_ = lean_st_mk_ref(v___x_1027_);
v___x_1029_ = lean_st_mk_ref(v___x_1027_);
v___x_1030_ = l_IO_FS_Stream_ofBuffer(v___x_1028_);
lean_inc(v___x_1029_);
v___x_1031_ = l_IO_FS_Stream_ofBuffer(v___x_1029_);
if (v_isolateStderr_1020_ == 0)
{
v___y_1033_ = v_x_1019_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1042_; 
lean_inc_ref(v___x_1031_);
v___x_1042_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1042_, 0, lean_box(0));
lean_closure_set(v___x_1042_, 1, v___x_1031_);
lean_closure_set(v___x_1042_, 2, v_x_1019_);
v___y_1033_ = v___x_1042_;
goto v___jp_1032_;
}
v___jp_1023_:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___y_1025_);
lean_ctor_set(v___x_1026_, 1, v___y_1024_);
return v___x_1026_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_data_1037_; uint8_t v___x_1038_; 
v___x_1034_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1034_, 0, lean_box(0));
lean_closure_set(v___x_1034_, 1, v___x_1031_);
lean_closure_set(v___x_1034_, 2, v___y_1033_);
v___x_1035_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1030_, v___x_1034_, v___y_1021_);
v___x_1036_ = lean_st_ref_get(v___x_1029_);
lean_dec(v___x_1029_);
v_data_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc_ref(v_data_1037_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_string_validate_utf8(v_data_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref(v_data_1037_);
v___x_1039_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1040_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1039_);
v___y_1024_ = v___x_1035_;
v___y_1025_ = v___x_1040_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_string_from_utf8_unchecked(v_data_1037_);
v___y_1024_ = v___x_1035_;
v___y_1025_ = v___x_1041_;
goto v___jp_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1043_, lean_object* v_isolateStderr_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_isolateStderr_boxed_1047_; lean_object* v_res_1048_; 
v_isolateStderr_boxed_1047_ = lean_unbox(v_isolateStderr_1044_);
v_res_1048_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1043_, v_isolateStderr_boxed_1047_, v___y_1045_);
lean_dec_ref(v___y_1045_);
return v_res_1048_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = 1;
v___x_1058_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1059_ = l_Lean_Name_toString(v___x_1058_, v___x_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1060_, lean_object* v_revCmds_1061_, lean_object* v_cmdState_1062_, lean_object* v_beginPos_1063_, lean_object* v_snap_1064_, lean_object* v_cancelTk_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_env_1068_; lean_object* v_scopes_1069_; lean_object* v_usedQuotCtxts_1070_; lean_object* v_nextMacroScope_1071_; lean_object* v_maxRecDepth_1072_; lean_object* v_ngen_1073_; lean_object* v_auxDeclNGen_1074_; lean_object* v_infoState_1075_; lean_object* v_prevLinterStates_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1159_; 
v_env_1068_ = lean_ctor_get(v_cmdState_1062_, 0);
v_scopes_1069_ = lean_ctor_get(v_cmdState_1062_, 2);
v_usedQuotCtxts_1070_ = lean_ctor_get(v_cmdState_1062_, 3);
v_nextMacroScope_1071_ = lean_ctor_get(v_cmdState_1062_, 4);
v_maxRecDepth_1072_ = lean_ctor_get(v_cmdState_1062_, 5);
v_ngen_1073_ = lean_ctor_get(v_cmdState_1062_, 6);
v_auxDeclNGen_1074_ = lean_ctor_get(v_cmdState_1062_, 7);
v_infoState_1075_ = lean_ctor_get(v_cmdState_1062_, 8);
v_prevLinterStates_1076_ = lean_ctor_get(v_cmdState_1062_, 11);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_cmdState_1062_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; 
v_unused_1160_ = lean_ctor_get(v_cmdState_1062_, 12);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_cmdState_1062_, 10);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_cmdState_1062_, 9);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_cmdState_1062_, 1);
lean_dec(v_unused_1163_);
v___x_1078_ = v_cmdState_1062_;
v_isShared_1079_ = v_isSharedCheck_1159_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_prevLinterStates_1076_);
lean_inc(v_infoState_1075_);
lean_inc(v_auxDeclNGen_1074_);
lean_inc(v_ngen_1073_);
lean_inc(v_maxRecDepth_1072_);
lean_inc(v_nextMacroScope_1071_);
lean_inc(v_usedQuotCtxts_1070_);
lean_inc(v_scopes_1069_);
lean_inc(v_env_1068_);
lean_dec(v_cmdState_1062_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1159_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___f_1080_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1080_, 0, v_stx_1060_);
lean_closure_set(v___f_1080_, 1, v_revCmds_1061_);
v___x_1081_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1082_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1083_ = l_List_head_x21___redArg(v___x_1081_, v_scopes_1069_);
v___x_1084_ = l_Lean_MessageLog_empty;
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1087_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 12, v___x_1087_);
lean_ctor_set(v___x_1078_, 10, v___x_1087_);
lean_ctor_set(v___x_1078_, 9, v___x_1086_);
lean_ctor_set(v___x_1078_, 1, v___x_1084_);
v___x_1089_ = v___x_1078_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_env_1068_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_scopes_1069_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_usedQuotCtxts_1070_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_nextMacroScope_1071_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v_maxRecDepth_1072_);
lean_ctor_set(v_reuseFailAlloc_1158_, 6, v_ngen_1073_);
lean_ctor_set(v_reuseFailAlloc_1158_, 7, v_auxDeclNGen_1074_);
lean_ctor_set(v_reuseFailAlloc_1158_, 8, v_infoState_1075_);
lean_ctor_set(v_reuseFailAlloc_1158_, 9, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1158_, 10, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1158_, 11, v_prevLinterStates_1076_);
lean_ctor_set(v_reuseFailAlloc_1158_, 12, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v_toProcessingContext_1091_; lean_object* v_fileName_1092_; lean_object* v_fileMap_1093_; lean_object* v_opts_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; uint8_t v___y_1102_; lean_object* v_env_1103_; lean_object* v_scopes_1104_; lean_object* v_usedQuotCtxts_1105_; lean_object* v_nextMacroScope_1106_; lean_object* v_maxRecDepth_1107_; lean_object* v_ngen_1108_; lean_object* v_auxDeclNGen_1109_; lean_object* v_infoState_1110_; lean_object* v_traceState_1111_; lean_object* v_snapshotTasks_1112_; lean_object* v_prevLinterStates_1113_; lean_object* v_codeQualityEntryTasks_1114_; lean_object* v_messages_1115_; lean_object* v___y_1124_; 
v___x_1090_ = lean_st_mk_ref(v___x_1089_);
v_toProcessingContext_1091_ = lean_ctor_get(v_a_1066_, 0);
v_fileName_1092_ = lean_ctor_get(v_toProcessingContext_1091_, 1);
v_fileMap_1093_ = lean_ctor_get(v_toProcessingContext_1091_, 2);
v_opts_1094_ = lean_ctor_get(v___x_1083_, 1);
lean_inc_ref(v_opts_1094_);
lean_dec(v___x_1083_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Lean_firstFrontendMacroScope;
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_internal_cmdlineSnapshots;
v___x_1100_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1094_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1157_; 
lean_inc_ref(v_snap_1064_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_snap_1064_);
v___y_1124_ = v___x_1157_;
goto v___jp_1123_;
}
else
{
v___y_1124_ = v___x_1096_;
goto v___jp_1123_;
}
v___jp_1101_:
{
lean_object* v_new_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_new_1116_ = lean_ctor_get(v_snap_1064_, 1);
lean_inc(v_new_1116_);
lean_dec_ref(v_snap_1064_);
v___x_1117_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1117_, 0, v_env_1103_);
lean_ctor_set(v___x_1117_, 1, v_messages_1115_);
lean_ctor_set(v___x_1117_, 2, v_scopes_1104_);
lean_ctor_set(v___x_1117_, 3, v_usedQuotCtxts_1105_);
lean_ctor_set(v___x_1117_, 4, v_nextMacroScope_1106_);
lean_ctor_set(v___x_1117_, 5, v_maxRecDepth_1107_);
lean_ctor_set(v___x_1117_, 6, v_ngen_1108_);
lean_ctor_set(v___x_1117_, 7, v_auxDeclNGen_1109_);
lean_ctor_set(v___x_1117_, 8, v_infoState_1110_);
lean_ctor_set(v___x_1117_, 9, v_traceState_1111_);
lean_ctor_set(v___x_1117_, 10, v_snapshotTasks_1112_);
lean_ctor_set(v___x_1117_, 11, v_prevLinterStates_1113_);
lean_ctor_set(v___x_1117_, 12, v_codeQualityEntryTasks_1114_);
v___x_1118_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1119_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1120_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_ctor_set(v___x_1120_, 2, v___x_1096_);
lean_ctor_set(v___x_1120_, 3, v___x_1086_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*4, v___y_1102_);
v___x_1121_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1082_, v___x_1120_);
v___x_1122_ = lean_io_promise_resolve(v___x_1121_, v_new_1116_);
lean_dec(v_new_1116_);
return v___x_1117_;
}
v___jp_1123_:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v_fst_1133_; lean_object* v___x_1134_; lean_object* v_env_1135_; lean_object* v_messages_1136_; lean_object* v_scopes_1137_; lean_object* v_usedQuotCtxts_1138_; lean_object* v_nextMacroScope_1139_; lean_object* v_maxRecDepth_1140_; lean_object* v_ngen_1141_; lean_object* v_auxDeclNGen_1142_; lean_object* v_infoState_1143_; lean_object* v_traceState_1144_; lean_object* v_snapshotTasks_1145_; lean_object* v_prevLinterStates_1146_; lean_object* v_codeQualityEntryTasks_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_cancelTk_1065_);
v___x_1126_ = 0;
v___x_1127_ = 0;
lean_inc(v_beginPos_1063_);
lean_inc_ref(v_fileMap_1093_);
lean_inc_ref(v_fileName_1092_);
v___x_1128_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1128_, 0, v_fileName_1092_);
lean_ctor_set(v___x_1128_, 1, v_fileMap_1093_);
lean_ctor_set(v___x_1128_, 2, v___x_1085_);
lean_ctor_set(v___x_1128_, 3, v_beginPos_1063_);
lean_ctor_set(v___x_1128_, 4, v___x_1095_);
lean_ctor_set(v___x_1128_, 5, v___x_1096_);
lean_ctor_set(v___x_1128_, 6, v___x_1097_);
lean_ctor_set(v___x_1128_, 7, v___x_1098_);
lean_ctor_set(v___x_1128_, 8, v___y_1124_);
lean_ctor_set(v___x_1128_, 9, v___x_1125_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*10, v___x_1126_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*10 + 1, v___x_1127_);
lean_inc(v___x_1090_);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1129_, 0, v___f_1080_);
lean_closure_set(v___f_1129_, 1, v___x_1128_);
lean_closure_set(v___f_1129_, 2, v___x_1090_);
v___x_1130_ = l_Lean_Core_stderrAsMessages;
v___x_1131_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1094_, v___x_1130_);
lean_dec_ref(v_opts_1094_);
v___x_1132_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1129_, v___x_1131_, v_a_1066_);
v_fst_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_fst_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_st_ref_get(v___x_1090_);
lean_dec(v___x_1090_);
v_env_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc_ref(v_env_1135_);
v_messages_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc_ref(v_messages_1136_);
v_scopes_1137_ = lean_ctor_get(v___x_1134_, 2);
lean_inc(v_scopes_1137_);
v_usedQuotCtxts_1138_ = lean_ctor_get(v___x_1134_, 3);
lean_inc(v_usedQuotCtxts_1138_);
v_nextMacroScope_1139_ = lean_ctor_get(v___x_1134_, 4);
lean_inc(v_nextMacroScope_1139_);
v_maxRecDepth_1140_ = lean_ctor_get(v___x_1134_, 5);
lean_inc(v_maxRecDepth_1140_);
v_ngen_1141_ = lean_ctor_get(v___x_1134_, 6);
lean_inc_ref(v_ngen_1141_);
v_auxDeclNGen_1142_ = lean_ctor_get(v___x_1134_, 7);
lean_inc_ref(v_auxDeclNGen_1142_);
v_infoState_1143_ = lean_ctor_get(v___x_1134_, 8);
lean_inc_ref(v_infoState_1143_);
v_traceState_1144_ = lean_ctor_get(v___x_1134_, 9);
lean_inc_ref(v_traceState_1144_);
v_snapshotTasks_1145_ = lean_ctor_get(v___x_1134_, 10);
lean_inc_ref(v_snapshotTasks_1145_);
v_prevLinterStates_1146_ = lean_ctor_get(v___x_1134_, 11);
lean_inc(v_prevLinterStates_1146_);
v_codeQualityEntryTasks_1147_ = lean_ctor_get(v___x_1134_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1147_);
lean_dec(v___x_1134_);
v___x_1148_ = lean_string_utf8_byte_size(v_fst_1133_);
v___x_1149_ = lean_nat_dec_eq(v___x_1148_, v___x_1085_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_inc_ref(v_fileMap_1093_);
v___x_1150_ = l_Lean_FileMap_toPosition(v_fileMap_1093_, v_beginPos_1063_);
lean_dec(v_beginPos_1063_);
v___x_1151_ = 0;
v___x_1152_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_fst_1133_);
v___x_1154_ = l_Lean_MessageData_ofFormat(v___x_1153_);
lean_inc_ref(v_fileName_1092_);
v___x_1155_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1155_, 0, v_fileName_1092_);
lean_ctor_set(v___x_1155_, 1, v___x_1150_);
lean_ctor_set(v___x_1155_, 2, v___x_1096_);
lean_ctor_set(v___x_1155_, 3, v___x_1152_);
lean_ctor_set(v___x_1155_, 4, v___x_1154_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*5, v___x_1126_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*5 + 1, v___x_1151_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*5 + 2, v___x_1126_);
v___x_1156_ = l_Lean_MessageLog_add(v___x_1155_, v_messages_1136_);
v___y_1102_ = v___x_1126_;
v_env_1103_ = v_env_1135_;
v_scopes_1104_ = v_scopes_1137_;
v_usedQuotCtxts_1105_ = v_usedQuotCtxts_1138_;
v_nextMacroScope_1106_ = v_nextMacroScope_1139_;
v_maxRecDepth_1107_ = v_maxRecDepth_1140_;
v_ngen_1108_ = v_ngen_1141_;
v_auxDeclNGen_1109_ = v_auxDeclNGen_1142_;
v_infoState_1110_ = v_infoState_1143_;
v_traceState_1111_ = v_traceState_1144_;
v_snapshotTasks_1112_ = v_snapshotTasks_1145_;
v_prevLinterStates_1113_ = v_prevLinterStates_1146_;
v_codeQualityEntryTasks_1114_ = v_codeQualityEntryTasks_1147_;
v_messages_1115_ = v___x_1156_;
goto v___jp_1101_;
}
else
{
lean_dec(v_fst_1133_);
lean_dec(v_beginPos_1063_);
v___y_1102_ = v___x_1126_;
v_env_1103_ = v_env_1135_;
v_scopes_1104_ = v_scopes_1137_;
v_usedQuotCtxts_1105_ = v_usedQuotCtxts_1138_;
v_nextMacroScope_1106_ = v_nextMacroScope_1139_;
v_maxRecDepth_1107_ = v_maxRecDepth_1140_;
v_ngen_1108_ = v_ngen_1141_;
v_auxDeclNGen_1109_ = v_auxDeclNGen_1142_;
v_infoState_1110_ = v_infoState_1143_;
v_traceState_1111_ = v_traceState_1144_;
v_snapshotTasks_1112_ = v_snapshotTasks_1145_;
v_prevLinterStates_1113_ = v_prevLinterStates_1146_;
v_codeQualityEntryTasks_1114_ = v_codeQualityEntryTasks_1147_;
v_messages_1115_ = v_messages_1136_;
goto v___jp_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1164_, lean_object* v_revCmds_1165_, lean_object* v_cmdState_1166_, lean_object* v_beginPos_1167_, lean_object* v_snap_1168_, lean_object* v_cancelTk_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1164_, v_revCmds_1165_, v_cmdState_1166_, v_beginPos_1167_, v_snap_1168_, v_cancelTk_1169_, v_a_1170_);
lean_dec_ref(v_a_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1173_, lean_object* v_h_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1174_, v_x_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_h_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1179_, v_h_1180_, v_x_1181_, v___y_1182_);
lean_dec_ref(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1185_, lean_object* v_x_1186_, uint8_t v_isolateStderr_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1186_, v_isolateStderr_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_x_1192_, lean_object* v_isolateStderr_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v_isolateStderr_boxed_1196_; lean_object* v_res_1197_; 
v_isolateStderr_boxed_1196_ = lean_unbox(v_isolateStderr_1193_);
v_res_1197_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1191_, v_x_1192_, v_isolateStderr_boxed_1196_, v___y_1194_);
lean_dec_ref(v___y_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1198_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1208_){
_start:
{
lean_object* v_toSnapshotTreeM_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_toSnapshotTreeM_1209_ = lean_ctor_get(v_a_1208_, 1);
lean_inc_ref(v_toSnapshotTreeM_1209_);
lean_dec_ref(v_a_1208_);
v___x_1210_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1211_ = lean_apply_1(v_toSnapshotTreeM_1209_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1212_){
_start:
{
lean_object* v_toSnapshot_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_toSnapshot_1213_ = lean_ctor_get(v_a_1212_, 0);
lean_inc_ref(v_toSnapshot_1213_);
lean_dec_ref(v_a_1212_);
v___x_1214_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1215_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1213_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1220_ = l_Lean_Language_Snapshot_transform(v_a_1218_, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1223_, lean_object* v_opt_1224_){
_start:
{
lean_object* v_name_1225_; lean_object* v_defValue_1226_; lean_object* v_map_1227_; lean_object* v___x_1228_; 
v_name_1225_ = lean_ctor_get(v_opt_1224_, 0);
v_defValue_1226_ = lean_ctor_get(v_opt_1224_, 1);
v_map_1227_ = lean_ctor_get(v_opts_1223_, 0);
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1227_, v_name_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_inc(v_defValue_1226_);
return v_defValue_1226_;
}
else
{
lean_object* v_val_1229_; 
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1228_, 1);
if (lean_obj_tag(v_val_1229_) == 3)
{
lean_object* v_v_1230_; 
v_v_1230_ = lean_ctor_get(v_val_1229_, 0);
lean_inc(v_v_1230_);
lean_dec_ref_known(v_val_1229_, 1);
return v_v_1230_;
}
else
{
lean_dec(v_val_1229_);
lean_inc(v_defValue_1226_);
return v_defValue_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1231_, lean_object* v_opt_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1231_, v_opt_1232_);
lean_dec_ref(v_opt_1232_);
lean_dec_ref(v_opts_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1236_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1234_, v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1243_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1244_ = l_Lean_Name_append(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1245_, lean_object* v___x_1246_, uint8_t v_val_1247_, lean_object* v_val_1248_, lean_object* v_val_1249_, lean_object* v___x_1250_, lean_object* v___x_1251_, uint8_t v___x_1252_, lean_object* v_a_1253_, lean_object* v_pos_1254_, lean_object* v___x_1255_, lean_object* v_infoSt_1256_){
_start:
{
lean_object* v___y_1259_; lean_object* v_msgLog_1260_; lean_object* v___y_1266_; lean_object* v_trees_1298_; lean_object* v_size_1299_; uint8_t v___x_1300_; 
v_trees_1298_ = lean_ctor_get(v_infoSt_1256_, 2);
v_size_1299_ = lean_ctor_get(v_trees_1298_, 2);
v___x_1300_ = lean_nat_dec_lt(v___x_1251_, v_size_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
v___x_1301_ = l_outOfBounds___redArg(v___x_1255_);
v___y_1266_ = v___x_1301_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1255_, v_trees_1298_, v___x_1251_);
v___y_1266_ = v___x_1302_;
goto v___jp_1265_;
}
v___jp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1260_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___y_1259_);
v___x_1263_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1245_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
lean_ctor_set(v___x_1263_, 2, v___x_1262_);
lean_ctor_set(v___x_1263_, 3, v___x_1246_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*4, v_val_1247_);
v___x_1264_ = lean_io_promise_resolve(v___x_1263_, v_val_1248_);
return v___x_1264_;
}
v___jp_1265_:
{
lean_object* v_scopes_1267_; lean_object* v___x_1268_; lean_object* v_opts_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v_hasTrace_1273_; 
v_scopes_1267_ = lean_ctor_get(v_val_1249_, 2);
v___x_1268_ = l_List_head_x21___redArg(v___x_1250_, v_scopes_1267_);
v_opts_1269_ = lean_ctor_get(v___x_1268_, 1);
lean_inc_ref(v_opts_1269_);
lean_dec(v___x_1268_);
v___x_1270_ = l_Lean_MessageLog_empty;
v___x_1271_ = l_Lean_inheritedTraceOptions;
v___x_1272_ = lean_st_ref_get(v___x_1271_);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_opts_1269_, sizeof(void*)*1);
if (v_hasTrace_1273_ == 0)
{
lean_dec(v___x_1272_);
lean_dec_ref(v_opts_1269_);
lean_dec(v___x_1251_);
v___y_1259_ = v___y_1266_;
v_msgLog_1260_ = v___x_1270_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1275_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1276_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1277_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1272_, v_opts_1269_, v___x_1276_);
lean_dec_ref(v_opts_1269_);
lean_dec(v___x_1272_);
if (v___x_1277_ == 0)
{
lean_dec(v___x_1251_);
v___y_1259_ = v___y_1266_;
v_msgLog_1260_ = v___x_1270_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_box(0);
lean_inc_ref(v___y_1266_);
v___x_1279_ = l_Lean_Elab_InfoTree_format(v___y_1266_, v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; double v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v_toProcessingContext_1284_; lean_object* v_fileName_1285_; lean_object* v_fileMap_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_float_of_nat(v___x_1251_);
v___x_1282_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1283_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1283_, 0, v___x_1274_);
lean_ctor_set(v___x_1283_, 1, v___x_1278_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
lean_ctor_set_float(v___x_1283_, sizeof(void*)*3, v___x_1281_);
lean_ctor_set_float(v___x_1283_, sizeof(void*)*3 + 8, v___x_1281_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*3 + 16, v___x_1252_);
v_toProcessingContext_1284_ = lean_ctor_get(v_a_1253_, 0);
v_fileName_1285_ = lean_ctor_get(v_toProcessingContext_1284_, 1);
v_fileMap_1286_ = lean_ctor_get(v_toProcessingContext_1284_, 2);
v___x_1287_ = l_Lean_MessageData_nil;
v___x_1288_ = l_Lean_MessageData_ofFormat(v_a_1280_);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_array_push(v___x_1290_, v___x_1288_);
v___x_1292_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1283_);
lean_ctor_set(v___x_1292_, 1, v___x_1287_);
lean_ctor_set(v___x_1292_, 2, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1275_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
lean_inc_ref(v_fileMap_1286_);
v___x_1294_ = l_Lean_FileMap_toPosition(v_fileMap_1286_, v_pos_1254_);
v___x_1295_ = 0;
lean_inc_ref(v_fileName_1285_);
v___x_1296_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1296_, 0, v_fileName_1285_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
lean_ctor_set(v___x_1296_, 2, v___x_1278_);
lean_ctor_set(v___x_1296_, 3, v___x_1282_);
lean_ctor_set(v___x_1296_, 4, v___x_1293_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*5, v_val_1247_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*5 + 1, v___x_1295_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*5 + 2, v_val_1247_);
v___x_1297_ = l_Lean_MessageLog_add(v___x_1296_, v___x_1270_);
v___y_1259_ = v___y_1266_;
v_msgLog_1260_ = v___x_1297_;
goto v___jp_1258_;
}
else
{
lean_dec_ref_known(v___x_1279_, 1);
lean_dec(v___x_1251_);
v___y_1259_ = v___y_1266_;
v_msgLog_1260_ = v___x_1270_;
goto v___jp_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v_val_1305_, lean_object* v_val_1306_, lean_object* v_val_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v_a_1311_, lean_object* v_pos_1312_, lean_object* v___x_1313_, lean_object* v_infoSt_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v_val_36691__boxed_1316_; uint8_t v___x_36696__boxed_1317_; lean_object* v_res_1318_; 
v_val_36691__boxed_1316_ = lean_unbox(v_val_1305_);
v___x_36696__boxed_1317_ = lean_unbox(v___x_1310_);
v_res_1318_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1303_, v___x_1304_, v_val_36691__boxed_1316_, v_val_1306_, v_val_1307_, v___x_1308_, v___x_1309_, v___x_36696__boxed_1317_, v_a_1311_, v_pos_1312_, v___x_1313_, v_infoSt_1314_);
lean_dec_ref(v_infoSt_1314_);
lean_dec_ref(v___x_1313_);
lean_dec(v_pos_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v___x_1308_);
lean_dec_ref(v_val_1307_);
lean_dec(v_val_1306_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1319_, lean_object* v___x_1320_, lean_object* v___x_1321_, uint8_t v_val_1322_, lean_object* v_as_1323_, size_t v_sz_1324_, size_t v_i_1325_, lean_object* v_b_1326_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_lt(v_i_1325_, v_sz_1324_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v___x_1321_);
lean_dec_ref(v___x_1319_);
return v_b_1326_;
}
else
{
lean_object* v_snd_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1347_; 
v_snd_1329_ = lean_ctor_get(v_b_1326_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_b_1326_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_b_1326_, 0);
lean_dec(v_unused_1348_);
v___x_1331_ = v_b_1326_;
v_isShared_1332_ = v_isSharedCheck_1347_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_snd_1329_);
lean_dec(v_b_1326_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1347_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v_a_1333_; lean_object* v_msg_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v_a_1333_ = lean_array_uget_borrowed(v_as_1323_, v_i_1325_);
v_msg_1334_ = lean_ctor_get(v_a_1333_, 1);
v___x_1335_ = lean_box(0);
lean_inc_ref(v___x_1319_);
v___x_1336_ = l_Lean_FileMap_toPosition(v___x_1319_, v___x_1320_);
v___x_1337_ = 0;
v___x_1338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1334_);
lean_inc_ref(v___x_1321_);
v___x_1339_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1339_, 0, v___x_1321_);
lean_ctor_set(v___x_1339_, 1, v___x_1336_);
lean_ctor_set(v___x_1339_, 2, v___x_1335_);
lean_ctor_set(v___x_1339_, 3, v___x_1338_);
lean_ctor_set(v___x_1339_, 4, v_msg_1334_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*5, v_val_1322_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*5 + 1, v___x_1337_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*5 + 2, v_val_1322_);
v___x_1340_ = l_Lean_MessageLog_add(v___x_1339_, v_snd_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1340_);
lean_ctor_set(v___x_1331_, 0, v___x_1335_);
v___x_1342_ = v___x_1331_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
size_t v___x_1343_; size_t v___x_1344_; 
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_add(v_i_1325_, v___x_1343_);
v_i_1325_ = v___x_1344_;
v_b_1326_ = v___x_1342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1349_, lean_object* v___x_1350_, lean_object* v___x_1351_, lean_object* v_val_1352_, lean_object* v_as_1353_, lean_object* v_sz_1354_, lean_object* v_i_1355_, lean_object* v_b_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v_val_36804__boxed_1358_; size_t v_sz_boxed_1359_; size_t v_i_boxed_1360_; lean_object* v_res_1361_; 
v_val_36804__boxed_1358_ = lean_unbox(v_val_1352_);
v_sz_boxed_1359_ = lean_unbox_usize(v_sz_1354_);
lean_dec(v_sz_1354_);
v_i_boxed_1360_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_res_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1349_, v___x_1350_, v___x_1351_, v_val_36804__boxed_1358_, v_as_1353_, v_sz_boxed_1359_, v_i_boxed_1360_, v_b_1356_);
lean_dec_ref(v_as_1353_);
lean_dec(v___x_1350_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, uint8_t v_val_1365_, lean_object* v_as_1366_, size_t v_sz_1367_, size_t v_i_1368_, lean_object* v_b_1369_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_lt(v_i_1368_, v_sz_1367_);
if (v___x_1371_ == 0)
{
lean_dec_ref(v___x_1364_);
lean_dec_ref(v___x_1362_);
return v_b_1369_;
}
else
{
lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1390_; 
v_snd_1372_ = lean_ctor_get(v_b_1369_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_b_1369_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v_b_1369_, 0);
lean_dec(v_unused_1391_);
v___x_1374_ = v_b_1369_;
v_isShared_1375_ = v_isSharedCheck_1390_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_dec(v_b_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1390_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v_a_1376_; lean_object* v_msg_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v_a_1376_ = lean_array_uget_borrowed(v_as_1366_, v_i_1368_);
v_msg_1377_ = lean_ctor_get(v_a_1376_, 1);
v___x_1378_ = lean_box(0);
lean_inc_ref(v___x_1362_);
v___x_1379_ = l_Lean_FileMap_toPosition(v___x_1362_, v___x_1363_);
v___x_1380_ = 0;
v___x_1381_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1377_);
lean_inc_ref(v___x_1364_);
v___x_1382_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1382_, 0, v___x_1364_);
lean_ctor_set(v___x_1382_, 1, v___x_1379_);
lean_ctor_set(v___x_1382_, 2, v___x_1378_);
lean_ctor_set(v___x_1382_, 3, v___x_1381_);
lean_ctor_set(v___x_1382_, 4, v_msg_1377_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*5, v_val_1365_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*5 + 1, v___x_1380_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*5 + 2, v_val_1365_);
v___x_1383_ = l_Lean_MessageLog_add(v___x_1382_, v_snd_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1383_);
lean_ctor_set(v___x_1374_, 0, v___x_1378_);
v___x_1385_ = v___x_1374_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1368_, v___x_1386_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1362_, v___x_1363_, v___x_1364_, v_val_1365_, v_as_1366_, v_sz_1367_, v___x_1387_, v___x_1385_);
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v_val_1395_, lean_object* v_as_1396_, lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_b_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v_val_36856__boxed_1401_; size_t v_sz_boxed_1402_; size_t v_i_boxed_1403_; lean_object* v_res_1404_; 
v_val_36856__boxed_1401_ = lean_unbox(v_val_1395_);
v_sz_boxed_1402_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1403_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1392_, v___x_1393_, v___x_1394_, v_val_36856__boxed_1401_, v_as_1396_, v_sz_boxed_1402_, v_i_boxed_1403_, v_b_1399_);
lean_dec_ref(v_as_1396_);
lean_dec(v___x_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v___x_1408_, uint8_t v_val_1409_, lean_object* v_n_1410_, lean_object* v_b_1411_){
_start:
{
if (lean_obj_tag(v_n_1410_) == 0)
{
lean_object* v_cs_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; lean_object* v_fst_1419_; 
v_cs_1413_ = lean_ctor_get(v_n_1410_, 0);
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v_b_1411_);
v_sz_1416_ = lean_array_size(v_cs_1413_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1405_, v___x_1406_, v___x_1407_, v___x_1408_, v_val_1409_, v_cs_1413_, v_sz_1416_, v___x_1417_, v___x_1415_);
v_fst_1419_ = lean_ctor_get(v___x_1418_, 0);
if (lean_obj_tag(v_fst_1419_) == 0)
{
lean_object* v_snd_1420_; lean_object* v___x_1421_; 
v_snd_1420_ = lean_ctor_get(v___x_1418_, 1);
lean_inc(v_snd_1420_);
lean_dec_ref(v___x_1418_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_snd_1420_);
return v___x_1421_;
}
else
{
lean_object* v_val_1422_; 
lean_inc_ref(v_fst_1419_);
lean_dec_ref(v___x_1418_);
v_val_1422_ = lean_ctor_get(v_fst_1419_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v_fst_1419_, 1);
return v_val_1422_;
}
}
else
{
lean_object* v_vs_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; size_t v_sz_1426_; size_t v___x_1427_; lean_object* v___x_1428_; lean_object* v_fst_1429_; 
v_vs_1423_ = lean_ctor_get(v_n_1410_, 0);
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
lean_ctor_set(v___x_1425_, 1, v_b_1411_);
v_sz_1426_ = lean_array_size(v_vs_1423_);
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1406_, v___x_1407_, v___x_1408_, v_val_1409_, v_vs_1423_, v_sz_1426_, v___x_1427_, v___x_1425_);
v_fst_1429_ = lean_ctor_get(v___x_1428_, 0);
if (lean_obj_tag(v_fst_1429_) == 0)
{
lean_object* v_snd_1430_; lean_object* v___x_1431_; 
v_snd_1430_ = lean_ctor_get(v___x_1428_, 1);
lean_inc(v_snd_1430_);
lean_dec_ref(v___x_1428_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_snd_1430_);
return v___x_1431_;
}
else
{
lean_object* v_val_1432_; 
lean_inc_ref(v_fst_1429_);
lean_dec_ref(v___x_1428_);
v_val_1432_ = lean_ctor_get(v_fst_1429_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v_fst_1429_, 1);
return v_val_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1433_, lean_object* v___x_1434_, lean_object* v___x_1435_, lean_object* v___x_1436_, uint8_t v_val_1437_, lean_object* v_as_1438_, size_t v_sz_1439_, size_t v_i_1440_, lean_object* v_b_1441_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_usize_dec_lt(v_i_1440_, v_sz_1439_);
if (v___x_1443_ == 0)
{
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1434_);
return v_b_1441_;
}
else
{
lean_object* v_snd_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1462_; 
v_snd_1444_ = lean_ctor_get(v_b_1441_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_b_1441_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_b_1441_, 0);
lean_dec(v_unused_1463_);
v___x_1446_ = v_b_1441_;
v_isShared_1447_ = v_isSharedCheck_1462_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_snd_1444_);
lean_dec(v_b_1441_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1462_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1450_; 
v___x_1448_ = lean_box(0);
v_a_1449_ = lean_array_uget_borrowed(v_as_1438_, v_i_1440_);
lean_inc(v_snd_1444_);
lean_inc_ref(v___x_1436_);
lean_inc_ref(v___x_1434_);
v___x_1450_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1433_, v___x_1434_, v___x_1435_, v___x_1436_, v_val_1437_, v_a_1449_, v_snd_1444_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1434_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1451_);
v___x_1453_ = v___x_1446_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_snd_1444_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; 
lean_dec(v_snd_1444_);
v_a_1455_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1450_, 1);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v_a_1455_);
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1457_ = v___x_1446_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1455_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
size_t v___x_1458_; size_t v___x_1459_; 
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_add(v_i_1440_, v___x_1458_);
v_i_1440_ = v___x_1459_;
v_b_1441_ = v___x_1457_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1464_, lean_object* v___x_1465_, lean_object* v___x_1466_, lean_object* v___x_1467_, lean_object* v_val_1468_, lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_val_36907__boxed_1474_; size_t v_sz_boxed_1475_; size_t v_i_boxed_1476_; lean_object* v_res_1477_; 
v_val_36907__boxed_1474_ = lean_unbox(v_val_1468_);
v_sz_boxed_1475_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1476_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1464_, v___x_1465_, v___x_1466_, v___x_1467_, v_val_36907__boxed_1474_, v_as_1469_, v_sz_boxed_1475_, v_i_boxed_1476_, v_b_1472_);
lean_dec_ref(v_as_1469_);
lean_dec(v___x_1466_);
lean_dec_ref(v_init_1464_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v_val_1482_, lean_object* v_n_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_){
_start:
{
uint8_t v_val_36923__boxed_1486_; lean_object* v_res_1487_; 
v_val_36923__boxed_1486_ = lean_unbox(v_val_1482_);
v_res_1487_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1478_, v___x_1479_, v___x_1480_, v___x_1481_, v_val_36923__boxed_1486_, v_n_1483_, v_b_1484_);
lean_dec_ref(v_n_1483_);
lean_dec(v___x_1480_);
lean_dec_ref(v_init_1478_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1488_, lean_object* v___x_1489_, lean_object* v___x_1490_, uint8_t v_val_1491_, lean_object* v_as_1492_, size_t v_sz_1493_, size_t v_i_1494_, lean_object* v_b_1495_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_lt(v_i_1494_, v_sz_1493_);
if (v___x_1497_ == 0)
{
lean_dec_ref(v___x_1490_);
lean_dec_ref(v___x_1488_);
return v_b_1495_;
}
else
{
lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1516_; 
v_snd_1498_ = lean_ctor_get(v_b_1495_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_b_1495_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_b_1495_, 0);
lean_dec(v_unused_1517_);
v___x_1500_ = v_b_1495_;
v_isShared_1501_ = v_isSharedCheck_1516_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_b_1495_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1516_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_a_1502_; lean_object* v_msg_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v_a_1502_ = lean_array_uget_borrowed(v_as_1492_, v_i_1494_);
v_msg_1503_ = lean_ctor_get(v_a_1502_, 1);
v___x_1504_ = lean_box(0);
lean_inc_ref(v___x_1488_);
v___x_1505_ = l_Lean_FileMap_toPosition(v___x_1488_, v___x_1489_);
v___x_1506_ = 0;
v___x_1507_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1503_);
lean_inc_ref(v___x_1490_);
v___x_1508_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1508_, 0, v___x_1490_);
lean_ctor_set(v___x_1508_, 1, v___x_1505_);
lean_ctor_set(v___x_1508_, 2, v___x_1504_);
lean_ctor_set(v___x_1508_, 3, v___x_1507_);
lean_ctor_set(v___x_1508_, 4, v_msg_1503_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*5, v_val_1491_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*5 + 1, v___x_1506_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*5 + 2, v_val_1491_);
v___x_1509_ = l_Lean_MessageLog_add(v___x_1508_, v_snd_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1509_);
lean_ctor_set(v___x_1500_, 0, v___x_1504_);
v___x_1511_ = v___x_1500_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
size_t v___x_1512_; size_t v___x_1513_; 
v___x_1512_ = ((size_t)1ULL);
v___x_1513_ = lean_usize_add(v_i_1494_, v___x_1512_);
v_i_1494_ = v___x_1513_;
v_b_1495_ = v___x_1511_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v_val_1521_, lean_object* v_as_1522_, lean_object* v_sz_1523_, lean_object* v_i_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v_val_37005__boxed_1527_; size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_val_37005__boxed_1527_ = lean_unbox(v_val_1521_);
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1523_);
lean_dec(v_sz_1523_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1524_);
lean_dec(v_i_1524_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1518_, v___x_1519_, v___x_1520_, v_val_37005__boxed_1527_, v_as_1522_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1525_);
lean_dec_ref(v_as_1522_);
lean_dec(v___x_1519_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1531_, lean_object* v___x_1532_, lean_object* v___x_1533_, uint8_t v_val_1534_, lean_object* v_as_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_b_1538_){
_start:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1540_ == 0)
{
lean_dec_ref(v___x_1533_);
lean_dec_ref(v___x_1531_);
return v_b_1538_;
}
else
{
lean_object* v_snd_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1559_; 
v_snd_1541_ = lean_ctor_get(v_b_1538_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_b_1538_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_b_1538_, 0);
lean_dec(v_unused_1560_);
v___x_1543_ = v_b_1538_;
v_isShared_1544_ = v_isSharedCheck_1559_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_snd_1541_);
lean_dec(v_b_1538_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1559_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_a_1545_; lean_object* v_msg_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v_a_1545_ = lean_array_uget_borrowed(v_as_1535_, v_i_1537_);
v_msg_1546_ = lean_ctor_get(v_a_1545_, 1);
v___x_1547_ = lean_box(0);
lean_inc_ref(v___x_1531_);
v___x_1548_ = l_Lean_FileMap_toPosition(v___x_1531_, v___x_1532_);
v___x_1549_ = 0;
v___x_1550_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1546_);
lean_inc_ref(v___x_1533_);
v___x_1551_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1551_, 0, v___x_1533_);
lean_ctor_set(v___x_1551_, 1, v___x_1548_);
lean_ctor_set(v___x_1551_, 2, v___x_1547_);
lean_ctor_set(v___x_1551_, 3, v___x_1550_);
lean_ctor_set(v___x_1551_, 4, v_msg_1546_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*5, v_val_1534_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*5 + 1, v___x_1549_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*5 + 2, v_val_1534_);
v___x_1552_ = l_Lean_MessageLog_add(v___x_1551_, v_snd_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___x_1552_);
lean_ctor_set(v___x_1543_, 0, v___x_1547_);
v___x_1554_ = v___x_1543_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_add(v_i_1537_, v___x_1555_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1531_, v___x_1532_, v___x_1533_, v_val_1534_, v_as_1535_, v_sz_1536_, v___x_1556_, v___x_1554_);
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v_val_1564_, lean_object* v_as_1565_, lean_object* v_sz_1566_, lean_object* v_i_1567_, lean_object* v_b_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_val_37057__boxed_1570_; size_t v_sz_boxed_1571_; size_t v_i_boxed_1572_; lean_object* v_res_1573_; 
v_val_37057__boxed_1570_ = lean_unbox(v_val_1564_);
v_sz_boxed_1571_ = lean_unbox_usize(v_sz_1566_);
lean_dec(v_sz_1566_);
v_i_boxed_1572_ = lean_unbox_usize(v_i_1567_);
lean_dec(v_i_1567_);
v_res_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1561_, v___x_1562_, v___x_1563_, v_val_37057__boxed_1570_, v_as_1565_, v_sz_boxed_1571_, v_i_boxed_1572_, v_b_1568_);
lean_dec_ref(v_as_1565_);
lean_dec(v___x_1562_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1574_, lean_object* v___x_1575_, lean_object* v___x_1576_, uint8_t v_val_1577_, lean_object* v_t_1578_, lean_object* v_init_1579_){
_start:
{
lean_object* v_root_1581_; lean_object* v_tail_1582_; lean_object* v___x_1583_; 
v_root_1581_ = lean_ctor_get(v_t_1578_, 0);
v_tail_1582_ = lean_ctor_get(v_t_1578_, 1);
lean_inc_ref(v___x_1576_);
lean_inc_ref(v___x_1574_);
lean_inc_ref(v_init_1579_);
v___x_1583_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1579_, v___x_1574_, v___x_1575_, v___x_1576_, v_val_1577_, v_root_1581_, v_init_1579_);
lean_dec_ref(v_init_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; 
lean_dec_ref(v___x_1576_);
lean_dec_ref(v___x_1574_);
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
return v_a_1584_;
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_1590_; lean_object* v_fst_1591_; 
v_a_1585_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_a_1585_);
v_sz_1588_ = lean_array_size(v_tail_1582_);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1574_, v___x_1575_, v___x_1576_, v_val_1577_, v_tail_1582_, v_sz_1588_, v___x_1589_, v___x_1587_);
v_fst_1591_ = lean_ctor_get(v___x_1590_, 0);
if (lean_obj_tag(v_fst_1591_) == 0)
{
lean_object* v_snd_1592_; 
v_snd_1592_ = lean_ctor_get(v___x_1590_, 1);
lean_inc(v_snd_1592_);
lean_dec_ref(v___x_1590_);
return v_snd_1592_;
}
else
{
lean_object* v_val_1593_; 
lean_inc_ref(v_fst_1591_);
lean_dec_ref(v___x_1590_);
v_val_1593_ = lean_ctor_get(v_fst_1591_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v_fst_1591_, 1);
return v_val_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_val_1597_, lean_object* v_t_1598_, lean_object* v_init_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_val_37108__boxed_1601_; lean_object* v_res_1602_; 
v_val_37108__boxed_1601_ = lean_unbox(v_val_1597_);
v_res_1602_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1594_, v___x_1595_, v___x_1596_, v_val_37108__boxed_1601_, v_t_1598_, v_init_1599_);
lean_dec_ref(v_t_1598_);
lean_dec(v___x_1595_);
return v_res_1602_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = l_Lean_firstFrontendMacroScope;
v___x_1605_ = lean_nat_add(v___x_1604_, v___x_1603_);
return v___x_1605_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1616_, lean_object* v_opts_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v___x_1620_, size_t v___x_1621_, uint8_t v___x_1622_, lean_object* v_env_1623_, lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_pos_1626_, uint8_t v_val_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, lean_object* v___x_1632_, uint8_t v___x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v_toProcessingContext_1636_; lean_object* v_fileName_1637_; lean_object* v_fileMap_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint16_t v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_fileName_1663_; lean_object* v_fileMap_1664_; lean_object* v_currNamespace_1665_; lean_object* v_openDecls_1666_; lean_object* v_initHeartbeats_1667_; lean_object* v_maxHeartbeats_1668_; lean_object* v_quotContext_1669_; lean_object* v_currMacroScope_1670_; lean_object* v_cancelTk_x3f_1671_; lean_object* v_inheritedTraceOptions_1672_; lean_object* v_currRecDepth_1673_; lean_object* v_ref_1674_; uint8_t v_suppressElabErrors_1675_; uint8_t v_checkDeprecated_1676_; uint8_t v_isRecordingDeps_1677_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___y_1697_; lean_object* v_env_1718_; uint8_t v___x_1719_; uint16_t v___x_1720_; uint16_t v___x_1721_; uint16_t v___x_1722_; uint8_t v___x_1723_; 
v_toProcessingContext_1636_ = lean_ctor_get(v_a_1616_, 0);
v_fileName_1637_ = lean_ctor_get(v_toProcessingContext_1636_, 1);
v_fileMap_1638_ = lean_ctor_get(v_toProcessingContext_1636_, 2);
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Lean_Core_getMaxHeartbeats(v_opts_1617_);
v___x_1641_ = l_Lean_firstFrontendMacroScope;
v___x_1642_ = lean_box(0);
v___x_1643_ = l_Lean_OptionFlags_ofOptions(v_opts_1617_);
v___x_1644_ = 0;
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1647_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1618_);
v___x_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1618_);
lean_ctor_set(v___x_1648_, 1, v___x_1645_);
lean_ctor_set(v___x_1648_, 2, v___x_1639_);
v___x_1649_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1650_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1619_);
v___x_1652_ = l_Lean_Options_empty;
lean_inc_n(v___x_1619_, 5);
lean_inc_ref_n(v___x_1651_, 3);
v___x_1653_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
lean_ctor_set(v___x_1653_, 2, v___x_1651_);
lean_ctor_set(v___x_1653_, 3, v___x_1619_);
lean_ctor_set(v___x_1653_, 4, v___x_1619_);
lean_ctor_set(v___x_1653_, 5, v___x_1619_);
v___x_1654_ = lean_mk_empty_array_with_capacity(v___x_1620_);
lean_inc_ref(v___x_1654_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1654_);
lean_ctor_set(v___x_1656_, 2, v___x_1619_);
lean_ctor_set(v___x_1656_, 3, v___x_1619_);
lean_ctor_set_usize(v___x_1656_, 4, v___x_1621_);
v___x_1657_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1656_, 2);
v___x_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1656_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1659_, 0, v___x_1649_);
lean_ctor_set(v___x_1659_, 1, v___x_1649_);
lean_ctor_set(v___x_1659_, 2, v___x_1656_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*3, v___x_1622_);
lean_inc_ref(v___x_1624_);
v___x_1660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1660_, 0, v_env_1623_);
lean_ctor_set(v___x_1660_, 1, v___x_1646_);
lean_ctor_set(v___x_1660_, 2, v___x_1647_);
lean_ctor_set(v___x_1660_, 3, v___x_1648_);
lean_ctor_set(v___x_1660_, 4, v___x_1624_);
lean_ctor_set(v___x_1660_, 5, v___x_1650_);
lean_ctor_set(v___x_1660_, 6, v___x_1653_);
lean_ctor_set(v___x_1660_, 7, v___x_1658_);
lean_ctor_set(v___x_1660_, 8, v___x_1659_);
lean_ctor_set(v___x_1660_, 9, v___x_1651_);
v___x_1661_ = lean_st_mk_ref(v___x_1660_);
v___x_1694_ = lean_st_ref_get(v___x_1631_);
v___x_1695_ = lean_st_ref_get(v___x_1661_);
v_env_1718_ = lean_ctor_get(v___x_1695_, 0);
lean_inc_ref(v_env_1718_);
lean_dec(v___x_1695_);
v___x_1719_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1718_);
lean_dec_ref(v_env_1718_);
v___x_1720_ = 512;
v___x_1721_ = lean_uint16_land(v___x_1643_, v___x_1720_);
v___x_1722_ = 0;
v___x_1723_ = lean_uint16_dec_eq(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
if (v___x_1719_ == 0)
{
v___y_1697_ = v___x_1633_;
goto v___jp_1696_;
}
else
{
lean_inc(v___x_1619_);
lean_inc(v___x_1618_);
lean_inc_ref(v_fileMap_1638_);
lean_inc_ref(v_fileName_1637_);
v_fileName_1663_ = v_fileName_1637_;
v_fileMap_1664_ = v_fileMap_1638_;
v_currNamespace_1665_ = v___x_1618_;
v_openDecls_1666_ = v___x_1639_;
v_initHeartbeats_1667_ = v___x_1619_;
v_maxHeartbeats_1668_ = v___x_1640_;
v_quotContext_1669_ = v___x_1618_;
v_currMacroScope_1670_ = v___x_1641_;
v_cancelTk_x3f_1671_ = v___x_1632_;
v_inheritedTraceOptions_1672_ = v___x_1694_;
v_currRecDepth_1673_ = v___x_1619_;
v_ref_1674_ = v___x_1642_;
v_suppressElabErrors_1675_ = v_val_1627_;
v_checkDeprecated_1676_ = v___x_1644_;
v_isRecordingDeps_1677_ = v_val_1627_;
goto v___jp_1662_;
}
}
else
{
if (v___x_1719_ == 0)
{
lean_inc(v___x_1619_);
lean_inc(v___x_1618_);
lean_inc_ref(v_fileMap_1638_);
lean_inc_ref(v_fileName_1637_);
v_fileName_1663_ = v_fileName_1637_;
v_fileMap_1664_ = v_fileMap_1638_;
v_currNamespace_1665_ = v___x_1618_;
v_openDecls_1666_ = v___x_1639_;
v_initHeartbeats_1667_ = v___x_1619_;
v_maxHeartbeats_1668_ = v___x_1640_;
v_quotContext_1669_ = v___x_1618_;
v_currMacroScope_1670_ = v___x_1641_;
v_cancelTk_x3f_1671_ = v___x_1632_;
v_inheritedTraceOptions_1672_ = v___x_1694_;
v_currRecDepth_1673_ = v___x_1619_;
v_ref_1674_ = v___x_1642_;
v_suppressElabErrors_1675_ = v_val_1627_;
v_checkDeprecated_1676_ = v___x_1644_;
v_isRecordingDeps_1677_ = v_val_1627_;
goto v___jp_1662_;
}
else
{
v___y_1697_ = v_val_1627_;
goto v___jp_1696_;
}
}
v___jp_1662_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1678_ = l_Lean_maxRecDepth;
v___x_1679_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1617_, v___x_1678_);
lean_inc(v_currMacroScope_1670_);
lean_inc(v_openDecls_1666_);
v___x_1680_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1680_, 0, v_fileName_1663_);
lean_ctor_set(v___x_1680_, 1, v_fileMap_1664_);
lean_ctor_set(v___x_1680_, 2, v_opts_1617_);
lean_ctor_set(v___x_1680_, 3, v___x_1679_);
lean_ctor_set(v___x_1680_, 4, v_currNamespace_1665_);
lean_ctor_set(v___x_1680_, 5, v_openDecls_1666_);
lean_ctor_set(v___x_1680_, 6, v_initHeartbeats_1667_);
lean_ctor_set(v___x_1680_, 7, v_maxHeartbeats_1668_);
lean_ctor_set(v___x_1680_, 8, v_quotContext_1669_);
lean_ctor_set(v___x_1680_, 9, v_currMacroScope_1670_);
lean_ctor_set(v___x_1680_, 10, v_cancelTk_x3f_1671_);
lean_ctor_set(v___x_1680_, 11, v_inheritedTraceOptions_1672_);
lean_inc(v_ref_1674_);
v___x_1681_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v_currRecDepth_1673_);
lean_ctor_set(v___x_1681_, 2, v_ref_1674_);
lean_ctor_set_uint16(v___x_1681_, sizeof(void*)*3, v___x_1643_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*3 + 2, v_suppressElabErrors_1675_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*3 + 3, v_checkDeprecated_1676_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*3 + 4, v_isRecordingDeps_1677_);
v___x_1682_ = l_Lean_Language_SnapshotTree_trace(v___x_1625_, v___x_1681_, v___x_1661_);
lean_dec_ref_known(v___x_1681_, 3);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1683_; lean_object* v_traceState_1684_; lean_object* v_traces_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1682_, 1);
lean_dec_ref(v___x_1630_);
v___x_1683_ = lean_st_ref_get(v___x_1661_);
lean_dec(v___x_1661_);
v_traceState_1684_ = lean_ctor_get(v___x_1683_, 4);
lean_inc_ref(v_traceState_1684_);
lean_dec(v___x_1683_);
v_traces_1685_ = lean_ctor_get(v_traceState_1684_, 0);
lean_inc_ref(v_traces_1685_);
lean_dec_ref(v_traceState_1684_);
v___x_1686_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1637_);
lean_inc_ref(v_fileMap_1638_);
v___x_1687_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1638_, v_pos_1626_, v_fileName_1637_, v_val_1627_, v_traces_1685_, v___x_1686_);
lean_dec_ref(v_traces_1685_);
v___x_1688_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1689_, 0, v___x_1628_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
lean_ctor_set(v___x_1689_, 2, v___x_1629_);
lean_ctor_set(v___x_1689_, 3, v___x_1624_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*4, v_val_1627_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___x_1651_);
v___x_1691_ = lean_task_pure(v___x_1690_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref_known(v___x_1682_, 1);
lean_dec(v___x_1661_);
lean_dec(v___x_1629_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v___x_1624_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1630_);
lean_ctor_set(v___x_1692_, 1, v___x_1651_);
v___x_1693_ = lean_task_pure(v___x_1692_);
return v___x_1693_;
}
}
v___jp_1696_:
{
lean_object* v___x_1698_; lean_object* v_env_1699_; lean_object* v_nextMacroScope_1700_; lean_object* v_ngen_1701_; lean_object* v_auxDeclNGen_1702_; lean_object* v_traceState_1703_; lean_object* v_recordedDeps_1704_; lean_object* v_messages_1705_; lean_object* v_infoState_1706_; lean_object* v_snapshotTasks_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1716_; 
v___x_1698_ = lean_st_ref_take(v___x_1661_);
v_env_1699_ = lean_ctor_get(v___x_1698_, 0);
v_nextMacroScope_1700_ = lean_ctor_get(v___x_1698_, 1);
v_ngen_1701_ = lean_ctor_get(v___x_1698_, 2);
v_auxDeclNGen_1702_ = lean_ctor_get(v___x_1698_, 3);
v_traceState_1703_ = lean_ctor_get(v___x_1698_, 4);
v_recordedDeps_1704_ = lean_ctor_get(v___x_1698_, 6);
v_messages_1705_ = lean_ctor_get(v___x_1698_, 7);
v_infoState_1706_ = lean_ctor_get(v___x_1698_, 8);
v_snapshotTasks_1707_ = lean_ctor_get(v___x_1698_, 9);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v___x_1698_, 5);
lean_dec(v_unused_1717_);
v___x_1709_ = v___x_1698_;
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_snapshotTasks_1707_);
lean_inc(v_infoState_1706_);
lean_inc(v_messages_1705_);
lean_inc(v_recordedDeps_1704_);
lean_inc(v_traceState_1703_);
lean_inc(v_auxDeclNGen_1702_);
lean_inc(v_ngen_1701_);
lean_inc(v_nextMacroScope_1700_);
lean_inc(v_env_1699_);
lean_dec(v___x_1698_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = l_Lean_Kernel_enableDiag(v_env_1699_, v___y_1697_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 5, v___x_1650_);
lean_ctor_set(v___x_1709_, 0, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_nextMacroScope_1700_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_ngen_1701_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_auxDeclNGen_1702_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v_traceState_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 5, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1715_, 6, v_recordedDeps_1704_);
lean_ctor_set(v_reuseFailAlloc_1715_, 7, v_messages_1705_);
lean_ctor_set(v_reuseFailAlloc_1715_, 8, v_infoState_1706_);
lean_ctor_set(v_reuseFailAlloc_1715_, 9, v_snapshotTasks_1707_);
v___x_1713_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_st_ref_put(v___x_1661_, v___x_1713_);
lean_inc(v___x_1619_);
lean_inc(v___x_1618_);
lean_inc_ref(v_fileMap_1638_);
lean_inc_ref(v_fileName_1637_);
v_fileName_1663_ = v_fileName_1637_;
v_fileMap_1664_ = v_fileMap_1638_;
v_currNamespace_1665_ = v___x_1618_;
v_openDecls_1666_ = v___x_1639_;
v_initHeartbeats_1667_ = v___x_1619_;
v_maxHeartbeats_1668_ = v___x_1640_;
v_quotContext_1669_ = v___x_1618_;
v_currMacroScope_1670_ = v___x_1641_;
v_cancelTk_x3f_1671_ = v___x_1632_;
v_inheritedTraceOptions_1672_ = v___x_1694_;
v_currRecDepth_1673_ = v___x_1619_;
v_ref_1674_ = v___x_1642_;
v_suppressElabErrors_1675_ = v_val_1627_;
v_checkDeprecated_1676_ = v___x_1644_;
v_isRecordingDeps_1677_ = v_val_1627_;
goto v___jp_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1724_ = _args[0];
lean_object* v_opts_1725_ = _args[1];
lean_object* v___x_1726_ = _args[2];
lean_object* v___x_1727_ = _args[3];
lean_object* v___x_1728_ = _args[4];
lean_object* v___x_1729_ = _args[5];
lean_object* v___x_1730_ = _args[6];
lean_object* v_env_1731_ = _args[7];
lean_object* v___x_1732_ = _args[8];
lean_object* v___x_1733_ = _args[9];
lean_object* v_pos_1734_ = _args[10];
lean_object* v_val_1735_ = _args[11];
lean_object* v___x_1736_ = _args[12];
lean_object* v___x_1737_ = _args[13];
lean_object* v___x_1738_ = _args[14];
lean_object* v___x_1739_ = _args[15];
lean_object* v___x_1740_ = _args[16];
lean_object* v___x_1741_ = _args[17];
lean_object* v_x_1742_ = _args[18];
lean_object* v___y_1743_ = _args[19];
_start:
{
size_t v___x_37168__boxed_1744_; uint8_t v___x_37169__boxed_1745_; uint8_t v_val_37172__boxed_1746_; uint8_t v___x_37178__boxed_1747_; lean_object* v_res_1748_; 
v___x_37168__boxed_1744_ = lean_unbox_usize(v___x_1729_);
lean_dec(v___x_1729_);
v___x_37169__boxed_1745_ = lean_unbox(v___x_1730_);
v_val_37172__boxed_1746_ = lean_unbox(v_val_1735_);
v___x_37178__boxed_1747_ = lean_unbox(v___x_1741_);
v_res_1748_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1724_, v_opts_1725_, v___x_1726_, v___x_1727_, v___x_1728_, v___x_37168__boxed_1744_, v___x_37169__boxed_1745_, v_env_1731_, v___x_1732_, v___x_1733_, v_pos_1734_, v_val_37172__boxed_1746_, v___x_1736_, v___x_1737_, v___x_1738_, v___x_1739_, v___x_1740_, v___x_37178__boxed_1747_, v_x_1742_);
lean_dec(v___x_1739_);
lean_dec(v_pos_1734_);
lean_dec(v___x_1728_);
lean_dec_ref(v_a_1724_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1749_, lean_object* v___x_1750_, lean_object* v_parserState_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_toProcessingContext_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_toProcessingContext_1753_ = lean_ctor_get(v_a_1749_, 0);
v___x_1754_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1753_);
v___x_1755_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1753_, v___x_1750_, v_parserState_1751_, v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1756_, lean_object* v___x_1757_, lean_object* v_parserState_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1756_, v___x_1757_, v_parserState_1758_, v_x_1759_);
lean_dec_ref(v_a_1756_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1762_, size_t v_i_1763_, size_t v_stop_1764_, lean_object* v_b_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_eq(v_i_1763_, v_stop_1764_);
if (v___x_1767_ == 0)
{
lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; 
v___f_1768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1769_ = lean_array_uget_borrowed(v_as_1762_, v_i_1763_);
lean_inc(v___x_1769_);
v___x_1770_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1768_, v___x_1769_);
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_add(v_i_1763_, v___x_1771_);
v_i_1763_ = v___x_1772_;
v_b_1765_ = v___x_1770_;
goto _start;
}
else
{
return v_b_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1774_, lean_object* v_i_1775_, lean_object* v_stop_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_){
_start:
{
size_t v_i_boxed_1779_; size_t v_stop_boxed_1780_; lean_object* v_res_1781_; 
v_i_boxed_1779_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_stop_boxed_1780_ = lean_unbox_usize(v_stop_1776_);
lean_dec(v_stop_1776_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1774_, v_i_boxed_1779_, v_stop_boxed_1780_, v_b_1777_);
lean_dec_ref(v_as_1774_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1782_, lean_object* v_stx_1783_, lean_object* v_revCmds_1784_, lean_object* v_newParserState_1785_, lean_object* v_val_1786_, lean_object* v_sync_1787_, lean_object* v_val_1788_, lean_object* v_a_1789_, lean_object* v_oldNext_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_sync_boxed_1792_; lean_object* v_res_1793_; 
v_sync_boxed_1792_ = lean_unbox(v_sync_1787_);
v_res_1793_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1782_, v_stx_1783_, v_revCmds_1784_, v_newParserState_1785_, v_val_1786_, v_sync_boxed_1792_, v_val_1788_, v_a_1789_, v_oldNext_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1794_, lean_object* v_stx_1795_, lean_object* v_revCmds_1796_, lean_object* v_newParserState_1797_, lean_object* v_val_1798_, uint8_t v_sync_1799_, lean_object* v_val_1800_, lean_object* v_a_1801_, lean_object* v_oldResult_1802_){
_start:
{
lean_object* v_task_1804_; lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; 
v_task_1804_ = lean_ctor_get(v_val_1794_, 3);
lean_inc_ref(v_task_1804_);
lean_dec_ref(v_val_1794_);
v___x_1805_ = lean_box(v_sync_1799_);
lean_inc_ref(v_a_1801_);
v___f_1806_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1806_, 0, v_oldResult_1802_);
lean_closure_set(v___f_1806_, 1, v_stx_1795_);
lean_closure_set(v___f_1806_, 2, v_revCmds_1796_);
lean_closure_set(v___f_1806_, 3, v_newParserState_1797_);
lean_closure_set(v___f_1806_, 4, v_val_1798_);
lean_closure_set(v___f_1806_, 5, v___x_1805_);
lean_closure_set(v___f_1806_, 6, v_val_1800_);
lean_closure_set(v___f_1806_, 7, v_a_1801_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = 1;
v___x_1809_ = l_BaseIO_chainTask___redArg(v_task_1804_, v___f_1806_, v___x_1807_, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1810_, lean_object* v_stx_1811_, lean_object* v_revCmds_1812_, lean_object* v_newParserState_1813_, lean_object* v_val_1814_, lean_object* v_sync_1815_, lean_object* v_val_1816_, lean_object* v_a_1817_, lean_object* v_oldResult_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v_sync_boxed_1820_; lean_object* v_res_1821_; 
v_sync_boxed_1820_ = lean_unbox(v_sync_1815_);
v_res_1821_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1810_, v_stx_1811_, v_revCmds_1812_, v_newParserState_1813_, v_val_1814_, v_sync_boxed_1820_, v_val_1816_, v_a_1817_, v_oldResult_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1821_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1830_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1831_ = l_Lean_Name_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1835_, lean_object* v_val_1836_, lean_object* v_fst_1837_, lean_object* v_revCmds_1838_, lean_object* v_fst_1839_, uint8_t v_val_1840_, lean_object* v_a_1841_, lean_object* v_snd_1842_, lean_object* v___x_1843_, uint8_t v___x_1844_, lean_object* v_fst_1845_, lean_object* v_val_1846_, lean_object* v_val_1847_, lean_object* v___x_1848_, lean_object* v___f_1849_, lean_object* v___f_1850_, lean_object* v___f_1851_, lean_object* v_pos_1852_, lean_object* v_cmdState_1853_, lean_object* v_val_1854_, lean_object* v___x_1855_, lean_object* v_opts_1856_, lean_object* v___x_1857_, lean_object* v_snd_1858_, lean_object* v_prom_1859_, lean_object* v_old_x3f_1860_, lean_object* v_parseCancelTk_1861_, lean_object* v_next_x3f_1862_){
_start:
{
lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v_snapshotTasks_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v_traceTask_1871_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; size_t v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v_env_1912_; lean_object* v_messages_1913_; lean_object* v_scopes_1914_; lean_object* v_infoState_1915_; lean_object* v_traceState_1916_; lean_object* v_snapshotTasks_1917_; lean_object* v_codeQualityEntryTasks_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v_reportedCmdState_1922_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; size_t v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v_reportedCmdState_1979_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; size_t v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2037_; 
if (lean_obj_tag(v_next_x3f_1862_) == 0)
{
lean_object* v___x_2090_; 
lean_dec_ref(v_parseCancelTk_1861_);
v___x_2090_ = lean_box(0);
v___y_2037_ = v___x_2090_;
goto v___jp_2036_;
}
else
{
lean_object* v_toProcessingContext_2091_; lean_object* v_val_2092_; lean_object* v_pos_2093_; lean_object* v_endPos_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_toProcessingContext_2091_ = lean_ctor_get(v_a_1841_, 0);
v_val_2092_ = lean_ctor_get(v_next_x3f_1862_, 0);
v_pos_2093_ = lean_ctor_get(v_fst_1839_, 0);
v_endPos_2094_ = lean_ctor_get(v_toProcessingContext_2091_, 3);
v___x_2095_ = lean_box(0);
lean_inc(v_endPos_2094_);
lean_inc(v_pos_2093_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v_pos_2093_);
lean_ctor_set(v___x_2096_, 1, v_endPos_2094_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_parseCancelTk_1861_);
v___x_2099_ = l_IO_Promise_result_x21___redArg(v_val_2092_);
v___x_2100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2095_);
lean_ctor_set(v___x_2100_, 1, v___x_2097_);
lean_ctor_set(v___x_2100_, 2, v___x_2098_);
lean_ctor_set(v___x_2100_, 3, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
v___y_2037_ = v___x_2101_;
goto v___jp_2036_;
}
v___jp_1864_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1872_, 0, v___y_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1835_);
lean_ctor_set(v___x_1872_, 2, v___y_1870_);
lean_ctor_set(v___x_1872_, 3, v_traceTask_1871_);
v___x_1873_ = lean_array_push(v_snapshotTasks_1867_, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___y_1868_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_io_promise_resolve(v___x_1874_, v_val_1836_);
if (lean_obj_tag(v_next_x3f_1862_) == 1)
{
lean_object* v_val_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_val_1876_ = lean_ctor_get(v_next_x3f_1862_, 0);
lean_inc(v_val_1876_);
lean_dec_ref_known(v_next_x3f_1862_, 1);
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_fst_1837_);
lean_ctor_set(v___x_1878_, 1, v_revCmds_1838_);
v___x_1879_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1877_, v_fst_1839_, v___y_1866_, v_val_1876_, v_val_1840_, v___y_1865_, v___x_1878_, v_a_1841_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; 
lean_dec_ref(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_next_x3f_1862_);
lean_dec_ref(v_fst_1839_);
lean_dec(v_revCmds_1838_);
lean_dec(v_fst_1837_);
v___x_1880_ = lean_box(0);
return v___x_1880_;
}
}
v___jp_1881_:
{
lean_object* v_snapshotTasks_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_snapshotTasks_1888_ = lean_ctor_get(v___y_1884_, 10);
lean_inc_ref(v_snapshotTasks_1888_);
v___x_1889_ = lean_mk_empty_array_with_capacity(v___y_1883_);
lean_dec(v___y_1883_);
lean_inc_ref(v___y_1885_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___y_1885_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_task_pure(v___x_1890_);
v___y_1865_ = v___y_1882_;
v___y_1866_ = v___y_1884_;
v_snapshotTasks_1867_ = v_snapshotTasks_1888_;
v___y_1868_ = v___y_1885_;
v___y_1869_ = v___y_1886_;
v___y_1870_ = v___y_1887_;
v_traceTask_1871_ = v___x_1891_;
goto v___jp_1864_;
}
v___jp_1892_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_opts_1932_; uint8_t v_hasTrace_1933_; 
v___x_1923_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1913_);
v___x_1924_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1924_, 0, v___y_1920_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
lean_ctor_set(v___x_1924_, 2, v___y_1908_);
lean_ctor_set(v___x_1924_, 3, v_traceState_1916_);
lean_ctor_set_uint8(v___x_1924_, sizeof(void*)*4, v_val_1840_);
v___x_1925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v_reportedCmdState_1922_);
lean_ctor_set(v___x_1925_, 2, v_codeQualityEntryTasks_1918_);
v___x_1926_ = lean_io_promise_resolve(v___x_1925_, v_val_1847_);
v___x_1927_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1915_);
lean_inc(v___y_1902_);
v___x_1928_ = l_BaseIO_chainTask___redArg(v___x_1927_, v___y_1921_, v___y_1902_, v___x_1844_);
v___x_1929_ = l_Lean_inheritedTraceOptions;
v___x_1930_ = lean_st_ref_get(v___x_1929_);
v___x_1931_ = l_List_head_x21___redArg(v___x_1848_, v_scopes_1914_);
lean_dec(v_scopes_1914_);
lean_dec_ref(v___x_1848_);
v_opts_1932_ = lean_ctor_get(v___x_1931_, 1);
lean_inc_ref(v_opts_1932_);
lean_dec(v___x_1931_);
v_hasTrace_1933_ = lean_ctor_get_uint8(v_opts_1932_, sizeof(void*)*1);
if (v_hasTrace_1933_ == 0)
{
lean_dec_ref(v_opts_1932_);
lean_dec(v___x_1930_);
lean_dec_ref(v_snapshotTasks_1917_);
lean_dec_ref(v_env_1912_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1893_);
lean_dec(v_pos_1852_);
lean_dec_ref(v___f_1851_);
lean_dec_ref(v___f_1850_);
lean_dec_ref(v___f_1849_);
lean_dec(v___x_1843_);
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1902_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1904_;
v___y_1886_ = v___y_1905_;
v___y_1887_ = v___y_1919_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1935_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1930_, v_opts_1932_, v___x_1934_);
lean_dec(v___x_1930_);
if (v___x_1935_ == 0)
{
lean_dec_ref(v_opts_1932_);
lean_dec_ref(v_snapshotTasks_1917_);
lean_dec_ref(v_env_1912_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1893_);
lean_dec(v_pos_1852_);
lean_dec_ref(v___f_1851_);
lean_dec_ref(v___f_1850_);
lean_dec_ref(v___f_1849_);
lean_dec(v___x_1843_);
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1902_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1904_;
v___y_1886_ = v___y_1905_;
v___y_1887_ = v___y_1919_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_inc_n(v___y_1902_, 3);
v___x_1936_ = lean_task_map(v___f_1849_, v___y_1906_, v___y_1902_, v___x_1844_);
lean_inc_n(v___y_1919_, 3);
lean_inc_n(v___y_1903_, 2);
lean_inc_n(v___y_1910_, 2);
v___x_1937_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1910_);
lean_ctor_set(v___x_1937_, 1, v___y_1903_);
lean_ctor_set(v___x_1937_, 2, v___y_1919_);
lean_ctor_set(v___x_1937_, 3, v___x_1936_);
v___x_1938_ = lean_task_map(v___f_1850_, v___y_1907_, v___y_1902_, v___x_1844_);
v___x_1939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1910_);
lean_ctor_set(v___x_1939_, 1, v___y_1903_);
lean_ctor_set(v___x_1939_, 2, v___y_1919_);
lean_ctor_set(v___x_1939_, 3, v___x_1938_);
v___x_1940_ = lean_task_map(v___f_1851_, v___y_1901_, v___y_1902_, v___x_1844_);
v___x_1941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1941_, 0, v___y_1910_);
lean_ctor_set(v___x_1941_, 1, v___y_1903_);
lean_ctor_set(v___x_1941_, 2, v___y_1919_);
lean_ctor_set(v___x_1941_, 3, v___x_1940_);
v___x_1942_ = lean_unsigned_to_nat(3u);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
v___x_1944_ = lean_array_push(v___x_1943_, v___x_1937_);
v___x_1945_ = lean_array_push(v___x_1944_, v___x_1939_);
v___x_1946_ = lean_array_push(v___x_1945_, v___x_1941_);
v___x_1947_ = l_Array_append___redArg(v___x_1946_, v_snapshotTasks_1917_);
lean_inc_ref(v___y_1904_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___y_1904_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_box_usize(v___y_1899_);
v___x_1950_ = lean_box(v___x_1844_);
v___x_1951_ = lean_box(v_val_1840_);
v___x_1952_ = lean_box(v___x_1935_);
lean_inc_ref(v___x_1948_);
lean_inc_ref(v___y_1894_);
lean_inc_ref(v_a_1841_);
v___f_1953_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1953_, 0, v_a_1841_);
lean_closure_set(v___f_1953_, 1, v_opts_1932_);
lean_closure_set(v___f_1953_, 2, v___x_1843_);
lean_closure_set(v___f_1953_, 3, v___y_1896_);
lean_closure_set(v___f_1953_, 4, v___y_1895_);
lean_closure_set(v___f_1953_, 5, v___x_1949_);
lean_closure_set(v___f_1953_, 6, v___x_1950_);
lean_closure_set(v___f_1953_, 7, v_env_1912_);
lean_closure_set(v___f_1953_, 8, v___y_1894_);
lean_closure_set(v___f_1953_, 9, v___x_1948_);
lean_closure_set(v___f_1953_, 10, v_pos_1852_);
lean_closure_set(v___f_1953_, 11, v___x_1951_);
lean_closure_set(v___f_1953_, 12, v___y_1893_);
lean_closure_set(v___f_1953_, 13, v___y_1898_);
lean_closure_set(v___f_1953_, 14, v___y_1900_);
lean_closure_set(v___f_1953_, 15, v___x_1929_);
lean_closure_set(v___f_1953_, 16, v___y_1897_);
lean_closure_set(v___f_1953_, 17, v___x_1952_);
v___x_1954_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1948_);
v___x_1955_ = lean_io_bind_task(v___x_1954_, v___f_1953_, v___y_1902_, v_val_1840_);
v___y_1865_ = v___y_1909_;
v___y_1866_ = v___y_1911_;
v_snapshotTasks_1867_ = v_snapshotTasks_1917_;
v___y_1868_ = v___y_1904_;
v___y_1869_ = v___y_1905_;
v___y_1870_ = v___y_1919_;
v_traceTask_1871_ = v___x_1955_;
goto v___jp_1864_;
}
}
}
v___jp_1956_:
{
lean_object* v_env_1980_; lean_object* v_messages_1981_; lean_object* v_scopes_1982_; lean_object* v_infoState_1983_; lean_object* v_traceState_1984_; lean_object* v_snapshotTasks_1985_; lean_object* v_codeQualityEntryTasks_1986_; 
v_env_1980_ = lean_ctor_get(v___y_1975_, 0);
lean_inc_ref(v_env_1980_);
v_messages_1981_ = lean_ctor_get(v___y_1975_, 1);
lean_inc_ref(v_messages_1981_);
v_scopes_1982_ = lean_ctor_get(v___y_1975_, 2);
lean_inc(v_scopes_1982_);
v_infoState_1983_ = lean_ctor_get(v___y_1975_, 8);
lean_inc_ref(v_infoState_1983_);
v_traceState_1984_ = lean_ctor_get(v___y_1975_, 9);
lean_inc_ref(v_traceState_1984_);
v_snapshotTasks_1985_ = lean_ctor_get(v___y_1975_, 10);
lean_inc_ref(v_snapshotTasks_1985_);
v_codeQualityEntryTasks_1986_ = lean_ctor_get(v___y_1975_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1986_);
v___y_1893_ = v___y_1958_;
v___y_1894_ = v___y_1957_;
v___y_1895_ = v___y_1960_;
v___y_1896_ = v___y_1959_;
v___y_1897_ = v___y_1962_;
v___y_1898_ = v___y_1961_;
v___y_1899_ = v___y_1963_;
v___y_1900_ = v___y_1964_;
v___y_1901_ = v___y_1965_;
v___y_1902_ = v___y_1966_;
v___y_1903_ = v___y_1967_;
v___y_1904_ = v___y_1968_;
v___y_1905_ = v___y_1969_;
v___y_1906_ = v___y_1970_;
v___y_1907_ = v___y_1971_;
v___y_1908_ = v___y_1972_;
v___y_1909_ = v___y_1973_;
v___y_1910_ = v___y_1974_;
v___y_1911_ = v___y_1975_;
v_env_1912_ = v_env_1980_;
v_messages_1913_ = v_messages_1981_;
v_scopes_1914_ = v_scopes_1982_;
v_infoState_1915_ = v_infoState_1983_;
v_traceState_1916_ = v_traceState_1984_;
v_snapshotTasks_1917_ = v_snapshotTasks_1985_;
v_codeQualityEntryTasks_1918_ = v_codeQualityEntryTasks_1986_;
v___y_1919_ = v___y_1976_;
v___y_1920_ = v___y_1977_;
v___y_1921_ = v___y_1978_;
v_reportedCmdState_1922_ = v_reportedCmdState_1979_;
goto v___jp_1892_;
}
v___jp_1987_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___f_2008_; uint8_t v___x_2009_; 
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___y_2003_);
lean_ctor_set(v___x_2004_, 1, v_val_1846_);
lean_inc_ref(v___y_1996_);
lean_inc_n(v_pos_1852_, 2);
lean_inc(v_revCmds_1838_);
lean_inc(v_fst_1837_);
v___x_2005_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1837_, v_revCmds_1838_, v_cmdState_1853_, v_pos_1852_, v___x_2004_, v___y_1996_, v_a_1841_);
v___x_2006_ = lean_box(v_val_1840_);
v___x_2007_ = lean_box(v___x_1844_);
lean_inc_ref(v_a_1841_);
lean_inc(v___y_1992_);
lean_inc_ref(v___x_1848_);
lean_inc_ref(v___x_2005_);
lean_inc_ref(v___y_1989_);
lean_inc_ref(v___y_1990_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2008_, 0, v___y_1990_);
lean_closure_set(v___f_2008_, 1, v___y_1989_);
lean_closure_set(v___f_2008_, 2, v___x_2006_);
lean_closure_set(v___f_2008_, 3, v_val_1854_);
lean_closure_set(v___f_2008_, 4, v___x_2005_);
lean_closure_set(v___f_2008_, 5, v___x_1848_);
lean_closure_set(v___f_2008_, 6, v___y_1992_);
lean_closure_set(v___f_2008_, 7, v___x_2007_);
lean_closure_set(v___f_2008_, 8, v_a_1841_);
lean_closure_set(v___f_2008_, 9, v_pos_1852_);
lean_closure_set(v___f_2008_, 10, v___x_1855_);
v___x_2009_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1856_, v___x_1857_);
if (v___x_2009_ == 0)
{
lean_inc_ref(v___x_2005_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1994_);
lean_inc(v___y_1995_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1990_);
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1990_;
v___y_1959_ = v___y_1992_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1995_;
v___y_1962_ = v___y_1994_;
v___y_1963_ = v___y_1997_;
v___y_1964_ = v___y_1999_;
v___y_1965_ = v___y_2000_;
v___y_1966_ = v___y_1992_;
v___y_1967_ = v___y_1993_;
v___y_1968_ = v___y_1999_;
v___y_1969_ = v___y_2001_;
v___y_1970_ = v___y_1988_;
v___y_1971_ = v___y_2002_;
v___y_1972_ = v___y_1995_;
v___y_1973_ = v___y_1996_;
v___y_1974_ = v___y_1998_;
v___y_1975_ = v___x_2005_;
v___y_1976_ = v___y_1994_;
v___y_1977_ = v___y_1990_;
v___y_1978_ = v___f_2008_;
v_reportedCmdState_1979_ = v___x_2005_;
goto v___jp_1956_;
}
else
{
uint8_t v___x_2010_; 
lean_inc(v_fst_1837_);
v___x_2010_ = l_Lean_Parser_isTerminalCommand(v_fst_1837_);
if (v___x_2010_ == 0)
{
lean_object* v_env_2011_; lean_object* v_messages_2012_; lean_object* v_scopes_2013_; lean_object* v_infoState_2014_; lean_object* v_traceState_2015_; lean_object* v_snapshotTasks_2016_; lean_object* v_codeQualityEntryTasks_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_env_2011_ = lean_ctor_get(v___x_2005_, 0);
lean_inc_ref_n(v_env_2011_, 2);
v_messages_2012_ = lean_ctor_get(v___x_2005_, 1);
lean_inc_ref(v_messages_2012_);
v_scopes_2013_ = lean_ctor_get(v___x_2005_, 2);
lean_inc(v_scopes_2013_);
v_infoState_2014_ = lean_ctor_get(v___x_2005_, 8);
lean_inc_ref(v_infoState_2014_);
v_traceState_2015_ = lean_ctor_get(v___x_2005_, 9);
lean_inc_ref(v_traceState_2015_);
v_snapshotTasks_2016_ = lean_ctor_get(v___x_2005_, 10);
lean_inc_ref(v_snapshotTasks_2016_);
v_codeQualityEntryTasks_2017_ = lean_ctor_get(v___x_2005_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2017_);
v___x_2018_ = lean_mk_empty_array_with_capacity(v___y_1991_);
lean_inc_ref(v___x_2018_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_inc_n(v___y_1992_, 4);
v___x_2020_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v___x_2018_);
lean_ctor_set(v___x_2020_, 2, v___y_1992_);
lean_ctor_set(v___x_2020_, 3, v___y_1992_);
lean_ctor_set_usize(v___x_2020_, 4, v___y_1997_);
v___x_2021_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2020_, 2);
v___x_2022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
lean_ctor_set(v___x_2022_, 1, v___x_2020_);
lean_ctor_set(v___x_2022_, 2, v___x_2021_);
v___x_2023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2024_ = l_Lean_Options_empty;
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_mk_empty_array_with_capacity(v___y_1992_);
lean_inc_ref_n(v___x_2026_, 3);
lean_inc_n(v___x_1843_, 2);
v___x_2027_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2027_, 0, v___x_2023_);
lean_ctor_set(v___x_2027_, 1, v___x_2024_);
lean_ctor_set(v___x_2027_, 2, v___x_1843_);
lean_ctor_set(v___x_2027_, 3, v___x_2025_);
lean_ctor_set(v___x_2027_, 4, v___x_2025_);
lean_ctor_set(v___x_2027_, 5, v___x_2026_);
lean_ctor_set(v___x_2027_, 6, v___x_2026_);
lean_ctor_set(v___x_2027_, 7, v___x_2025_);
lean_ctor_set(v___x_2027_, 8, v___x_2025_);
lean_ctor_set(v___x_2027_, 9, v___x_2025_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*10, v_val_1840_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*10 + 1, v_val_1840_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*10 + 2, v_val_1840_);
v___x_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2025_);
v___x_2029_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2030_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2031_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1843_);
v___x_2032_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2033_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_ctor_set(v___x_2033_, 2, v___x_2020_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*3, v___x_1844_);
v___x_2034_ = lean_box(0);
lean_inc_ref(v___y_1989_);
v___x_2035_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2035_, 0, v_env_2011_);
lean_ctor_set(v___x_2035_, 1, v___x_2022_);
lean_ctor_set(v___x_2035_, 2, v___x_2028_);
lean_ctor_set(v___x_2035_, 3, v___x_2021_);
lean_ctor_set(v___x_2035_, 4, v___x_2029_);
lean_ctor_set(v___x_2035_, 5, v___y_1992_);
lean_ctor_set(v___x_2035_, 6, v___x_2030_);
lean_ctor_set(v___x_2035_, 7, v___x_2031_);
lean_ctor_set(v___x_2035_, 8, v___x_2033_);
lean_ctor_set(v___x_2035_, 9, v___y_1989_);
lean_ctor_set(v___x_2035_, 10, v___x_2026_);
lean_ctor_set(v___x_2035_, 11, v___x_2034_);
lean_ctor_set(v___x_2035_, 12, v___x_2026_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1990_);
v___y_1893_ = v___y_1990_;
v___y_1894_ = v___y_1989_;
v___y_1895_ = v___y_1991_;
v___y_1896_ = v___y_1992_;
v___y_1897_ = v___y_1994_;
v___y_1898_ = v___y_1995_;
v___y_1899_ = v___y_1997_;
v___y_1900_ = v___y_1999_;
v___y_1901_ = v___y_2000_;
v___y_1902_ = v___y_1992_;
v___y_1903_ = v___y_1993_;
v___y_1904_ = v___y_1999_;
v___y_1905_ = v___y_2001_;
v___y_1906_ = v___y_1988_;
v___y_1907_ = v___y_2002_;
v___y_1908_ = v___y_1995_;
v___y_1909_ = v___y_1996_;
v___y_1910_ = v___y_1998_;
v___y_1911_ = v___x_2005_;
v_env_1912_ = v_env_2011_;
v_messages_1913_ = v_messages_2012_;
v_scopes_1914_ = v_scopes_2013_;
v_infoState_1915_ = v_infoState_2014_;
v_traceState_1916_ = v_traceState_2015_;
v_snapshotTasks_1917_ = v_snapshotTasks_2016_;
v_codeQualityEntryTasks_1918_ = v_codeQualityEntryTasks_2017_;
v___y_1919_ = v___y_1994_;
v___y_1920_ = v___y_1990_;
v___y_1921_ = v___f_2008_;
v_reportedCmdState_1922_ = v___x_2035_;
goto v___jp_1892_;
}
else
{
lean_inc_ref(v___x_2005_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1994_);
lean_inc(v___y_1995_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1990_);
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1990_;
v___y_1959_ = v___y_1992_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1995_;
v___y_1962_ = v___y_1994_;
v___y_1963_ = v___y_1997_;
v___y_1964_ = v___y_1999_;
v___y_1965_ = v___y_2000_;
v___y_1966_ = v___y_1992_;
v___y_1967_ = v___y_1993_;
v___y_1968_ = v___y_1999_;
v___y_1969_ = v___y_2001_;
v___y_1970_ = v___y_1988_;
v___y_1971_ = v___y_2002_;
v___y_1972_ = v___y_1995_;
v___y_1973_ = v___y_1996_;
v___y_1974_ = v___y_1998_;
v___y_1975_ = v___x_2005_;
v___y_1976_ = v___y_1994_;
v___y_1977_ = v___y_1990_;
v___y_1978_ = v___f_2008_;
v_reportedCmdState_1979_ = v___x_2005_;
goto v___jp_1956_;
}
}
}
v___jp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2038_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1842_);
v___x_2039_ = l_IO_CancelToken_new();
v___x_2040_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1843_);
v___x_2041_ = l_Lean_Name_str___override(v___x_1843_, v___x_2040_);
v___x_2042_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2043_ = l_Lean_Name_str___override(v___x_2041_, v___x_2042_);
v___x_2044_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2045_ = l_Lean_Name_str___override(v___x_2043_, v___x_2044_);
v___x_2046_ = l_Lean_Name_str___override(v___x_2045_, v___x_2042_);
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = l_Lean_Name_num___override(v___x_2046_, v___x_2047_);
v___x_2049_ = l_Lean_Name_str___override(v___x_2048_, v___x_2042_);
v___x_2050_ = l_Lean_Name_str___override(v___x_2049_, v___x_2044_);
v___x_2051_ = l_Lean_Name_str___override(v___x_2050_, v___x_2042_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2053_ = l_Lean_Name_str___override(v___x_2051_, v___x_2052_);
v___x_2054_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2055_ = l_Lean_Name_str___override(v___x_2053_, v___x_2054_);
v___x_2056_ = l_Lean_Name_toString(v___x_2055_, v___x_1844_);
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_unsigned_to_nat(32u);
v___x_2059_ = ((size_t)5ULL);
v___x_2060_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2056_, 2);
v___x_2061_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2061_, 0, v___x_2056_);
lean_ctor_set(v___x_2061_, 1, v___x_2038_);
lean_ctor_set(v___x_2061_, 2, v___x_2057_);
lean_ctor_set(v___x_2061_, 3, v___x_2060_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*4, v_val_1840_);
v___x_2062_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2063_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2063_, 0, v___x_2056_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
lean_ctor_set(v___x_2063_, 2, v___x_2057_);
lean_ctor_set(v___x_2063_, 3, v___x_2060_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*4, v_val_1840_);
lean_inc(v_fst_1845_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_fst_1845_);
v___x_2065_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2064_);
lean_inc_ref(v___x_2039_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2039_);
v___x_2067_ = l_IO_Promise_result_x21___redArg(v_val_1846_);
lean_inc_ref(v___x_2067_);
lean_inc(v___x_2065_);
lean_inc_ref_n(v___x_2064_, 3);
v___x_2068_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2064_);
lean_ctor_set(v___x_2068_, 1, v___x_2065_);
lean_ctor_set(v___x_2068_, 2, v___x_2066_);
lean_ctor_set(v___x_2068_, 3, v___x_2067_);
v___x_2069_ = l_IO_Promise_result_x21___redArg(v_val_1847_);
lean_inc_ref(v___x_2069_);
lean_inc_n(v___x_1835_, 3);
v___x_2070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2064_);
lean_ctor_set(v___x_2070_, 1, v___x_1835_);
lean_ctor_set(v___x_2070_, 2, v___x_2057_);
lean_ctor_set(v___x_2070_, 3, v___x_2069_);
v___x_2071_ = l_IO_Promise_result_x21___redArg(v_val_1854_);
lean_inc_ref(v___x_2071_);
v___x_2072_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2064_);
lean_ctor_set(v___x_2072_, 1, v___x_1835_);
lean_ctor_set(v___x_2072_, 2, v___x_2057_);
lean_ctor_set(v___x_2072_, 3, v___x_2071_);
v___x_2073_ = l_IO_Promise_result_x21___redArg(v_val_1836_);
v___x_2074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2057_);
lean_ctor_set(v___x_2074_, 1, v___x_1835_);
lean_ctor_set(v___x_2074_, 2, v___x_2057_);
lean_ctor_set(v___x_2074_, 3, v___x_2073_);
lean_inc_ref(v___x_2063_);
v___x_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2063_);
lean_ctor_set(v___x_2075_, 1, v___x_2068_);
lean_ctor_set(v___x_2075_, 2, v___x_2070_);
lean_ctor_set(v___x_2075_, 3, v___x_2072_);
lean_ctor_set(v___x_2075_, 4, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2061_);
lean_ctor_set(v___x_2076_, 1, v_fst_1845_);
lean_ctor_set(v___x_2076_, 2, v_snd_1858_);
lean_ctor_set(v___x_2076_, 3, v___x_2075_);
lean_ctor_set(v___x_2076_, 4, v___y_2037_);
v___x_2077_ = lean_io_promise_resolve(v___x_2076_, v_prom_1859_);
if (lean_obj_tag(v_old_x3f_1860_) == 0)
{
v___y_1988_ = v___x_2067_;
v___y_1989_ = v___x_2060_;
v___y_1990_ = v___x_2056_;
v___y_1991_ = v___x_2058_;
v___y_1992_ = v___x_2047_;
v___y_1993_ = v___x_2065_;
v___y_1994_ = v___x_2057_;
v___y_1995_ = v___x_2057_;
v___y_1996_ = v___x_2039_;
v___y_1997_ = v___x_2059_;
v___y_1998_ = v___x_2064_;
v___y_1999_ = v___x_2063_;
v___y_2000_ = v___x_2071_;
v___y_2001_ = v___x_2057_;
v___y_2002_ = v___x_2069_;
v___y_2003_ = v___x_2057_;
goto v___jp_1987_;
}
else
{
lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2089_; 
v_val_2078_ = lean_ctor_get(v_old_x3f_1860_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_old_x3f_1860_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2080_ = v_old_x3f_1860_;
v_isShared_2081_ = v_isSharedCheck_2089_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_dec(v_old_x3f_1860_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2089_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_elabSnap_2082_; lean_object* v_stx_2083_; lean_object* v_elabSnap_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v_elabSnap_2082_ = lean_ctor_get(v_val_2078_, 3);
lean_inc_ref(v_elabSnap_2082_);
v_stx_2083_ = lean_ctor_get(v_val_2078_, 1);
lean_inc(v_stx_2083_);
lean_dec(v_val_2078_);
v_elabSnap_2084_ = lean_ctor_get(v_elabSnap_2082_, 1);
lean_inc_ref(v_elabSnap_2084_);
lean_dec_ref(v_elabSnap_2082_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_stx_2083_);
lean_ctor_set(v___x_2085_, 1, v_elabSnap_2084_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2085_);
v___x_2087_ = v___x_2080_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
v___y_1988_ = v___x_2067_;
v___y_1989_ = v___x_2060_;
v___y_1990_ = v___x_2056_;
v___y_1991_ = v___x_2058_;
v___y_1992_ = v___x_2047_;
v___y_1993_ = v___x_2065_;
v___y_1994_ = v___x_2057_;
v___y_1995_ = v___x_2057_;
v___y_1996_ = v___x_2039_;
v___y_1997_ = v___x_2059_;
v___y_1998_ = v___x_2064_;
v___y_1999_ = v___x_2063_;
v___y_2000_ = v___x_2071_;
v___y_2001_ = v___x_2057_;
v___y_2002_ = v___x_2069_;
v___y_2003_ = v___x_2087_;
goto v___jp_1987_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2103_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2107_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2108_, lean_object* v_revCmds_2109_, lean_object* v_fst_2110_, uint8_t v_val_2111_, lean_object* v_a_2112_, lean_object* v_snd_2113_, lean_object* v___x_2114_, uint8_t v___x_2115_, lean_object* v___x_2116_, lean_object* v___f_2117_, lean_object* v___f_2118_, lean_object* v___f_2119_, lean_object* v_pos_2120_, lean_object* v_cmdState_2121_, lean_object* v___x_2122_, lean_object* v_opts_2123_, lean_object* v_prom_2124_, lean_object* v_old_x3f_2125_, lean_object* v_parseCancelTk_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v_snapshotTasks_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v_traceTask_2141_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; size_t v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v_env_2186_; lean_object* v_messages_2187_; lean_object* v_scopes_2188_; lean_object* v_infoState_2189_; lean_object* v_traceState_2190_; lean_object* v_snapshotTasks_2191_; lean_object* v_codeQualityEntryTasks_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v_reportedCmdState_2196_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; size_t v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v_reportedCmdState_2255_; lean_object* v___x_2263_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; size_t v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v_fst_2394_; lean_object* v_snd_2395_; uint8_t v___x_2407_; 
v___x_2128_ = lean_io_promise_new();
v___x_2129_ = lean_io_promise_new();
v___x_2130_ = lean_io_promise_new();
v___x_2131_ = lean_io_promise_new();
v___x_2263_ = l_Lean_internal_cmdlineSnapshots;
v___x_2407_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2123_, v___x_2263_);
if (v___x_2407_ == 0)
{
lean_inc_ref(v_fst_2110_);
lean_inc(v_fst_2108_);
v_fst_2394_ = v_fst_2108_;
v_snd_2395_ = v_fst_2110_;
goto v___jp_2393_;
}
else
{
uint8_t v___x_2408_; 
lean_inc(v_fst_2108_);
v___x_2408_ = l_Lean_Parser_isTerminalCommand(v_fst_2108_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_box(0);
v___x_2410_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2394_ = v___x_2409_;
v_snd_2395_ = v___x_2410_;
goto v___jp_2393_;
}
else
{
lean_inc_ref(v_fst_2110_);
lean_inc(v_fst_2108_);
v_fst_2394_ = v_fst_2108_;
v_snd_2395_ = v_fst_2110_;
goto v___jp_2393_;
}
}
v___jp_2132_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2142_, 0, v___y_2134_);
lean_ctor_set(v___x_2142_, 1, v___y_2136_);
lean_ctor_set(v___x_2142_, 2, v___y_2135_);
lean_ctor_set(v___x_2142_, 3, v_traceTask_2141_);
v___x_2143_ = lean_array_push(v_snapshotTasks_2138_, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___y_2140_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_io_promise_resolve(v___x_2144_, v___x_2131_);
lean_dec(v___x_2131_);
if (lean_obj_tag(v___y_2133_) == 1)
{
lean_object* v_val_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_val_2146_ = lean_ctor_get(v___y_2133_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v___y_2133_, 1);
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_fst_2108_);
lean_ctor_set(v___x_2148_, 1, v_revCmds_2109_);
v___x_2149_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2147_, v_fst_2110_, v___y_2137_, v_val_2146_, v_val_2111_, v___y_2139_, v___x_2148_, v_a_2112_);
return v___x_2149_;
}
else
{
lean_object* v___x_2150_; 
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2133_);
lean_dec_ref(v_fst_2110_);
lean_dec(v_revCmds_2109_);
lean_dec(v_fst_2108_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
}
v___jp_2151_:
{
lean_object* v_snapshotTasks_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_snapshotTasks_2160_ = lean_ctor_get(v___y_2157_, 10);
lean_inc_ref(v_snapshotTasks_2160_);
v___x_2161_ = lean_mk_empty_array_with_capacity(v___y_2152_);
lean_dec(v___y_2152_);
lean_inc_ref(v___y_2159_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2159_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_task_pure(v___x_2162_);
v___y_2133_ = v___y_2153_;
v___y_2134_ = v___y_2154_;
v___y_2135_ = v___y_2155_;
v___y_2136_ = v___y_2156_;
v___y_2137_ = v___y_2157_;
v_snapshotTasks_2138_ = v_snapshotTasks_2160_;
v___y_2139_ = v___y_2158_;
v___y_2140_ = v___y_2159_;
v_traceTask_2141_ = v___x_2163_;
goto v___jp_2132_;
}
v___jp_2164_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_opts_2206_; uint8_t v_hasTrace_2207_; 
v___x_2197_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2187_);
v___x_2198_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2198_, 0, v___y_2178_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
lean_ctor_set(v___x_2198_, 2, v___y_2173_);
lean_ctor_set(v___x_2198_, 3, v_traceState_2190_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*4, v_val_2111_);
v___x_2199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v_reportedCmdState_2196_);
lean_ctor_set(v___x_2199_, 2, v_codeQualityEntryTasks_2192_);
v___x_2200_ = lean_io_promise_resolve(v___x_2199_, v___x_2129_);
lean_dec(v___x_2129_);
v___x_2201_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2189_);
lean_inc(v___y_2180_);
v___x_2202_ = l_BaseIO_chainTask___redArg(v___x_2201_, v___y_2181_, v___y_2180_, v___x_2115_);
v___x_2203_ = l_Lean_inheritedTraceOptions;
v___x_2204_ = lean_st_ref_get(v___x_2203_);
v___x_2205_ = l_List_head_x21___redArg(v___x_2116_, v_scopes_2188_);
lean_dec(v_scopes_2188_);
lean_dec_ref(v___x_2116_);
v_opts_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc_ref(v_opts_2206_);
lean_dec(v___x_2205_);
v_hasTrace_2207_ = lean_ctor_get_uint8(v_opts_2206_, sizeof(void*)*1);
if (v_hasTrace_2207_ == 0)
{
lean_dec_ref(v_opts_2206_);
lean_dec(v___x_2204_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_snapshotTasks_2191_);
lean_dec_ref(v_env_2186_);
lean_dec(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2175_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v_pos_2120_);
lean_dec_ref(v___f_2119_);
lean_dec_ref(v___f_2118_);
lean_dec_ref(v___f_2117_);
lean_dec(v___x_2114_);
v___y_2152_ = v___y_2180_;
v___y_2153_ = v___y_2174_;
v___y_2154_ = v___y_2176_;
v___y_2155_ = v___y_2184_;
v___y_2156_ = v___y_2177_;
v___y_2157_ = v___y_2185_;
v___y_2158_ = v___y_2179_;
v___y_2159_ = v___y_2195_;
goto v___jp_2151_;
}
else
{
lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2209_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2204_, v_opts_2206_, v___x_2208_);
lean_dec(v___x_2204_);
if (v___x_2209_ == 0)
{
lean_dec_ref(v_opts_2206_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_snapshotTasks_2191_);
lean_dec_ref(v_env_2186_);
lean_dec(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2175_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v_pos_2120_);
lean_dec_ref(v___f_2119_);
lean_dec_ref(v___f_2118_);
lean_dec_ref(v___f_2117_);
lean_dec(v___x_2114_);
v___y_2152_ = v___y_2180_;
v___y_2153_ = v___y_2174_;
v___y_2154_ = v___y_2176_;
v___y_2155_ = v___y_2184_;
v___y_2156_ = v___y_2177_;
v___y_2157_ = v___y_2185_;
v___y_2158_ = v___y_2179_;
v___y_2159_ = v___y_2195_;
goto v___jp_2151_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_inc_n(v___y_2180_, 3);
v___x_2210_ = lean_task_map(v___f_2117_, v___y_2194_, v___y_2180_, v___x_2115_);
lean_inc_n(v___y_2184_, 3);
lean_inc_n(v___y_2182_, 2);
lean_inc_n(v___y_2183_, 2);
v___x_2211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2183_);
lean_ctor_set(v___x_2211_, 1, v___y_2182_);
lean_ctor_set(v___x_2211_, 2, v___y_2184_);
lean_ctor_set(v___x_2211_, 3, v___x_2210_);
v___x_2212_ = lean_task_map(v___f_2118_, v___y_2193_, v___y_2180_, v___x_2115_);
v___x_2213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2213_, 0, v___y_2183_);
lean_ctor_set(v___x_2213_, 1, v___y_2182_);
lean_ctor_set(v___x_2213_, 2, v___y_2184_);
lean_ctor_set(v___x_2213_, 3, v___x_2212_);
v___x_2214_ = lean_task_map(v___f_2119_, v___y_2175_, v___y_2180_, v___x_2115_);
v___x_2215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2215_, 0, v___y_2183_);
lean_ctor_set(v___x_2215_, 1, v___y_2182_);
lean_ctor_set(v___x_2215_, 2, v___y_2184_);
lean_ctor_set(v___x_2215_, 3, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(3u);
v___x_2217_ = lean_mk_empty_array_with_capacity(v___x_2216_);
v___x_2218_ = lean_array_push(v___x_2217_, v___x_2211_);
v___x_2219_ = lean_array_push(v___x_2218_, v___x_2213_);
v___x_2220_ = lean_array_push(v___x_2219_, v___x_2215_);
v___x_2221_ = l_Array_append___redArg(v___x_2220_, v_snapshotTasks_2191_);
lean_inc_ref(v___y_2195_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___y_2195_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_box_usize(v___y_2168_);
v___x_2224_ = lean_box(v___x_2115_);
v___x_2225_ = lean_box(v_val_2111_);
v___x_2226_ = lean_box(v___x_2209_);
lean_inc_ref(v___x_2222_);
lean_inc_ref(v___y_2170_);
lean_inc_ref(v_a_2112_);
v___f_2227_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2227_, 0, v_a_2112_);
lean_closure_set(v___f_2227_, 1, v_opts_2206_);
lean_closure_set(v___f_2227_, 2, v___x_2114_);
lean_closure_set(v___f_2227_, 3, v___y_2167_);
lean_closure_set(v___f_2227_, 4, v___y_2165_);
lean_closure_set(v___f_2227_, 5, v___x_2223_);
lean_closure_set(v___f_2227_, 6, v___x_2224_);
lean_closure_set(v___f_2227_, 7, v_env_2186_);
lean_closure_set(v___f_2227_, 8, v___y_2170_);
lean_closure_set(v___f_2227_, 9, v___x_2222_);
lean_closure_set(v___f_2227_, 10, v_pos_2120_);
lean_closure_set(v___f_2227_, 11, v___x_2225_);
lean_closure_set(v___f_2227_, 12, v___y_2172_);
lean_closure_set(v___f_2227_, 13, v___y_2171_);
lean_closure_set(v___f_2227_, 14, v___y_2169_);
lean_closure_set(v___f_2227_, 15, v___x_2203_);
lean_closure_set(v___f_2227_, 16, v___y_2166_);
lean_closure_set(v___f_2227_, 17, v___x_2226_);
v___x_2228_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2222_);
v___x_2229_ = lean_io_bind_task(v___x_2228_, v___f_2227_, v___y_2180_, v_val_2111_);
v___y_2133_ = v___y_2174_;
v___y_2134_ = v___y_2176_;
v___y_2135_ = v___y_2184_;
v___y_2136_ = v___y_2177_;
v___y_2137_ = v___y_2185_;
v_snapshotTasks_2138_ = v_snapshotTasks_2191_;
v___y_2139_ = v___y_2179_;
v___y_2140_ = v___y_2195_;
v_traceTask_2141_ = v___x_2229_;
goto v___jp_2132_;
}
}
}
v___jp_2230_:
{
lean_object* v_env_2256_; lean_object* v_messages_2257_; lean_object* v_scopes_2258_; lean_object* v_infoState_2259_; lean_object* v_traceState_2260_; lean_object* v_snapshotTasks_2261_; lean_object* v_codeQualityEntryTasks_2262_; 
v_env_2256_ = lean_ctor_get(v___y_2251_, 0);
lean_inc_ref(v_env_2256_);
v_messages_2257_ = lean_ctor_get(v___y_2251_, 1);
lean_inc_ref(v_messages_2257_);
v_scopes_2258_ = lean_ctor_get(v___y_2251_, 2);
lean_inc(v_scopes_2258_);
v_infoState_2259_ = lean_ctor_get(v___y_2251_, 8);
lean_inc_ref(v_infoState_2259_);
v_traceState_2260_ = lean_ctor_get(v___y_2251_, 9);
lean_inc_ref(v_traceState_2260_);
v_snapshotTasks_2261_ = lean_ctor_get(v___y_2251_, 10);
lean_inc_ref(v_snapshotTasks_2261_);
v_codeQualityEntryTasks_2262_ = lean_ctor_get(v___y_2251_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2262_);
v___y_2165_ = v___y_2231_;
v___y_2166_ = v___y_2233_;
v___y_2167_ = v___y_2232_;
v___y_2168_ = v___y_2234_;
v___y_2169_ = v___y_2236_;
v___y_2170_ = v___y_2235_;
v___y_2171_ = v___y_2238_;
v___y_2172_ = v___y_2237_;
v___y_2173_ = v___y_2239_;
v___y_2174_ = v___y_2240_;
v___y_2175_ = v___y_2241_;
v___y_2176_ = v___y_2242_;
v___y_2177_ = v___y_2243_;
v___y_2178_ = v___y_2244_;
v___y_2179_ = v___y_2245_;
v___y_2180_ = v___y_2246_;
v___y_2181_ = v___y_2247_;
v___y_2182_ = v___y_2248_;
v___y_2183_ = v___y_2249_;
v___y_2184_ = v___y_2250_;
v___y_2185_ = v___y_2251_;
v_env_2186_ = v_env_2256_;
v_messages_2187_ = v_messages_2257_;
v_scopes_2188_ = v_scopes_2258_;
v_infoState_2189_ = v_infoState_2259_;
v_traceState_2190_ = v_traceState_2260_;
v_snapshotTasks_2191_ = v_snapshotTasks_2261_;
v_codeQualityEntryTasks_2192_ = v_codeQualityEntryTasks_2262_;
v___y_2193_ = v___y_2252_;
v___y_2194_ = v___y_2253_;
v___y_2195_ = v___y_2254_;
v_reportedCmdState_2196_ = v_reportedCmdState_2255_;
goto v___jp_2164_;
}
v___jp_2264_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___f_2287_; uint8_t v___x_2288_; 
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___y_2282_);
lean_ctor_set(v___x_2283_, 1, v___x_2128_);
lean_inc_ref(v___y_2270_);
lean_inc_n(v_pos_2120_, 2);
lean_inc(v_revCmds_2109_);
lean_inc(v_fst_2108_);
v___x_2284_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2108_, v_revCmds_2109_, v_cmdState_2121_, v_pos_2120_, v___x_2283_, v___y_2270_, v_a_2112_);
v___x_2285_ = lean_box(v_val_2111_);
v___x_2286_ = lean_box(v___x_2115_);
lean_inc_ref(v_a_2112_);
lean_inc(v___y_2269_);
lean_inc_ref(v___x_2116_);
lean_inc_ref(v___x_2284_);
lean_inc_ref(v___y_2274_);
lean_inc_ref(v___y_2276_);
v___f_2287_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2287_, 0, v___y_2276_);
lean_closure_set(v___f_2287_, 1, v___y_2274_);
lean_closure_set(v___f_2287_, 2, v___x_2285_);
lean_closure_set(v___f_2287_, 3, v___x_2130_);
lean_closure_set(v___f_2287_, 4, v___x_2284_);
lean_closure_set(v___f_2287_, 5, v___x_2116_);
lean_closure_set(v___f_2287_, 6, v___y_2269_);
lean_closure_set(v___f_2287_, 7, v___x_2286_);
lean_closure_set(v___f_2287_, 8, v_a_2112_);
lean_closure_set(v___f_2287_, 9, v_pos_2120_);
lean_closure_set(v___f_2287_, 10, v___x_2122_);
v___x_2288_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2123_, v___x_2263_);
if (v___x_2288_ == 0)
{
lean_inc_ref(v___x_2284_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2276_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2268_);
lean_inc(v___y_2269_);
v___y_2231_ = v___y_2266_;
v___y_2232_ = v___y_2269_;
v___y_2233_ = v___y_2268_;
v___y_2234_ = v___y_2271_;
v___y_2235_ = v___y_2274_;
v___y_2236_ = v___y_2273_;
v___y_2237_ = v___y_2276_;
v___y_2238_ = v___y_2275_;
v___y_2239_ = v___y_2275_;
v___y_2240_ = v___y_2277_;
v___y_2241_ = v___y_2279_;
v___y_2242_ = v___y_2278_;
v___y_2243_ = v___y_2280_;
v___y_2244_ = v___y_2276_;
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2269_;
v___y_2247_ = v___f_2287_;
v___y_2248_ = v___y_2267_;
v___y_2249_ = v___y_2265_;
v___y_2250_ = v___y_2268_;
v___y_2251_ = v___x_2284_;
v___y_2252_ = v___y_2281_;
v___y_2253_ = v___y_2272_;
v___y_2254_ = v___y_2273_;
v_reportedCmdState_2255_ = v___x_2284_;
goto v___jp_2230_;
}
else
{
uint8_t v___x_2289_; 
lean_inc(v_fst_2108_);
v___x_2289_ = l_Lean_Parser_isTerminalCommand(v_fst_2108_);
if (v___x_2289_ == 0)
{
lean_object* v_env_2290_; lean_object* v_messages_2291_; lean_object* v_scopes_2292_; lean_object* v_infoState_2293_; lean_object* v_traceState_2294_; lean_object* v_snapshotTasks_2295_; lean_object* v_codeQualityEntryTasks_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_env_2290_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref_n(v_env_2290_, 2);
v_messages_2291_ = lean_ctor_get(v___x_2284_, 1);
lean_inc_ref(v_messages_2291_);
v_scopes_2292_ = lean_ctor_get(v___x_2284_, 2);
lean_inc(v_scopes_2292_);
v_infoState_2293_ = lean_ctor_get(v___x_2284_, 8);
lean_inc_ref(v_infoState_2293_);
v_traceState_2294_ = lean_ctor_get(v___x_2284_, 9);
lean_inc_ref(v_traceState_2294_);
v_snapshotTasks_2295_ = lean_ctor_get(v___x_2284_, 10);
lean_inc_ref(v_snapshotTasks_2295_);
v_codeQualityEntryTasks_2296_ = lean_ctor_get(v___x_2284_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2296_);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___y_2266_);
lean_inc_ref(v___x_2297_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_inc_n(v___y_2269_, 4);
v___x_2299_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
lean_ctor_set(v___x_2299_, 2, v___y_2269_);
lean_ctor_set(v___x_2299_, 3, v___y_2269_);
lean_ctor_set_usize(v___x_2299_, 4, v___y_2271_);
v___x_2300_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2299_, 2);
v___x_2301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2299_);
lean_ctor_set(v___x_2301_, 2, v___x_2300_);
v___x_2302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2303_ = l_Lean_Options_empty;
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_mk_empty_array_with_capacity(v___y_2269_);
lean_inc_ref_n(v___x_2305_, 3);
lean_inc_n(v___x_2114_, 2);
v___x_2306_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2306_, 0, v___x_2302_);
lean_ctor_set(v___x_2306_, 1, v___x_2303_);
lean_ctor_set(v___x_2306_, 2, v___x_2114_);
lean_ctor_set(v___x_2306_, 3, v___x_2304_);
lean_ctor_set(v___x_2306_, 4, v___x_2304_);
lean_ctor_set(v___x_2306_, 5, v___x_2305_);
lean_ctor_set(v___x_2306_, 6, v___x_2305_);
lean_ctor_set(v___x_2306_, 7, v___x_2304_);
lean_ctor_set(v___x_2306_, 8, v___x_2304_);
lean_ctor_set(v___x_2306_, 9, v___x_2304_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*10, v_val_2111_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*10 + 1, v_val_2111_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*10 + 2, v_val_2111_);
v___x_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2304_);
v___x_2308_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2309_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2310_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2114_);
v___x_2311_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2312_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
lean_ctor_set(v___x_2312_, 2, v___x_2299_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*3, v___x_2115_);
v___x_2313_ = lean_box(0);
lean_inc_ref(v___y_2274_);
v___x_2314_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2314_, 0, v_env_2290_);
lean_ctor_set(v___x_2314_, 1, v___x_2301_);
lean_ctor_set(v___x_2314_, 2, v___x_2307_);
lean_ctor_set(v___x_2314_, 3, v___x_2300_);
lean_ctor_set(v___x_2314_, 4, v___x_2308_);
lean_ctor_set(v___x_2314_, 5, v___y_2269_);
lean_ctor_set(v___x_2314_, 6, v___x_2309_);
lean_ctor_set(v___x_2314_, 7, v___x_2310_);
lean_ctor_set(v___x_2314_, 8, v___x_2312_);
lean_ctor_set(v___x_2314_, 9, v___y_2274_);
lean_ctor_set(v___x_2314_, 10, v___x_2305_);
lean_ctor_set(v___x_2314_, 11, v___x_2313_);
lean_ctor_set(v___x_2314_, 12, v___x_2305_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2268_);
v___y_2165_ = v___y_2266_;
v___y_2166_ = v___y_2268_;
v___y_2167_ = v___y_2269_;
v___y_2168_ = v___y_2271_;
v___y_2169_ = v___y_2273_;
v___y_2170_ = v___y_2274_;
v___y_2171_ = v___y_2275_;
v___y_2172_ = v___y_2276_;
v___y_2173_ = v___y_2275_;
v___y_2174_ = v___y_2277_;
v___y_2175_ = v___y_2279_;
v___y_2176_ = v___y_2278_;
v___y_2177_ = v___y_2280_;
v___y_2178_ = v___y_2276_;
v___y_2179_ = v___y_2270_;
v___y_2180_ = v___y_2269_;
v___y_2181_ = v___f_2287_;
v___y_2182_ = v___y_2267_;
v___y_2183_ = v___y_2265_;
v___y_2184_ = v___y_2268_;
v___y_2185_ = v___x_2284_;
v_env_2186_ = v_env_2290_;
v_messages_2187_ = v_messages_2291_;
v_scopes_2188_ = v_scopes_2292_;
v_infoState_2189_ = v_infoState_2293_;
v_traceState_2190_ = v_traceState_2294_;
v_snapshotTasks_2191_ = v_snapshotTasks_2295_;
v_codeQualityEntryTasks_2192_ = v_codeQualityEntryTasks_2296_;
v___y_2193_ = v___y_2281_;
v___y_2194_ = v___y_2272_;
v___y_2195_ = v___y_2273_;
v_reportedCmdState_2196_ = v___x_2314_;
goto v___jp_2164_;
}
else
{
lean_inc_ref(v___x_2284_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2276_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2268_);
lean_inc(v___y_2269_);
v___y_2231_ = v___y_2266_;
v___y_2232_ = v___y_2269_;
v___y_2233_ = v___y_2268_;
v___y_2234_ = v___y_2271_;
v___y_2235_ = v___y_2274_;
v___y_2236_ = v___y_2273_;
v___y_2237_ = v___y_2276_;
v___y_2238_ = v___y_2275_;
v___y_2239_ = v___y_2275_;
v___y_2240_ = v___y_2277_;
v___y_2241_ = v___y_2279_;
v___y_2242_ = v___y_2278_;
v___y_2243_ = v___y_2280_;
v___y_2244_ = v___y_2276_;
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2269_;
v___y_2247_ = v___f_2287_;
v___y_2248_ = v___y_2267_;
v___y_2249_ = v___y_2265_;
v___y_2250_ = v___y_2268_;
v___y_2251_ = v___x_2284_;
v___y_2252_ = v___y_2281_;
v___y_2253_ = v___y_2272_;
v___y_2254_ = v___y_2273_;
v_reportedCmdState_2255_ = v___x_2284_;
goto v___jp_2230_;
}
}
}
v___jp_2315_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; size_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2321_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2113_);
v___x_2322_ = l_IO_CancelToken_new();
v___x_2323_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2114_);
v___x_2324_ = l_Lean_Name_str___override(v___x_2114_, v___x_2323_);
v___x_2325_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2326_ = l_Lean_Name_str___override(v___x_2324_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2328_ = l_Lean_Name_str___override(v___x_2326_, v___x_2327_);
v___x_2329_ = l_Lean_Name_str___override(v___x_2328_, v___x_2325_);
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = l_Lean_Name_num___override(v___x_2329_, v___x_2330_);
v___x_2332_ = l_Lean_Name_str___override(v___x_2331_, v___x_2325_);
v___x_2333_ = l_Lean_Name_str___override(v___x_2332_, v___x_2327_);
v___x_2334_ = l_Lean_Name_str___override(v___x_2333_, v___x_2325_);
v___x_2335_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2336_ = l_Lean_Name_str___override(v___x_2334_, v___x_2335_);
v___x_2337_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2338_ = l_Lean_Name_str___override(v___x_2336_, v___x_2337_);
v___x_2339_ = l_Lean_Name_toString(v___x_2338_, v___x_2115_);
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_unsigned_to_nat(32u);
v___x_2342_ = lean_mk_empty_array_with_capacity(v___x_2341_);
lean_dec_ref(v___x_2342_);
v___x_2343_ = ((size_t)5ULL);
v___x_2344_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2339_, 2);
v___x_2345_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2339_);
lean_ctor_set(v___x_2345_, 1, v___x_2321_);
lean_ctor_set(v___x_2345_, 2, v___x_2340_);
lean_ctor_set(v___x_2345_, 3, v___x_2344_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*4, v_val_2111_);
v___x_2346_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2347_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2339_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
lean_ctor_set(v___x_2347_, 2, v___x_2340_);
lean_ctor_set(v___x_2347_, 3, v___x_2344_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*4, v_val_2111_);
lean_inc(v___y_2316_);
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___y_2316_);
v___x_2349_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2348_);
lean_inc_ref(v___x_2322_);
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2322_);
v___x_2351_ = l_IO_Promise_result_x21___redArg(v___x_2128_);
lean_inc_ref(v___x_2351_);
lean_inc(v___x_2349_);
lean_inc_ref_n(v___x_2348_, 3);
v___x_2352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2348_);
lean_ctor_set(v___x_2352_, 1, v___x_2349_);
lean_ctor_set(v___x_2352_, 2, v___x_2350_);
lean_ctor_set(v___x_2352_, 3, v___x_2351_);
v___x_2353_ = l_IO_Promise_result_x21___redArg(v___x_2129_);
lean_inc_ref(v___x_2353_);
lean_inc_n(v___y_2318_, 3);
v___x_2354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2348_);
lean_ctor_set(v___x_2354_, 1, v___y_2318_);
lean_ctor_set(v___x_2354_, 2, v___x_2340_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
v___x_2355_ = l_IO_Promise_result_x21___redArg(v___x_2130_);
lean_inc_ref(v___x_2355_);
v___x_2356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2348_);
lean_ctor_set(v___x_2356_, 1, v___y_2318_);
lean_ctor_set(v___x_2356_, 2, v___x_2340_);
lean_ctor_set(v___x_2356_, 3, v___x_2355_);
v___x_2357_ = l_IO_Promise_result_x21___redArg(v___x_2131_);
v___x_2358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2340_);
lean_ctor_set(v___x_2358_, 1, v___y_2318_);
lean_ctor_set(v___x_2358_, 2, v___x_2340_);
lean_ctor_set(v___x_2358_, 3, v___x_2357_);
lean_inc_ref(v___x_2347_);
v___x_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2347_);
lean_ctor_set(v___x_2359_, 1, v___x_2352_);
lean_ctor_set(v___x_2359_, 2, v___x_2354_);
lean_ctor_set(v___x_2359_, 3, v___x_2356_);
lean_ctor_set(v___x_2359_, 4, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2345_);
lean_ctor_set(v___x_2360_, 1, v___y_2316_);
lean_ctor_set(v___x_2360_, 2, v___y_2319_);
lean_ctor_set(v___x_2360_, 3, v___x_2359_);
lean_ctor_set(v___x_2360_, 4, v___y_2320_);
v___x_2361_ = lean_io_promise_resolve(v___x_2360_, v_prom_2124_);
if (lean_obj_tag(v_old_x3f_2125_) == 0)
{
v___y_2265_ = v___x_2348_;
v___y_2266_ = v___x_2341_;
v___y_2267_ = v___x_2349_;
v___y_2268_ = v___x_2340_;
v___y_2269_ = v___x_2330_;
v___y_2270_ = v___x_2322_;
v___y_2271_ = v___x_2343_;
v___y_2272_ = v___x_2351_;
v___y_2273_ = v___x_2347_;
v___y_2274_ = v___x_2344_;
v___y_2275_ = v___x_2340_;
v___y_2276_ = v___x_2339_;
v___y_2277_ = v___y_2317_;
v___y_2278_ = v___x_2340_;
v___y_2279_ = v___x_2355_;
v___y_2280_ = v___y_2318_;
v___y_2281_ = v___x_2353_;
v___y_2282_ = v___x_2340_;
goto v___jp_2264_;
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2373_; 
v_val_2362_ = lean_ctor_get(v_old_x3f_2125_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_old_x3f_2125_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2364_ = v_old_x3f_2125_;
v_isShared_2365_ = v_isSharedCheck_2373_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v_old_x3f_2125_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2373_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_elabSnap_2366_; lean_object* v_stx_2367_; lean_object* v_elabSnap_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v_elabSnap_2366_ = lean_ctor_get(v_val_2362_, 3);
lean_inc_ref(v_elabSnap_2366_);
v_stx_2367_ = lean_ctor_get(v_val_2362_, 1);
lean_inc(v_stx_2367_);
lean_dec(v_val_2362_);
v_elabSnap_2368_ = lean_ctor_get(v_elabSnap_2366_, 1);
lean_inc_ref(v_elabSnap_2368_);
lean_dec_ref(v_elabSnap_2366_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_stx_2367_);
lean_ctor_set(v___x_2369_, 1, v_elabSnap_2368_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2369_);
v___x_2371_ = v___x_2364_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
v___y_2265_ = v___x_2348_;
v___y_2266_ = v___x_2341_;
v___y_2267_ = v___x_2349_;
v___y_2268_ = v___x_2340_;
v___y_2269_ = v___x_2330_;
v___y_2270_ = v___x_2322_;
v___y_2271_ = v___x_2343_;
v___y_2272_ = v___x_2351_;
v___y_2273_ = v___x_2347_;
v___y_2274_ = v___x_2344_;
v___y_2275_ = v___x_2340_;
v___y_2276_ = v___x_2339_;
v___y_2277_ = v___y_2317_;
v___y_2278_ = v___x_2340_;
v___y_2279_ = v___x_2355_;
v___y_2280_ = v___y_2318_;
v___y_2281_ = v___x_2353_;
v___y_2282_ = v___x_2371_;
goto v___jp_2264_;
}
}
}
}
v___jp_2374_:
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2377_);
lean_inc(v_fst_2108_);
v___x_2379_ = l_Lean_Parser_isTerminalCommand(v_fst_2108_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v_toProcessingContext_2381_; lean_object* v_pos_2382_; lean_object* v_endPos_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2380_ = lean_io_promise_new();
v_toProcessingContext_2381_ = lean_ctor_get(v_a_2112_, 0);
v_pos_2382_ = lean_ctor_get(v_fst_2110_, 0);
v_endPos_2383_ = lean_ctor_get(v_toProcessingContext_2381_, 3);
lean_inc(v___x_2380_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2380_);
v___x_2385_ = lean_box(0);
lean_inc(v_endPos_2383_);
lean_inc(v_pos_2382_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_pos_2382_);
lean_ctor_set(v___x_2386_, 1, v_endPos_2383_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_parseCancelTk_2126_);
v___x_2389_ = l_IO_Promise_result_x21___redArg(v___x_2380_);
lean_dec(v___x_2380_);
v___x_2390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2385_);
lean_ctor_set(v___x_2390_, 1, v___x_2387_);
lean_ctor_set(v___x_2390_, 2, v___x_2388_);
lean_ctor_set(v___x_2390_, 3, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
v___y_2316_ = v___y_2375_;
v___y_2317_ = v___x_2384_;
v___y_2318_ = v___x_2378_;
v___y_2319_ = v___y_2376_;
v___y_2320_ = v___x_2391_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2392_; 
lean_dec_ref(v_parseCancelTk_2126_);
v___x_2392_ = lean_box(0);
v___y_2316_ = v___y_2375_;
v___y_2317_ = v___x_2392_;
v___y_2318_ = v___x_2378_;
v___y_2319_ = v___y_2376_;
v___y_2320_ = v___x_2392_;
goto v___jp_2315_;
}
}
v___jp_2393_:
{
lean_object* v___x_2396_; 
lean_inc(v_fst_2108_);
v___x_2396_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2108_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_box(0);
v___y_2375_ = v_fst_2394_;
v___y_2376_ = v_snd_2395_;
v___y_2377_ = v___x_2397_;
goto v___jp_2374_;
}
else
{
lean_object* v_val_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_val_2398_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v___x_2396_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_val_2398_);
lean_dec(v___x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_inc(v_val_2398_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_val_2398_);
lean_ctor_set(v___x_2402_, 1, v_val_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
v___y_2375_ = v_fst_2394_;
v___y_2376_ = v_snd_2395_;
v___y_2377_ = v___x_2404_;
goto v___jp_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2411_ = _args[0];
lean_object* v_revCmds_2412_ = _args[1];
lean_object* v_fst_2413_ = _args[2];
lean_object* v_val_2414_ = _args[3];
lean_object* v_a_2415_ = _args[4];
lean_object* v_snd_2416_ = _args[5];
lean_object* v___x_2417_ = _args[6];
lean_object* v___x_2418_ = _args[7];
lean_object* v___x_2419_ = _args[8];
lean_object* v___f_2420_ = _args[9];
lean_object* v___f_2421_ = _args[10];
lean_object* v___f_2422_ = _args[11];
lean_object* v_pos_2423_ = _args[12];
lean_object* v_cmdState_2424_ = _args[13];
lean_object* v___x_2425_ = _args[14];
lean_object* v_opts_2426_ = _args[15];
lean_object* v_prom_2427_ = _args[16];
lean_object* v_old_x3f_2428_ = _args[17];
lean_object* v_parseCancelTk_2429_ = _args[18];
lean_object* v___y_2430_ = _args[19];
_start:
{
uint8_t v_val_38003__boxed_2431_; uint8_t v___x_38006__boxed_2432_; lean_object* v_res_2433_; 
v_val_38003__boxed_2431_ = lean_unbox(v_val_2414_);
v___x_38006__boxed_2432_ = lean_unbox(v___x_2418_);
v_res_2433_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2411_, v_revCmds_2412_, v_fst_2413_, v_val_38003__boxed_2431_, v_a_2415_, v_snd_2416_, v___x_2417_, v___x_38006__boxed_2432_, v___x_2419_, v___f_2420_, v___f_2421_, v___f_2422_, v_pos_2423_, v_cmdState_2424_, v___x_2425_, v_opts_2426_, v_prom_2427_, v_old_x3f_2428_, v_parseCancelTk_2429_);
lean_dec(v_prom_2427_);
lean_dec_ref(v_opts_2426_);
lean_dec_ref(v_a_2415_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2436_, lean_object* v_parserState_2437_, lean_object* v_cmdState_2438_, lean_object* v_prom_2439_, uint8_t v_sync_2440_, lean_object* v_parseCancelTk_2441_, lean_object* v_revCmds_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_toSnapshot_2446_; lean_object* v_stx_2447_; lean_object* v_parserState_2448_; lean_object* v_elabSnap_2449_; lean_object* v_val_2450_; lean_object* v_newParserState_2451_; lean_object* v___y_2485_; lean_object* v___f_2486_; lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; uint8_t v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; uint8_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v_fst_2531_; lean_object* v_snd_2532_; lean_object* v___y_2545_; lean_object* v___y_2546_; uint8_t v___y_2547_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___x_2618_; 
v___f_2486_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2487_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2488_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2489_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2490_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2618_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2436_) == 1)
{
lean_object* v_val_2651_; lean_object* v_nextCmdSnap_x3f_2652_; 
v_val_2651_ = lean_ctor_get(v_old_x3f_2436_, 0);
v_nextCmdSnap_x3f_2652_ = lean_ctor_get(v_val_2651_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2652_) == 0)
{
goto v___jp_2619_;
}
else
{
lean_object* v_toSnapshot_2653_; lean_object* v_stx_2654_; lean_object* v_parserState_2655_; lean_object* v_elabSnap_2656_; lean_object* v_val_2657_; lean_object* v___x_2658_; 
v_toSnapshot_2653_ = lean_ctor_get(v_val_2651_, 0);
v_stx_2654_ = lean_ctor_get(v_val_2651_, 1);
v_parserState_2655_ = lean_ctor_get(v_val_2651_, 2);
v_elabSnap_2656_ = lean_ctor_get(v_val_2651_, 3);
v_val_2657_ = lean_ctor_get(v_nextCmdSnap_x3f_2652_, 0);
lean_inc(v_val_2657_);
v___x_2658_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2657_);
if (lean_obj_tag(v___x_2658_) == 1)
{
lean_object* v_val_2659_; lean_object* v_nextCmdSnap_x3f_2660_; 
v_val_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_val_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v_nextCmdSnap_x3f_2660_ = lean_ctor_get(v_val_2659_, 4);
lean_inc(v_nextCmdSnap_x3f_2660_);
lean_dec(v_val_2659_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2660_) == 0)
{
goto v___jp_2619_;
}
else
{
lean_object* v_val_2661_; lean_object* v___x_2662_; 
v_val_2661_ = lean_ctor_get(v_nextCmdSnap_x3f_2660_, 0);
lean_inc(v_val_2661_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2660_, 1);
v___x_2662_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2661_);
if (lean_obj_tag(v___x_2662_) == 1)
{
lean_object* v_val_2663_; lean_object* v_parserState_2664_; lean_object* v_pos_2665_; uint8_t v___x_2666_; 
v_val_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v_parserState_2664_ = lean_ctor_get(v_val_2663_, 2);
lean_inc_ref(v_parserState_2664_);
lean_dec(v_val_2663_);
v_pos_2665_ = lean_ctor_get(v_parserState_2664_, 0);
lean_inc(v_pos_2665_);
lean_dec_ref(v_parserState_2664_);
v___x_2666_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2665_, v_a_2443_);
lean_dec(v_pos_2665_);
if (v___x_2666_ == 0)
{
goto v___jp_2619_;
}
else
{
lean_inc(v_val_2657_);
lean_inc_ref(v_elabSnap_2656_);
lean_inc_ref_n(v_parserState_2655_, 2);
lean_inc(v_stx_2654_);
lean_inc_ref(v_toSnapshot_2653_);
lean_dec_ref_known(v_old_x3f_2436_, 1);
lean_dec_ref(v_parseCancelTk_2441_);
lean_dec_ref(v_cmdState_2438_);
lean_dec_ref(v_parserState_2437_);
v_toSnapshot_2446_ = v_toSnapshot_2653_;
v_stx_2447_ = v_stx_2654_;
v_parserState_2448_ = v_parserState_2655_;
v_elabSnap_2449_ = v_elabSnap_2656_;
v_val_2450_ = v_val_2657_;
v_newParserState_2451_ = v_parserState_2655_;
goto v___jp_2445_;
}
}
else
{
lean_dec(v___x_2662_);
goto v___jp_2619_;
}
}
}
else
{
lean_dec(v___x_2658_);
goto v___jp_2619_;
}
}
}
else
{
goto v___jp_2619_;
}
v___jp_2445_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_resultSnap_2454_; lean_object* v_task_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2478_; 
v___x_2452_ = lean_io_promise_new();
v___x_2453_ = l_IO_CancelToken_new();
v_resultSnap_2454_ = lean_ctor_get(v_elabSnap_2449_, 2);
lean_inc_ref(v_resultSnap_2454_);
v_task_2455_ = lean_ctor_get(v_resultSnap_2454_, 3);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_resultSnap_2454_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; lean_object* v_unused_2480_; lean_object* v_unused_2481_; 
v_unused_2479_ = lean_ctor_get(v_resultSnap_2454_, 2);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_resultSnap_2454_, 1);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v_resultSnap_2454_, 0);
lean_dec(v_unused_2481_);
v___x_2457_ = v_resultSnap_2454_;
v_isShared_2458_ = v_isSharedCheck_2478_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_task_2455_);
lean_dec(v_resultSnap_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2478_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v_toProcessingContext_2464_; lean_object* v_pos_2465_; lean_object* v_endPos_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2459_ = lean_box(v_sync_2440_);
lean_inc_ref(v_a_2443_);
lean_inc_ref(v___x_2453_);
lean_inc(v___x_2452_);
lean_inc_ref(v_newParserState_2451_);
lean_inc(v_stx_2447_);
v___f_2460_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2460_, 0, v_val_2450_);
lean_closure_set(v___f_2460_, 1, v_stx_2447_);
lean_closure_set(v___f_2460_, 2, v_revCmds_2442_);
lean_closure_set(v___f_2460_, 3, v_newParserState_2451_);
lean_closure_set(v___f_2460_, 4, v___x_2452_);
lean_closure_set(v___f_2460_, 5, v___x_2459_);
lean_closure_set(v___f_2460_, 6, v___x_2453_);
lean_closure_set(v___f_2460_, 7, v_a_2443_);
v___x_2461_ = lean_unsigned_to_nat(0u);
v___x_2462_ = 1;
v___x_2463_ = l_BaseIO_chainTask___redArg(v_task_2455_, v___f_2460_, v___x_2461_, v___x_2462_);
v_toProcessingContext_2464_ = lean_ctor_get(v_a_2443_, 0);
v_pos_2465_ = lean_ctor_get(v_newParserState_2451_, 0);
lean_inc(v_pos_2465_);
lean_dec_ref(v_newParserState_2451_);
v_endPos_2466_ = lean_ctor_get(v_toProcessingContext_2464_, 3);
v___x_2467_ = lean_box(0);
lean_inc(v_endPos_2466_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_pos_2465_);
lean_ctor_set(v___x_2468_, 1, v_endPos_2466_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2453_);
v___x_2471_ = l_IO_Promise_result_x21___redArg(v___x_2452_);
lean_dec(v___x_2452_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 3, v___x_2471_);
lean_ctor_set(v___x_2457_, 2, v___x_2470_);
lean_ctor_set(v___x_2457_, 1, v___x_2469_);
lean_ctor_set(v___x_2457_, 0, v___x_2467_);
v___x_2473_ = v___x_2457_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2475_, 0, v_toSnapshot_2446_);
lean_ctor_set(v___x_2475_, 1, v_stx_2447_);
lean_ctor_set(v___x_2475_, 2, v_parserState_2448_);
lean_ctor_set(v___x_2475_, 3, v_elabSnap_2449_);
lean_ctor_set(v___x_2475_, 4, v___x_2474_);
v___x_2476_ = lean_io_promise_resolve(v___x_2475_, v_prom_2439_);
lean_dec(v_prom_2439_);
return v___x_2476_;
}
}
}
v___jp_2482_:
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_box(0);
return v___x_2483_;
}
v___jp_2484_:
{
goto v___jp_2482_;
}
v___jp_2491_:
{
lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2509_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2508_);
v___x_2510_ = l_Lean_Parser_isTerminalCommand(v___y_2502_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_io_promise_new();
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
v___x_2513_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2509_, v___y_2498_, v___y_2493_, v_revCmds_2442_, v___y_2499_, v___y_2497_, v_a_2443_, v___y_2492_, v___y_2501_, v___y_2506_, v___y_2495_, v___y_2503_, v___y_2496_, v___x_2489_, v___f_2488_, v___f_2487_, v___f_2486_, v___y_2500_, v_cmdState_2438_, v___y_2507_, v___x_2490_, v___y_2504_, v___y_2494_, v___y_2505_, v_prom_2439_, v_old_x3f_2436_, v_parseCancelTk_2441_, v___x_2512_);
lean_dec(v_prom_2439_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2496_);
lean_dec(v___y_2498_);
v___y_2485_ = v___x_2513_;
goto v___jp_2484_;
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_box(0);
v___x_2515_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2509_, v___y_2498_, v___y_2493_, v_revCmds_2442_, v___y_2499_, v___y_2497_, v_a_2443_, v___y_2492_, v___y_2501_, v___y_2506_, v___y_2495_, v___y_2503_, v___y_2496_, v___x_2489_, v___f_2488_, v___f_2487_, v___f_2486_, v___y_2500_, v_cmdState_2438_, v___y_2507_, v___x_2490_, v___y_2504_, v___y_2494_, v___y_2505_, v_prom_2439_, v_old_x3f_2436_, v_parseCancelTk_2441_, v___x_2514_);
lean_dec(v_prom_2439_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2496_);
lean_dec(v___y_2498_);
v___y_2485_ = v___x_2515_;
goto v___jp_2484_;
}
}
v___jp_2516_:
{
lean_object* v___x_2533_; 
lean_inc(v___y_2530_);
v___x_2533_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2530_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_box(0);
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2518_;
v___y_2494_ = v___y_2519_;
v___y_2495_ = v_fst_2531_;
v___y_2496_ = v___y_2520_;
v___y_2497_ = v___y_2521_;
v___y_2498_ = v___y_2522_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2524_;
v___y_2501_ = v___y_2525_;
v___y_2502_ = v___y_2530_;
v___y_2503_ = v___y_2526_;
v___y_2504_ = v___y_2527_;
v___y_2505_ = v_snd_2532_;
v___y_2506_ = v___y_2528_;
v___y_2507_ = v___y_2529_;
v___y_2508_ = v___x_2534_;
goto v___jp_2491_;
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2543_; 
v_val_2535_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2537_ = v___x_2533_;
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_val_2535_);
lean_dec(v___x_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_inc(v_val_2535_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_val_2535_);
lean_ctor_set(v___x_2539_, 1, v_val_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2518_;
v___y_2494_ = v___y_2519_;
v___y_2495_ = v_fst_2531_;
v___y_2496_ = v___y_2520_;
v___y_2497_ = v___y_2521_;
v___y_2498_ = v___y_2522_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2524_;
v___y_2501_ = v___y_2525_;
v___y_2502_ = v___y_2530_;
v___y_2503_ = v___y_2526_;
v___y_2504_ = v___y_2527_;
v___y_2505_ = v_snd_2532_;
v___y_2506_ = v___y_2528_;
v___y_2507_ = v___y_2529_;
v___y_2508_ = v___x_2541_;
goto v___jp_2491_;
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2549_ = l_Lean_Name_str___override(v___y_2546_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2551_ = l_Lean_Name_str___override(v___x_2549_, v___x_2550_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2553_ = l_Lean_Name_str___override(v___x_2551_, v___x_2552_);
v___x_2554_ = l_Lean_Name_str___override(v___x_2553_, v___x_2550_);
v___x_2555_ = lean_unsigned_to_nat(0u);
v___x_2556_ = l_Lean_Name_num___override(v___x_2554_, v___x_2555_);
v___x_2557_ = l_Lean_Name_str___override(v___x_2556_, v___x_2550_);
v___x_2558_ = l_Lean_Name_str___override(v___x_2557_, v___x_2552_);
v___x_2559_ = l_Lean_Name_str___override(v___x_2558_, v___x_2550_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2561_ = l_Lean_Name_str___override(v___x_2559_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2563_ = l_Lean_Name_str___override(v___x_2561_, v___x_2562_);
v___x_2564_ = l_Lean_Name_toString(v___x_2563_, v___y_2547_);
v___x_2565_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2568_ = 0;
v___x_2569_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2569_, 0, v___x_2564_);
lean_ctor_set(v___x_2569_, 1, v___x_2565_);
lean_ctor_set(v___x_2569_, 2, v___x_2566_);
lean_ctor_set(v___x_2569_, 3, v___x_2567_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*4, v___x_2568_);
v___x_2570_ = lean_box(0);
v___x_2571_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2572_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2569_, 3);
v___x_2573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2569_);
lean_ctor_set(v___x_2573_, 1, v_cmdState_2438_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
v___x_2574_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2566_, v___x_2573_);
v___x_2575_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2566_, v___x_2569_);
v___x_2576_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2569_);
lean_ctor_set(v___x_2577_, 1, v___x_2571_);
lean_ctor_set(v___x_2577_, 2, v___x_2574_);
lean_ctor_set(v___x_2577_, 3, v___x_2575_);
lean_ctor_set(v___x_2577_, 4, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2569_);
lean_ctor_set(v___x_2578_, 1, v___x_2570_);
lean_ctor_set(v___x_2578_, 2, v___y_2545_);
lean_ctor_set(v___x_2578_, 3, v___x_2577_);
lean_ctor_set(v___x_2578_, 4, v___x_2566_);
v___x_2579_ = lean_io_promise_resolve(v___x_2578_, v_prom_2439_);
lean_dec(v_prom_2439_);
v___x_2580_ = lean_box(0);
return v___x_2580_;
}
v___jp_2581_:
{
uint8_t v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = l_IO_CancelToken_isSet(v_parseCancelTk_2441_);
v___x_2593_ = 1;
if (v___x_2592_ == 0)
{
lean_dec(v___y_2590_);
if (v_sync_2440_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2594_ = lean_io_promise_new();
v___x_2595_ = lean_io_promise_new();
v___x_2596_ = lean_io_promise_new();
v___x_2597_ = lean_io_promise_new();
v___x_2598_ = l_Lean_internal_cmdlineSnapshots;
v___x_2599_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2591_, v___x_2598_);
lean_dec_ref(v___y_2591_);
if (v___x_2599_ == 0)
{
lean_inc(v___y_2589_);
v___y_2517_ = v___y_2584_;
v___y_2518_ = v___y_2586_;
v___y_2519_ = v___x_2598_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___x_2592_;
v___y_2522_ = v___x_2597_;
v___y_2523_ = v___y_2583_;
v___y_2524_ = v___y_2582_;
v___y_2525_ = v___y_2585_;
v___y_2526_ = v___x_2594_;
v___y_2527_ = v___y_2587_;
v___y_2528_ = v___x_2593_;
v___y_2529_ = v___x_2596_;
v___y_2530_ = v___y_2589_;
v_fst_2531_ = v___y_2589_;
v_snd_2532_ = v___y_2588_;
goto v___jp_2516_;
}
else
{
uint8_t v___x_2600_; 
lean_inc(v___y_2589_);
v___x_2600_ = l_Lean_Parser_isTerminalCommand(v___y_2589_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref(v___y_2588_);
v___x_2601_ = lean_box(0);
v___x_2602_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2517_ = v___y_2584_;
v___y_2518_ = v___y_2586_;
v___y_2519_ = v___x_2598_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___x_2592_;
v___y_2522_ = v___x_2597_;
v___y_2523_ = v___y_2583_;
v___y_2524_ = v___y_2582_;
v___y_2525_ = v___y_2585_;
v___y_2526_ = v___x_2594_;
v___y_2527_ = v___y_2587_;
v___y_2528_ = v___x_2593_;
v___y_2529_ = v___x_2596_;
v___y_2530_ = v___y_2589_;
v_fst_2531_ = v___x_2601_;
v_snd_2532_ = v___x_2602_;
goto v___jp_2516_;
}
else
{
lean_inc(v___y_2589_);
v___y_2517_ = v___y_2584_;
v___y_2518_ = v___y_2586_;
v___y_2519_ = v___x_2598_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___x_2592_;
v___y_2522_ = v___x_2597_;
v___y_2523_ = v___y_2583_;
v___y_2524_ = v___y_2582_;
v___y_2525_ = v___y_2585_;
v___y_2526_ = v___x_2594_;
v___y_2527_ = v___y_2587_;
v___y_2528_ = v___x_2593_;
v___y_2529_ = v___x_2596_;
v___y_2530_ = v___y_2589_;
v_fst_2531_ = v___y_2589_;
v_snd_2532_ = v___y_2588_;
goto v___jp_2516_;
}
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
v___x_2603_ = lean_box(v___x_2592_);
v___x_2604_ = lean_box(v___x_2593_);
lean_inc_ref(v_a_2443_);
v___f_2605_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2605_, 0, v___y_2586_);
lean_closure_set(v___f_2605_, 1, v_revCmds_2442_);
lean_closure_set(v___f_2605_, 2, v___y_2583_);
lean_closure_set(v___f_2605_, 3, v___x_2603_);
lean_closure_set(v___f_2605_, 4, v_a_2443_);
lean_closure_set(v___f_2605_, 5, v___y_2584_);
lean_closure_set(v___f_2605_, 6, v___y_2585_);
lean_closure_set(v___f_2605_, 7, v___x_2604_);
lean_closure_set(v___f_2605_, 8, v___x_2489_);
lean_closure_set(v___f_2605_, 9, v___f_2488_);
lean_closure_set(v___f_2605_, 10, v___f_2487_);
lean_closure_set(v___f_2605_, 11, v___f_2486_);
lean_closure_set(v___f_2605_, 12, v___y_2582_);
lean_closure_set(v___f_2605_, 13, v_cmdState_2438_);
lean_closure_set(v___f_2605_, 14, v___x_2490_);
lean_closure_set(v___f_2605_, 15, v___y_2587_);
lean_closure_set(v___f_2605_, 16, v_prom_2439_);
lean_closure_set(v___f_2605_, 17, v_old_x3f_2436_);
lean_closure_set(v___f_2605_, 18, v_parseCancelTk_2441_);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_io_as_task(v___f_2605_, v___x_2606_);
lean_dec_ref(v___x_2607_);
goto v___jp_2482_;
}
}
else
{
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v_revCmds_2442_);
lean_dec_ref(v_parseCancelTk_2441_);
if (lean_obj_tag(v_old_x3f_2436_) == 1)
{
lean_object* v_val_2608_; lean_object* v___x_2609_; lean_object* v_children_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_val_2608_ = lean_ctor_get(v_old_x3f_2436_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v_old_x3f_2436_, 1);
v___x_2609_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2608_);
v_children_2610_ = lean_ctor_get(v___x_2609_, 1);
lean_inc_ref(v_children_2610_);
lean_dec_ref(v___x_2609_);
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_array_get_size(v_children_2610_);
v___x_2613_ = lean_nat_dec_lt(v___x_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_dec_ref(v_children_2610_);
v___y_2545_ = v___y_2588_;
v___y_2546_ = v___y_2590_;
v___y_2547_ = v___x_2593_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2614_; size_t v___x_2615_; size_t v___x_2616_; lean_object* v___x_2617_; 
v___x_2614_ = lean_box(0);
v___x_2615_ = ((size_t)0ULL);
v___x_2616_ = lean_usize_of_nat(v___x_2612_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2610_, v___x_2615_, v___x_2616_, v___x_2614_);
lean_dec_ref(v_children_2610_);
v___y_2545_ = v___y_2588_;
v___y_2546_ = v___y_2590_;
v___y_2547_ = v___x_2593_;
goto v___jp_2544_;
}
}
else
{
lean_dec(v_old_x3f_2436_);
v___y_2545_ = v___y_2588_;
v___y_2546_ = v___y_2590_;
v___y_2547_ = v___x_2593_;
goto v___jp_2544_;
}
}
}
v___jp_2619_:
{
lean_object* v_env_2620_; lean_object* v_scopes_2621_; lean_object* v___x_2622_; lean_object* v_opts_2623_; lean_object* v_currNamespace_2624_; lean_object* v_openDecls_2625_; lean_object* v___x_2626_; lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v_snd_2631_; 
v_env_2620_ = lean_ctor_get(v_cmdState_2438_, 0);
v_scopes_2621_ = lean_ctor_get(v_cmdState_2438_, 2);
v___x_2622_ = l_List_head_x21___redArg(v___x_2489_, v_scopes_2621_);
v_opts_2623_ = lean_ctor_get(v___x_2622_, 1);
lean_inc_ref_n(v_opts_2623_, 2);
v_currNamespace_2624_ = lean_ctor_get(v___x_2622_, 2);
lean_inc(v_currNamespace_2624_);
v_openDecls_2625_ = lean_ctor_get(v___x_2622_, 3);
lean_inc(v_openDecls_2625_);
lean_dec(v___x_2622_);
lean_inc_ref(v_env_2620_);
v___x_2626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2626_, 0, v_env_2620_);
lean_ctor_set(v___x_2626_, 1, v_opts_2623_);
lean_ctor_set(v___x_2626_, 2, v_currNamespace_2624_);
lean_ctor_set(v___x_2626_, 3, v_openDecls_2625_);
lean_inc_ref(v_parserState_2437_);
lean_inc_ref(v_a_2443_);
v___f_2627_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2627_, 0, v_a_2443_);
lean_closure_set(v___f_2627_, 1, v___x_2626_);
lean_closure_set(v___f_2627_, 2, v_parserState_2437_);
v___x_2628_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2629_ = lean_box(0);
v___x_2630_ = lean_profileit(v___x_2628_, v_opts_2623_, v___f_2627_, v___x_2629_);
v_snd_2631_ = lean_ctor_get(v___x_2630_, 1);
lean_inc(v_snd_2631_);
if (lean_obj_tag(v_old_x3f_2436_) == 1)
{
lean_object* v_val_2632_; lean_object* v_fst_2633_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v_pos_2636_; lean_object* v_toSnapshot_2637_; lean_object* v_stx_2638_; lean_object* v_parserState_2639_; lean_object* v_elabSnap_2640_; lean_object* v_nextCmdSnap_x3f_2641_; uint8_t v___x_2642_; 
v_val_2632_ = lean_ctor_get(v_old_x3f_2436_, 0);
v_fst_2633_ = lean_ctor_get(v___x_2630_, 0);
lean_inc_n(v_fst_2633_, 2);
lean_dec(v___x_2630_);
v_fst_2634_ = lean_ctor_get(v_snd_2631_, 0);
lean_inc(v_fst_2634_);
v_snd_2635_ = lean_ctor_get(v_snd_2631_, 1);
lean_inc(v_snd_2635_);
lean_dec(v_snd_2631_);
v_pos_2636_ = lean_ctor_get(v_parserState_2437_, 0);
lean_inc(v_pos_2636_);
lean_dec_ref(v_parserState_2437_);
v_toSnapshot_2637_ = lean_ctor_get(v_val_2632_, 0);
v_stx_2638_ = lean_ctor_get(v_val_2632_, 1);
v_parserState_2639_ = lean_ctor_get(v_val_2632_, 2);
v_elabSnap_2640_ = lean_ctor_get(v_val_2632_, 3);
v_nextCmdSnap_x3f_2641_ = lean_ctor_get(v_val_2632_, 4);
lean_inc(v_stx_2638_);
v___x_2642_ = l_Lean_Syntax_eqWithInfo(v_fst_2633_, v_stx_2638_);
if (v___x_2642_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2641_) == 0)
{
lean_inc_ref(v_opts_2623_);
lean_inc(v_fst_2633_);
lean_inc(v_fst_2634_);
v___y_2582_ = v_pos_2636_;
v___y_2583_ = v_fst_2634_;
v___y_2584_ = v_snd_2635_;
v___y_2585_ = v___x_2629_;
v___y_2586_ = v_fst_2633_;
v___y_2587_ = v_opts_2623_;
v___y_2588_ = v_fst_2634_;
v___y_2589_ = v_fst_2633_;
v___y_2590_ = v___x_2629_;
v___y_2591_ = v_opts_2623_;
goto v___jp_2581_;
}
else
{
lean_object* v_val_2643_; lean_object* v___x_2644_; 
v_val_2643_ = lean_ctor_get(v_nextCmdSnap_x3f_2641_, 0);
lean_inc(v_val_2643_);
v___x_2644_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2618_, v_val_2643_);
lean_inc_ref(v_opts_2623_);
lean_inc(v_fst_2633_);
lean_inc(v_fst_2634_);
v___y_2582_ = v_pos_2636_;
v___y_2583_ = v_fst_2634_;
v___y_2584_ = v_snd_2635_;
v___y_2585_ = v___x_2629_;
v___y_2586_ = v_fst_2633_;
v___y_2587_ = v_opts_2623_;
v___y_2588_ = v_fst_2634_;
v___y_2589_ = v_fst_2633_;
v___y_2590_ = v___x_2629_;
v___y_2591_ = v_opts_2623_;
goto v___jp_2581_;
}
}
else
{
lean_inc(v_val_2632_);
lean_dec(v_pos_2636_);
lean_dec(v_snd_2635_);
lean_dec(v_fst_2633_);
lean_dec_ref_known(v_old_x3f_2436_, 1);
lean_dec_ref(v_opts_2623_);
lean_dec_ref(v_parseCancelTk_2441_);
lean_dec_ref(v_cmdState_2438_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2641_) == 1)
{
lean_object* v_val_2645_; 
lean_inc_ref(v_nextCmdSnap_x3f_2641_);
lean_inc_ref(v_elabSnap_2640_);
lean_inc_ref(v_parserState_2639_);
lean_inc(v_stx_2638_);
lean_inc_ref(v_toSnapshot_2637_);
lean_dec(v_val_2632_);
v_val_2645_ = lean_ctor_get(v_nextCmdSnap_x3f_2641_, 0);
lean_inc(v_val_2645_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2641_, 1);
v_toSnapshot_2446_ = v_toSnapshot_2637_;
v_stx_2447_ = v_stx_2638_;
v_parserState_2448_ = v_parserState_2639_;
v_elabSnap_2449_ = v_elabSnap_2640_;
v_val_2450_ = v_val_2645_;
v_newParserState_2451_ = v_fst_2634_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2646_; 
lean_dec(v_fst_2634_);
lean_dec(v_revCmds_2442_);
v___x_2646_ = lean_io_promise_resolve(v_val_2632_, v_prom_2439_);
lean_dec(v_prom_2439_);
return v___x_2646_;
}
}
}
else
{
lean_object* v_fst_2647_; lean_object* v_fst_2648_; lean_object* v_snd_2649_; lean_object* v_pos_2650_; 
v_fst_2647_ = lean_ctor_get(v___x_2630_, 0);
lean_inc_n(v_fst_2647_, 2);
lean_dec(v___x_2630_);
v_fst_2648_ = lean_ctor_get(v_snd_2631_, 0);
lean_inc_n(v_fst_2648_, 2);
v_snd_2649_ = lean_ctor_get(v_snd_2631_, 1);
lean_inc(v_snd_2649_);
lean_dec(v_snd_2631_);
v_pos_2650_ = lean_ctor_get(v_parserState_2437_, 0);
lean_inc(v_pos_2650_);
lean_dec_ref(v_parserState_2437_);
lean_inc_ref(v_opts_2623_);
v___y_2582_ = v_pos_2650_;
v___y_2583_ = v_fst_2648_;
v___y_2584_ = v_snd_2649_;
v___y_2585_ = v___x_2629_;
v___y_2586_ = v_fst_2647_;
v___y_2587_ = v_opts_2623_;
v___y_2588_ = v_fst_2648_;
v___y_2589_ = v_fst_2647_;
v___y_2590_ = v___x_2629_;
v___y_2591_ = v_opts_2623_;
goto v___jp_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2667_, lean_object* v_stx_2668_, lean_object* v_revCmds_2669_, lean_object* v_newParserState_2670_, lean_object* v_val_2671_, uint8_t v_sync_2672_, lean_object* v_val_2673_, lean_object* v_a_2674_, lean_object* v_oldNext_2675_){
_start:
{
lean_object* v_cmdState_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_cmdState_2677_ = lean_ctor_get(v_oldResult_2667_, 1);
lean_inc_ref(v_cmdState_2677_);
lean_dec_ref(v_oldResult_2667_);
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_oldNext_2675_);
v___x_2679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_stx_2668_);
lean_ctor_set(v___x_2679_, 1, v_revCmds_2669_);
v___x_2680_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2678_, v_newParserState_2670_, v_cmdState_2677_, v_val_2671_, v_sync_2672_, v_val_2673_, v___x_2679_, v_a_2674_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2681_ = _args[0];
lean_object* v_val_2682_ = _args[1];
lean_object* v_fst_2683_ = _args[2];
lean_object* v_revCmds_2684_ = _args[3];
lean_object* v_fst_2685_ = _args[4];
lean_object* v_val_2686_ = _args[5];
lean_object* v_a_2687_ = _args[6];
lean_object* v_snd_2688_ = _args[7];
lean_object* v___x_2689_ = _args[8];
lean_object* v___x_2690_ = _args[9];
lean_object* v_fst_2691_ = _args[10];
lean_object* v_val_2692_ = _args[11];
lean_object* v_val_2693_ = _args[12];
lean_object* v___x_2694_ = _args[13];
lean_object* v___f_2695_ = _args[14];
lean_object* v___f_2696_ = _args[15];
lean_object* v___f_2697_ = _args[16];
lean_object* v_pos_2698_ = _args[17];
lean_object* v_cmdState_2699_ = _args[18];
lean_object* v_val_2700_ = _args[19];
lean_object* v___x_2701_ = _args[20];
lean_object* v_opts_2702_ = _args[21];
lean_object* v___x_2703_ = _args[22];
lean_object* v_snd_2704_ = _args[23];
lean_object* v_prom_2705_ = _args[24];
lean_object* v_old_x3f_2706_ = _args[25];
lean_object* v_parseCancelTk_2707_ = _args[26];
lean_object* v_next_x3f_2708_ = _args[27];
lean_object* v___y_2709_ = _args[28];
_start:
{
uint8_t v_val_37608__boxed_2710_; uint8_t v___x_37611__boxed_2711_; lean_object* v_res_2712_; 
v_val_37608__boxed_2710_ = lean_unbox(v_val_2686_);
v___x_37611__boxed_2711_ = lean_unbox(v___x_2690_);
v_res_2712_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2681_, v_val_2682_, v_fst_2683_, v_revCmds_2684_, v_fst_2685_, v_val_37608__boxed_2710_, v_a_2687_, v_snd_2688_, v___x_2689_, v___x_37611__boxed_2711_, v_fst_2691_, v_val_2692_, v_val_2693_, v___x_2694_, v___f_2695_, v___f_2696_, v___f_2697_, v_pos_2698_, v_cmdState_2699_, v_val_2700_, v___x_2701_, v_opts_2702_, v___x_2703_, v_snd_2704_, v_prom_2705_, v_old_x3f_2706_, v_parseCancelTk_2707_, v_next_x3f_2708_);
lean_dec(v_prom_2705_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v_opts_2702_);
lean_dec(v_val_2693_);
lean_dec_ref(v_a_2687_);
lean_dec(v_val_2682_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2713_, lean_object* v_parserState_2714_, lean_object* v_cmdState_2715_, lean_object* v_prom_2716_, lean_object* v_sync_2717_, lean_object* v_parseCancelTk_2718_, lean_object* v_revCmds_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
uint8_t v_sync_boxed_2722_; lean_object* v_res_2723_; 
v_sync_boxed_2722_ = lean_unbox(v_sync_2717_);
v_res_2723_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2713_, v_parserState_2714_, v_cmdState_2715_, v_prom_2716_, v_sync_boxed_2722_, v_parseCancelTk_2718_, v_revCmds_2719_, v_a_2720_);
lean_dec_ref(v_a_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2724_, size_t v_i_2725_, size_t v_stop_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2724_, v_i_2725_, v_stop_2726_, v_b_2727_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2731_, lean_object* v_i_2732_, lean_object* v_stop_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
size_t v_i_boxed_2737_; size_t v_stop_boxed_2738_; lean_object* v_res_2739_; 
v_i_boxed_2737_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_stop_boxed_2738_ = lean_unbox_usize(v_stop_2733_);
lean_dec(v_stop_2733_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2731_, v_i_boxed_2737_, v_stop_boxed_2738_, v_b_2734_, v___y_2735_);
lean_dec_ref(v___y_2735_);
lean_dec_ref(v_as_2731_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2740_, lean_object* v_opt_2741_){
_start:
{
lean_object* v_name_2742_; lean_object* v_map_2743_; lean_object* v___x_2744_; 
v_name_2742_ = lean_ctor_get(v_opt_2741_, 0);
v_map_2743_ = lean_ctor_get(v_opts_2740_, 0);
v___x_2744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2743_, v_name_2742_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_box(0);
return v___x_2745_;
}
else
{
lean_object* v_val_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2755_; 
v_val_2746_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2748_ = v___x_2744_;
v_isShared_2749_ = v_isSharedCheck_2755_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_val_2746_);
lean_dec(v___x_2744_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2755_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
if (lean_obj_tag(v_val_2746_) == 0)
{
lean_object* v_v_2750_; lean_object* v___x_2752_; 
v_v_2750_ = lean_ctor_get(v_val_2746_, 0);
lean_inc_ref(v_v_2750_);
lean_dec_ref_known(v_val_2746_, 1);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v_v_2750_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_v_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
else
{
lean_object* v___x_2754_; 
lean_del_object(v___x_2748_);
lean_dec(v_val_2746_);
v___x_2754_ = lean_box(0);
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2756_, lean_object* v_opt_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2756_, v_opt_2757_);
lean_dec_ref(v_opt_2757_);
lean_dec_ref(v_opts_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2759_, lean_object* v_x_2760_){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2759_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2763_, 0, v_x_2760_);
lean_ctor_set(v___x_2763_, 1, v___x_2761_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2770_ = l_Lean_Array_toPArray_x27___redArg(v___x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
if (lean_obj_tag(v_a_2771_) == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = l_List_reverse___redArg(v_a_2772_);
return v___x_2773_;
}
else
{
lean_object* v_head_2774_; lean_object* v_tail_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2788_; 
v_head_2774_ = lean_ctor_get(v_a_2771_, 0);
v_tail_2775_ = lean_ctor_get(v_a_2771_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_a_2771_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2777_ = v_a_2771_;
v_isShared_2778_ = v_isSharedCheck_2788_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_tail_2775_);
lean_inc(v_head_2774_);
lean_dec(v_a_2771_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2788_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2779_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v_head_2774_);
v___x_2781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
v___x_2782_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 1, v_a_2772_);
lean_ctor_set(v___x_2777_, 0, v___x_2783_);
v___x_2785_ = v___x_2777_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_a_2772_);
v___x_2785_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
v_a_2771_ = v_tail_2775_;
v_a_2772_ = v___x_2785_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2789_; double v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(1000000000u);
v___x_2790_ = lean_float_of_nat(v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2808_ = l_Lean_MessageData_ofFormat(v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2809_, lean_object* v_stx_2810_, lean_object* v_origStx_2811_, lean_object* v_toProcessingContext_2812_, lean_object* v___x_2813_, lean_object* v_fileMap_2814_, lean_object* v_parserState_2815_, lean_object* v_a_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_toProcessingContext_2822_; lean_object* v___x_2823_; 
v_toProcessingContext_2822_ = lean_ctor_get(v___y_2820_, 0);
lean_inc_ref(v_toProcessingContext_2822_);
lean_inc(v_stx_2810_);
v___x_2823_ = lean_apply_3(v_setupImports_2809_, v_stx_2810_, v_toProcessingContext_2822_, lean_box(0));
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_3037_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_3037_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_3037_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
if (lean_obj_tag(v_a_2824_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; 
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2817_);
lean_dec_ref(v_parserState_2815_);
lean_dec_ref(v_fileMap_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v_toProcessingContext_2812_);
lean_dec(v_origStx_2811_);
lean_dec(v_stx_2810_);
v_a_2828_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v_a_2824_, 1);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_a_2828_);
v___x_2830_ = v___x_2826_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_3036_; 
v_a_2832_ = lean_ctor_get(v_a_2824_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v_a_2824_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2834_ = v_a_2824_;
v_isShared_2835_ = v_isSharedCheck_3036_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v_a_2824_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_3036_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v_mainModuleName_2837_; lean_object* v_package_x3f_2838_; uint8_t v_isModule_2839_; lean_object* v_imports_2840_; lean_object* v_opts_2841_; uint32_t v_trustLevel_2842_; lean_object* v_importArts_2843_; lean_object* v_plugins_2844_; double v___x_2845_; double v___x_2846_; double v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2852_; 
v___x_2836_ = lean_io_mono_nanos_now();
v_mainModuleName_2837_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_mainModuleName_2837_);
v_package_x3f_2838_ = lean_ctor_get(v_a_2832_, 1);
lean_inc(v_package_x3f_2838_);
v_isModule_2839_ = lean_ctor_get_uint8(v_a_2832_, sizeof(void*)*6 + 4);
v_imports_2840_ = lean_ctor_get(v_a_2832_, 2);
lean_inc_ref(v_imports_2840_);
v_opts_2841_ = lean_ctor_get(v_a_2832_, 3);
lean_inc_ref(v_opts_2841_);
v_trustLevel_2842_ = lean_ctor_get_uint32(v_a_2832_, sizeof(void*)*6);
v_importArts_2843_ = lean_ctor_get(v_a_2832_, 4);
lean_inc(v_importArts_2843_);
v_plugins_2844_ = lean_ctor_get(v_a_2832_, 5);
lean_inc_ref(v_plugins_2844_);
lean_dec(v_a_2832_);
v___x_2845_ = lean_float_of_nat(v___x_2836_);
v___x_2846_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2847_ = lean_float_div(v___x_2845_, v___x_2846_);
v___x_2848_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2810_);
v___x_2849_ = l_Lean_MessageLog_empty;
v___x_2850_ = 1;
lean_inc(v_stx_2810_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_stx_2810_);
v___x_2852_ = v___x_2834_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_stx_2810_);
v___x_2852_ = v_reuseFailAlloc_3035_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_origStx_2811_);
lean_inc_ref(v___x_2852_);
lean_inc_ref(v_opts_2841_);
v___x_2854_ = l_Lean_Elab_processHeaderCore(v___x_2848_, v_imports_2840_, v_isModule_2839_, v_opts_2841_, v___x_2849_, v_toProcessingContext_2812_, v_trustLevel_2842_, v_plugins_2844_, v___x_2850_, v_mainModuleName_2837_, v_package_x3f_2838_, v_importArts_2843_, v___x_2852_, v___x_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_3026_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_3026_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_3026_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_3025_; 
v_fst_2859_ = lean_ctor_get(v_a_2855_, 0);
v_snd_2860_ = lean_ctor_get(v_a_2855_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2862_ = v_a_2855_;
v_isShared_2863_ = v_isSharedCheck_3025_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_snd_2860_);
lean_inc(v_fst_2859_);
lean_dec(v_a_2855_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_3025_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; double v___x_2865_; double v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v_traceState_2884_; 
v___x_2864_ = lean_io_mono_nanos_now();
v___x_2865_ = lean_float_of_nat(v___x_2864_);
v___x_2866_ = lean_float_div(v___x_2865_, v___x_2846_);
lean_inc(v_snd_2860_);
v___x_2867_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2860_);
v___x_2868_ = l_Lean_MessageLog_hasErrors(v_snd_2860_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_del_object(v___x_2826_);
lean_dec_ref(v___x_2819_);
v___x_2994_ = l_Lean_trace_profiler_output;
v___x_2995_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2841_, v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = l_Lean_trace_profiler_serve;
v___x_2997_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2841_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2884_ = v___x_2998_;
goto v___jp_2883_;
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
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint64_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_del_object(v___x_2862_);
lean_dec(v_snd_2860_);
lean_dec(v_fst_2859_);
lean_del_object(v___x_2857_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v_opts_2841_);
lean_dec(v___x_2817_);
lean_dec_ref(v_parserState_2815_);
lean_dec_ref(v_fileMap_2814_);
lean_dec(v_stx_2810_);
v___x_2999_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3000_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3001_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2813_, 2);
v___x_3002_ = l_Lean_Name_num___override(v___x_3001_, v___x_2813_);
v___x_3003_ = l_Lean_Name_str___override(v___x_3002_, v___x_2999_);
v___x_3004_ = l_Lean_Name_str___override(v___x_3003_, v___x_3000_);
v___x_3005_ = l_Lean_Name_str___override(v___x_3004_, v___x_2999_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3007_ = l_Lean_Name_str___override(v___x_3005_, v___x_3006_);
v___x_3008_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3009_ = l_Lean_Name_str___override(v___x_3007_, v___x_3008_);
v___x_3010_ = l_Lean_Name_toString(v___x_3009_, v___x_2850_);
v___x_3011_ = lean_box(0);
v___x_3012_ = 0ULL;
v___x_3013_ = lean_unsigned_to_nat(32u);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_3013_);
v___x_3015_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3016_ = ((size_t)5ULL);
v___x_3017_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3014_);
lean_ctor_set(v___x_3017_, 2, v___x_2813_);
lean_ctor_set(v___x_3017_, 3, v___x_2813_);
lean_ctor_set_usize(v___x_3017_, 4, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set_uint64(v___x_3018_, sizeof(void*)*1, v___x_3012_);
v___x_3019_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3019_, 0, v___x_3010_);
lean_ctor_set(v___x_3019_, 1, v___x_2867_);
lean_ctor_set(v___x_3019_, 2, v___x_3011_);
lean_ctor_set(v___x_3019_, 3, v___x_3018_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*4, v___x_2868_);
v___x_3020_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2819_);
v___x_3021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
lean_ctor_set(v___x_3021_, 2, v___x_3011_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_3021_);
v___x_3023_ = v___x_2826_;
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
v___jp_2869_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___y_2875_);
v___x_2877_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2877_, 0, v___y_2872_);
lean_ctor_set(v___x_2877_, 1, v___x_2867_);
lean_ctor_set(v___x_2877_, 2, v___x_2876_);
lean_ctor_set(v___x_2877_, 3, v___y_2870_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*4, v___x_2868_);
v___x_2878_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2874_, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2879_, 0, v___y_2871_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
lean_ctor_set(v___x_2879_, 2, v___y_2873_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2879_);
v___x_2881_ = v___x_2857_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
v___jp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Language_Lean_reparseOptions(v_opts_2841_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v_env_2888_; lean_object* v_messages_2889_; lean_object* v_scopes_2890_; lean_object* v_usedQuotCtxts_2891_; lean_object* v_nextMacroScope_2892_; lean_object* v_maxRecDepth_2893_; lean_object* v_ngen_2894_; lean_object* v_auxDeclNGen_2895_; lean_object* v_snapshotTasks_2896_; lean_object* v_prevLinterStates_2897_; lean_object* v_codeQualityEntryTasks_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2967_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
lean_inc(v_fst_2859_);
v___x_2887_ = l_Lean_Elab_Command_mkState(v_fst_2859_, v_snd_2860_, v_a_2886_);
v_env_2888_ = lean_ctor_get(v___x_2887_, 0);
v_messages_2889_ = lean_ctor_get(v___x_2887_, 1);
v_scopes_2890_ = lean_ctor_get(v___x_2887_, 2);
v_usedQuotCtxts_2891_ = lean_ctor_get(v___x_2887_, 3);
v_nextMacroScope_2892_ = lean_ctor_get(v___x_2887_, 4);
v_maxRecDepth_2893_ = lean_ctor_get(v___x_2887_, 5);
v_ngen_2894_ = lean_ctor_get(v___x_2887_, 6);
v_auxDeclNGen_2895_ = lean_ctor_get(v___x_2887_, 7);
v_snapshotTasks_2896_ = lean_ctor_get(v___x_2887_, 10);
v_prevLinterStates_2897_ = lean_ctor_get(v___x_2887_, 11);
v_codeQualityEntryTasks_2898_ = lean_ctor_get(v___x_2887_, 12);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; lean_object* v_unused_2969_; 
v_unused_2968_ = lean_ctor_get(v___x_2887_, 9);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v___x_2887_, 8);
lean_dec(v_unused_2969_);
v___x_2900_ = v___x_2887_;
v_isShared_2901_ = v_isSharedCheck_2967_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2898_);
lean_inc(v_prevLinterStates_2897_);
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
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2967_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2902_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2903_ = lean_box(0);
v___x_2904_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_inc_n(v___x_2813_, 4);
v___x_2905_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2813_);
lean_ctor_set(v___x_2905_, 1, v___x_2813_);
lean_ctor_set(v___x_2905_, 2, v___x_2813_);
lean_ctor_set(v___x_2905_, 3, v___x_2813_);
lean_ctor_set(v___x_2905_, 4, v___x_2902_);
lean_ctor_set(v___x_2905_, 5, v___x_2902_);
lean_ctor_set(v___x_2905_, 6, v___x_2902_);
lean_ctor_set(v___x_2905_, 7, v___x_2902_);
lean_ctor_set(v___x_2905_, 8, v___x_2902_);
lean_ctor_set(v___x_2905_, 9, v___x_2902_);
lean_ctor_set(v___x_2905_, 10, v___x_2902_);
lean_ctor_set(v___x_2905_, 11, v___x_2904_);
v___x_2906_ = l_Lean_Options_empty;
v___x_2907_ = lean_box(0);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2911_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2911_, 0, v_fst_2859_);
lean_ctor_set(v___x_2911_, 1, v___x_2903_);
lean_ctor_set(v___x_2911_, 2, v_fileMap_2814_);
lean_ctor_set(v___x_2911_, 3, v___x_2905_);
lean_ctor_set(v___x_2911_, 4, v___x_2906_);
lean_ctor_set(v___x_2911_, 5, v___x_2907_);
lean_ctor_set(v___x_2911_, 6, v___x_2908_);
lean_ctor_set(v___x_2911_, 7, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
v___x_2913_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2810_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v_stx_2810_);
lean_ctor_set(v___x_2862_, 0, v___x_2913_);
v___x_2915_ = v___x_2862_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_stx_2810_);
v___x_2915_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
v___x_2917_ = lean_unsigned_to_nat(2u);
v___x_2918_ = l_Lean_Syntax_getArg(v_stx_2810_, v___x_2917_);
lean_dec(v_stx_2810_);
v___x_2919_ = l_Lean_Syntax_getArgs(v___x_2918_);
lean_dec(v___x_2918_);
v___x_2920_ = lean_array_to_list(v___x_2919_);
v___x_2921_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2920_, v___x_2908_);
v___x_2922_ = l_Lean_List_toPArray_x27___redArg(v___x_2921_);
v___x_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2916_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2912_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_mk_empty_array_with_capacity(v___x_2909_);
v___x_2926_ = lean_array_push(v___x_2925_, v___x_2924_);
v___x_2927_ = l_Lean_Array_toPArray_x27___redArg(v___x_2926_);
lean_dec_ref(v___x_2926_);
lean_inc_ref(v___x_2927_);
v___x_2928_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2928_, 0, v___x_2902_);
lean_ctor_set(v___x_2928_, 1, v___x_2902_);
lean_ctor_set(v___x_2928_, 2, v___x_2927_);
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*3, v___x_2850_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 9, v_traceState_2884_);
lean_ctor_set(v___x_2900_, 8, v___x_2928_);
v___x_2930_ = v___x_2900_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_env_2888_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_messages_2889_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_scopes_2890_);
lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_usedQuotCtxts_2891_);
lean_ctor_set(v_reuseFailAlloc_2965_, 4, v_nextMacroScope_2892_);
lean_ctor_set(v_reuseFailAlloc_2965_, 5, v_maxRecDepth_2893_);
lean_ctor_set(v_reuseFailAlloc_2965_, 6, v_ngen_2894_);
lean_ctor_set(v_reuseFailAlloc_2965_, 7, v_auxDeclNGen_2895_);
lean_ctor_set(v_reuseFailAlloc_2965_, 8, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2965_, 9, v_traceState_2884_);
lean_ctor_set(v_reuseFailAlloc_2965_, 10, v_snapshotTasks_2896_);
lean_ctor_set(v_reuseFailAlloc_2965_, 11, v_prevLinterStates_2897_);
lean_ctor_set(v_reuseFailAlloc_2965_, 12, v_codeQualityEntryTasks_2898_);
v___x_2930_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; size_t v___x_2941_; lean_object* v___x_2942_; lean_object* v_size_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint64_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2931_ = lean_io_promise_new();
v___x_2932_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_2932_);
lean_inc(v___x_2931_);
lean_inc_ref(v___x_2930_);
v___x_2933_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2903_, v_parserState_2815_, v___x_2930_, v___x_2931_, v___x_2850_, v___x_2932_, v___x_2908_, v_a_2816_);
v___x_2934_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2935_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2936_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2813_, 3);
v___x_2937_ = l_Lean_Name_num___override(v___x_2936_, v___x_2813_);
v___x_2938_ = lean_unsigned_to_nat(32u);
v___x_2939_ = lean_mk_empty_array_with_capacity(v___x_2938_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2941_ = ((size_t)5ULL);
v___x_2942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2939_);
lean_ctor_set(v___x_2942_, 2, v___x_2813_);
lean_ctor_set(v___x_2942_, 3, v___x_2813_);
lean_ctor_set_usize(v___x_2942_, 4, v___x_2941_);
v_size_2943_ = lean_ctor_get(v___x_2927_, 2);
v___x_2944_ = l_Lean_Name_str___override(v___x_2937_, v___x_2934_);
v___x_2945_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2817_);
v___x_2946_ = l_Lean_Name_str___override(v___x_2944_, v___x_2935_);
v___x_2947_ = l_Lean_Name_str___override(v___x_2946_, v___x_2934_);
v___x_2948_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2949_ = l_Lean_Name_str___override(v___x_2947_, v___x_2948_);
v___x_2950_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2951_ = l_Lean_Name_str___override(v___x_2949_, v___x_2950_);
v___x_2952_ = l_Lean_Name_toString(v___x_2951_, v___x_2850_);
v___x_2953_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2954_ = 0ULL;
v___x_2955_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2955_, 0, v___x_2942_);
lean_ctor_set_uint64(v___x_2955_, sizeof(void*)*1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2932_);
v___x_2957_ = l_IO_Promise_result_x21___redArg(v___x_2931_);
lean_dec(v___x_2931_);
v___x_2958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2817_);
lean_ctor_set(v___x_2958_, 1, v___x_2945_);
lean_ctor_set(v___x_2958_, 2, v___x_2956_);
lean_ctor_set(v___x_2958_, 3, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2930_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_inc_ref(v___x_2955_);
lean_inc_ref(v___x_2952_);
v___x_2961_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2961_, 0, v___x_2952_);
lean_ctor_set(v___x_2961_, 1, v___x_2953_);
lean_ctor_set(v___x_2961_, 2, v___x_2903_);
lean_ctor_set(v___x_2961_, 3, v___x_2955_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*4, v___x_2868_);
v___x_2962_ = lean_nat_dec_lt(v___x_2813_, v_size_2943_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; 
lean_dec_ref(v___x_2927_);
lean_dec(v___x_2813_);
v___x_2963_ = l_outOfBounds___redArg(v___x_2818_);
v___y_2870_ = v___x_2955_;
v___y_2871_ = v___x_2961_;
v___y_2872_ = v___x_2952_;
v___y_2873_ = v___x_2960_;
v___y_2874_ = v___x_2852_;
v___y_2875_ = v___x_2963_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2818_, v___x_2927_, v___x_2813_);
lean_dec(v___x_2813_);
lean_dec_ref(v___x_2927_);
v___y_2870_ = v___x_2955_;
v___y_2871_ = v___x_2961_;
v___y_2872_ = v___x_2952_;
v___y_2873_ = v___x_2960_;
v___y_2874_ = v___x_2852_;
v___y_2875_ = v___x_2964_;
goto v___jp_2869_;
}
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_traceState_2884_);
lean_dec_ref(v___x_2867_);
lean_del_object(v___x_2862_);
lean_dec(v_snd_2860_);
lean_dec(v_fst_2859_);
lean_del_object(v___x_2857_);
lean_dec_ref(v___x_2852_);
lean_dec(v___x_2817_);
lean_dec_ref(v_parserState_2815_);
lean_dec_ref(v_fileMap_2814_);
lean_dec(v___x_2813_);
lean_dec(v_stx_2810_);
v_a_2970_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2885_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2885_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
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
lean_ctor_set_float(v___x_2984_, sizeof(void*)*3, v___x_2847_);
lean_ctor_set_float(v___x_2984_, sizeof(void*)*3 + 8, v___x_2866_);
lean_ctor_set_uint8(v___x_2984_, sizeof(void*)*3 + 16, v___x_2850_);
v___x_2985_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2986_ = lean_mk_empty_array_with_capacity(v___x_2813_);
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
v___x_2992_ = l_Lean_Array_toPArray_x27___redArg(v___x_2991_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set_uint64(v___x_2993_, sizeof(void*)*1, v___x_2979_);
v_traceState_2884_ = v___x_2993_;
goto v___jp_2883_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v___x_2852_);
lean_dec_ref(v_opts_2841_);
lean_del_object(v___x_2826_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2817_);
lean_dec_ref(v_parserState_2815_);
lean_dec_ref(v_fileMap_2814_);
lean_dec(v___x_2813_);
lean_dec(v_stx_2810_);
v_a_3027_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2854_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2854_);
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
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2817_);
lean_dec_ref(v_parserState_2815_);
lean_dec_ref(v_fileMap_2814_);
lean_dec(v___x_2813_);
lean_dec_ref(v_toProcessingContext_2812_);
lean_dec(v_origStx_2811_);
lean_dec(v_stx_2810_);
v_a_3038_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2823_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2823_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3046_, lean_object* v_stx_3047_, lean_object* v_origStx_3048_, lean_object* v_toProcessingContext_3049_, lean_object* v___x_3050_, lean_object* v_fileMap_3051_, lean_object* v_parserState_3052_, lean_object* v_a_3053_, lean_object* v___x_3054_, lean_object* v___x_3055_, lean_object* v___x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3046_, v_stx_3047_, v_origStx_3048_, v_toProcessingContext_3049_, v___x_3050_, v_fileMap_3051_, v_parserState_3052_, v_a_3053_, v___x_3054_, v___x_3055_, v___x_3056_, v___y_3057_);
lean_dec_ref(v___y_3057_);
lean_dec_ref(v___x_3055_);
lean_dec_ref(v_a_3053_);
return v_res_3059_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___f_3061_; 
v___x_3060_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3061_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3061_, 0, v___x_3060_);
return v___f_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3062_, lean_object* v_stx_3063_, lean_object* v_origStx_3064_, lean_object* v_parserState_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_toProcessingContext_3068_; lean_object* v_fileMap_3069_; lean_object* v_endPos_3070_; lean_object* v___x_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_toProcessingContext_3068_ = lean_ctor_get(v_a_3066_, 0);
v_fileMap_3069_ = lean_ctor_get(v_toProcessingContext_3068_, 2);
v_endPos_3070_ = lean_ctor_get(v_toProcessingContext_3068_, 3);
v___x_3071_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3072_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3073_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3066_, 2);
lean_inc_ref(v_fileMap_3069_);
lean_inc_ref(v_toProcessingContext_3068_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3076_, 0, v_setupImports_3062_);
lean_closure_set(v___f_3076_, 1, v_stx_3063_);
lean_closure_set(v___f_3076_, 2, v_origStx_3064_);
lean_closure_set(v___f_3076_, 3, v_toProcessingContext_3068_);
lean_closure_set(v___f_3076_, 4, v___x_3075_);
lean_closure_set(v___f_3076_, 5, v_fileMap_3069_);
lean_closure_set(v___f_3076_, 6, v_parserState_3065_);
lean_closure_set(v___f_3076_, 7, v_a_3066_);
lean_closure_set(v___f_3076_, 8, v___x_3074_);
lean_closure_set(v___f_3076_, 9, v___x_3073_);
lean_closure_set(v___f_3076_, 10, v___x_3071_);
lean_inc(v_endPos_3070_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v_endPos_3070_);
v___x_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
v___x_3079_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3079_, 0, lean_box(0));
lean_closure_set(v___x_3079_, 1, v___f_3072_);
lean_closure_set(v___x_3079_, 2, v___f_3076_);
lean_closure_set(v___x_3079_, 3, v_a_3066_);
v___x_3080_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3074_, v___x_3074_, v___x_3078_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3081_, lean_object* v_stx_3082_, lean_object* v_origStx_3083_, lean_object* v_parserState_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3081_, v_stx_3082_, v_origStx_3083_, v_parserState_3084_, v_a_3085_);
lean_dec_ref(v_a_3085_);
return v_res_3087_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_box(0);
v___x_3089_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3088_);
return v___x_3089_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = 1;
v___x_3095_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3096_ = l_Lean_Name_toString(v___x_3095_, v___x_3094_);
return v___x_3096_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3097_ = 0;
v___x_3098_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3099_ = lean_box(0);
v___x_3100_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3101_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
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
v___x_3114_ = lean_box(0);
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
v___x_3121_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3122_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
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
v___x_3130_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
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
v___x_3179_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
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
v___x_3214_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3252_, lean_object* v_setupImports_3253_, lean_object* v_old_x3f_3254_, lean_object* v___x_3255_, lean_object* v___f_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; 
lean_inc_ref(v_toProcessingContext_3252_);
v___x_3259_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3252_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3328_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3328_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3328_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_snd_3264_; lean_object* v_fst_3265_; lean_object* v_fst_3266_; lean_object* v_snd_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3327_; 
v_snd_3264_ = lean_ctor_get(v_a_3260_, 1);
lean_inc(v_snd_3264_);
v_fst_3265_ = lean_ctor_get(v_a_3260_, 0);
lean_inc(v_fst_3265_);
lean_dec(v_a_3260_);
v_fst_3266_ = lean_ctor_get(v_snd_3264_, 0);
v_snd_3267_ = lean_ctor_get(v_snd_3264_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_snd_3264_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3269_ = v_snd_3264_;
v_isShared_3270_ = v_isSharedCheck_3327_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_snd_3267_);
lean_inc(v_fst_3266_);
lean_dec(v_snd_3264_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3327_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
uint8_t v___x_3271_; 
v___x_3271_ = l_Lean_MessageLog_hasErrors(v_snd_3267_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___y_3274_; 
lean_inc(v_fst_3265_);
v___x_3272_ = l_Lean_Syntax_unsetTrailing(v_fst_3265_);
if (lean_obj_tag(v_old_x3f_3254_) == 1)
{
lean_object* v_val_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3310_; 
v_val_3295_ = lean_ctor_get(v_old_x3f_3254_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_old_x3f_3254_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3297_ = v_old_x3f_3254_;
v_isShared_3298_ = v_isSharedCheck_3310_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_val_3295_);
lean_dec(v_old_x3f_3254_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3310_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_stx_3299_; lean_object* v_result_x3f_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v_stx_3299_ = lean_ctor_get(v_val_3295_, 3);
v_result_x3f_3300_ = lean_ctor_get(v_val_3295_, 4);
lean_inc(v_stx_3299_);
v___x_3301_ = l_Lean_Syntax_unsetTrailing(v_stx_3299_);
lean_inc(v___x_3272_);
v___x_3302_ = l_Lean_Syntax_eqWithInfo(v___x_3272_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_inc(v_result_x3f_3300_);
lean_del_object(v___x_3297_);
lean_dec(v_val_3295_);
lean_dec_ref(v___f_3256_);
if (lean_obj_tag(v_result_x3f_3300_) == 0)
{
lean_dec_ref(v___x_3255_);
v___y_3274_ = v___y_3257_;
goto v___jp_3273_;
}
else
{
lean_object* v_val_3303_; lean_object* v_processedSnap_3304_; lean_object* v___x_3305_; 
v_val_3303_ = lean_ctor_get(v_result_x3f_3300_, 0);
lean_inc(v_val_3303_);
lean_dec_ref_known(v_result_x3f_3300_, 1);
v_processedSnap_3304_ = lean_ctor_get(v_val_3303_, 1);
lean_inc_ref(v_processedSnap_3304_);
lean_dec(v_val_3303_);
v___x_3305_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3255_, v_processedSnap_3304_);
v___y_3274_ = v___y_3257_;
goto v___jp_3273_;
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_dec(v___x_3272_);
lean_del_object(v___x_3269_);
lean_dec(v_snd_3267_);
lean_del_object(v___x_3262_);
lean_dec_ref(v___x_3255_);
lean_dec_ref(v_setupImports_3253_);
lean_dec_ref(v_toProcessingContext_3252_);
lean_inc_ref(v___y_3257_);
v___x_3306_ = lean_apply_5(v___f_3256_, v_val_3295_, v_fst_3265_, v_fst_3266_, v___y_3257_, lean_box(0));
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3306_);
v___x_3308_ = v___x_3297_;
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
lean_dec_ref(v___f_3256_);
lean_dec_ref(v___x_3255_);
lean_dec(v_old_x3f_3254_);
v___y_3274_ = v___y_3257_;
goto v___jp_3273_;
}
v___jp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3275_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3267_);
lean_inc(v_fst_3266_);
lean_inc(v_fst_3265_);
v___x_3276_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3253_, v___x_3272_, v_fst_3265_, v_fst_3266_, v___y_3274_);
v___x_3277_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3278_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_unsigned_to_nat(32u);
v___x_3281_ = lean_mk_empty_array_with_capacity(v___x_3280_);
lean_dec_ref(v___x_3281_);
v___x_3282_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v___x_3276_);
v___x_3284_ = v___x_3269_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_fst_3266_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___x_3276_);
v___x_3284_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3286_, 0, v___x_3277_);
lean_ctor_set(v___x_3286_, 1, v___x_3278_);
lean_ctor_set(v___x_3286_, 2, v___x_3279_);
lean_ctor_set(v___x_3286_, 3, v___x_3282_);
lean_ctor_set_uint8(v___x_3286_, sizeof(void*)*4, v___x_3271_);
lean_inc(v_fst_3265_);
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v_fst_3265_);
v___x_3288_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3277_);
lean_ctor_set(v___x_3288_, 1, v___x_3275_);
lean_ctor_set(v___x_3288_, 2, v___x_3279_);
lean_ctor_set(v___x_3288_, 3, v___x_3282_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*4, v___x_3271_);
v___x_3289_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3287_, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3286_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
lean_ctor_set(v___x_3290_, 2, v_toProcessingContext_3252_);
lean_ctor_set(v___x_3290_, 3, v_fst_3265_);
lean_ctor_set(v___x_3290_, 4, v___x_3285_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3290_);
v___x_3292_ = v___x_3262_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3325_; 
lean_del_object(v___x_3269_);
lean_dec(v_fst_3266_);
lean_dec_ref(v___f_3256_);
lean_dec_ref(v___x_3255_);
lean_dec(v_old_x3f_3254_);
lean_dec_ref(v_setupImports_3253_);
v___x_3311_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3267_);
v___x_3312_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
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
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*4, v___x_3271_);
lean_inc(v_fst_3265_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_fst_3265_);
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
lean_ctor_set(v___x_3323_, 3, v_fst_3265_);
lean_ctor_set(v___x_3323_, 4, v___x_3314_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3323_);
v___x_3325_ = v___x_3262_;
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
lean_dec_ref(v___f_3256_);
lean_dec_ref(v___x_3255_);
lean_dec(v_old_x3f_3254_);
lean_dec_ref(v_setupImports_3253_);
lean_dec_ref(v_toProcessingContext_3252_);
v_a_3329_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3259_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3259_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3337_, lean_object* v_setupImports_3338_, lean_object* v_old_x3f_3339_, lean_object* v___x_3340_, lean_object* v___f_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3337_, v_setupImports_3338_, v_old_x3f_3339_, v___x_3340_, v___f_3341_, v___y_3342_);
lean_dec_ref(v___y_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3345_, lean_object* v_toProcessingContext_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3348_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3345_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3351_, 0, v_x_3347_);
lean_ctor_set(v___x_3351_, 1, v___x_3348_);
lean_ctor_set(v___x_3351_, 2, v_toProcessingContext_3346_);
lean_ctor_set(v___x_3351_, 3, v___x_3349_);
lean_ctor_set(v___x_3351_, 4, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3352_, lean_object* v_old_x3f_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_toProcessingContext_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___f_3361_; 
v_toProcessingContext_3356_ = lean_ctor_get(v_a_3354_, 0);
v___x_3357_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3358_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3354_);
lean_inc_ref_n(v_toProcessingContext_3356_, 3);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3359_, 0, v_toProcessingContext_3356_);
lean_closure_set(v___f_3359_, 1, v_a_3354_);
lean_inc(v_old_x3f_3353_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3360_, 0, v_toProcessingContext_3356_);
lean_closure_set(v___f_3360_, 1, v_setupImports_3352_);
lean_closure_set(v___f_3360_, 2, v_old_x3f_3353_);
lean_closure_set(v___f_3360_, 3, v___x_3358_);
lean_closure_set(v___f_3360_, 4, v___f_3359_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3361_, 0, v___x_3357_);
lean_closure_set(v___f_3361_, 1, v_toProcessingContext_3356_);
if (lean_obj_tag(v_old_x3f_3353_) == 1)
{
lean_object* v_val_3362_; lean_object* v_result_x3f_3363_; 
v_val_3362_ = lean_ctor_get(v_old_x3f_3353_, 0);
lean_inc(v_val_3362_);
lean_dec_ref_known(v_old_x3f_3353_, 1);
v_result_x3f_3363_ = lean_ctor_get(v_val_3362_, 4);
if (lean_obj_tag(v_result_x3f_3363_) == 1)
{
lean_object* v_stx_3364_; lean_object* v_val_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_stx_3364_ = lean_ctor_get(v_val_3362_, 3);
lean_inc(v_stx_3364_);
v_val_3365_ = lean_ctor_get(v_result_x3f_3363_, 0);
lean_inc(v_val_3362_);
v___x_3366_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3362_);
v___x_3367_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3366_);
if (lean_obj_tag(v___x_3367_) == 1)
{
lean_object* v_val_3368_; 
v_val_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_val_3368_);
lean_dec_ref_known(v___x_3367_, 1);
if (lean_obj_tag(v_val_3368_) == 1)
{
lean_object* v_val_3369_; lean_object* v_firstCmdSnap_3370_; lean_object* v___x_3371_; 
v_val_3369_ = lean_ctor_get(v_val_3368_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v_val_3368_, 1);
v_firstCmdSnap_3370_ = lean_ctor_get(v_val_3369_, 1);
lean_inc_ref(v_firstCmdSnap_3370_);
lean_dec(v_val_3369_);
v___x_3371_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3370_);
if (lean_obj_tag(v___x_3371_) == 1)
{
lean_object* v_val_3372_; lean_object* v_nextCmdSnap_x3f_3373_; 
v_val_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_val_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v_nextCmdSnap_x3f_3373_ = lean_ctor_get(v_val_3372_, 4);
lean_inc(v_nextCmdSnap_x3f_3373_);
lean_dec(v_val_3372_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3373_) == 0)
{
lean_object* v___x_3374_; 
lean_dec(v_stx_3364_);
lean_dec(v_val_3362_);
v___x_3374_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3374_;
}
else
{
lean_object* v_val_3375_; lean_object* v___x_3376_; 
v_val_3375_ = lean_ctor_get(v_nextCmdSnap_x3f_3373_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3373_, 1);
v___x_3376_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3375_);
if (lean_obj_tag(v___x_3376_) == 1)
{
lean_object* v_val_3377_; lean_object* v_parserState_3378_; lean_object* v_pos_3379_; uint8_t v___x_3380_; 
v_val_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_val_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v_parserState_3378_ = lean_ctor_get(v_val_3377_, 2);
lean_inc_ref(v_parserState_3378_);
lean_dec(v_val_3377_);
v_pos_3379_ = lean_ctor_get(v_parserState_3378_, 0);
lean_inc(v_pos_3379_);
lean_dec_ref(v_parserState_3378_);
v___x_3380_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3379_, v_a_3354_);
lean_dec(v_pos_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
lean_dec(v_stx_3364_);
lean_dec(v_val_3362_);
v___x_3381_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3381_;
}
else
{
lean_object* v_parserState_3382_; lean_object* v___x_3383_; 
lean_dec_ref(v___f_3361_);
lean_dec_ref(v___f_3360_);
v_parserState_3382_ = lean_ctor_get(v_val_3365_, 0);
lean_inc_ref(v_parserState_3382_);
lean_inc_ref(v_toProcessingContext_3356_);
v___x_3383_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3356_, v_a_3354_, v_val_3362_, v_stx_3364_, v_parserState_3382_, v_a_3354_);
return v___x_3383_;
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v___x_3376_);
lean_dec(v_stx_3364_);
lean_dec(v_val_3362_);
v___x_3384_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3384_;
}
}
}
else
{
lean_object* v___x_3385_; 
lean_dec(v___x_3371_);
lean_dec(v_stx_3364_);
lean_dec(v_val_3362_);
v___x_3385_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3385_;
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v_val_3368_);
lean_dec(v_stx_3364_);
lean_dec(v_val_3362_);
v___x_3386_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3386_;
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v___x_3367_);
lean_dec(v_stx_3364_);
lean_dec(v_val_3362_);
v___x_3387_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3387_;
}
}
else
{
lean_object* v___x_3388_; 
lean_dec(v_val_3362_);
v___x_3388_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3388_;
}
}
else
{
lean_object* v___x_3389_; 
lean_dec(v_old_x3f_3353_);
v___x_3389_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3361_, v___f_3360_, v_a_3354_);
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3390_, lean_object* v_old_x3f_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3390_, v_old_x3f_3391_, v_a_3392_);
lean_dec_ref(v_a_3392_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3395_, lean_object* v_old_x3f_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v___x_3399_; 
lean_inc(v_old_x3f_3396_);
v___x_3399_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3399_, 0, v_setupImports_3395_);
lean_closure_set(v___x_3399_, 1, v_old_x3f_3396_);
if (lean_obj_tag(v_old_x3f_3396_) == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_box(0);
v___x_3401_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3399_, v___x_3400_, v_a_3397_);
return v___x_3401_;
}
else
{
lean_object* v_val_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3411_; 
v_val_3402_ = lean_ctor_get(v_old_x3f_3396_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_old_x3f_3396_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3404_ = v_old_x3f_3396_;
v_isShared_3405_ = v_isSharedCheck_3411_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_val_3402_);
lean_dec(v_old_x3f_3396_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3411_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_ictx_3406_; lean_object* v___x_3408_; 
v_ictx_3406_ = lean_ctor_get(v_val_3402_, 2);
lean_inc_ref(v_ictx_3406_);
lean_dec(v_val_3402_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v_ictx_3406_);
v___x_3408_ = v___x_3404_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_ictx_3406_);
v___x_3408_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3399_, v___x_3408_, v_a_3397_);
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3412_, lean_object* v_old_x3f_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Language_Lean_process(v_setupImports_3412_, v_old_x3f_3413_, v_a_3414_);
lean_dec_ref(v_a_3414_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3417_, lean_object* v_parserState_3418_, lean_object* v_commandState_3419_, lean_object* v_old_x3f_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3430_; 
v___x_3422_ = lean_io_promise_new();
v___x_3423_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3420_) == 0)
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_box(0);
v___y_3430_ = v___x_3445_;
goto v___jp_3429_;
}
else
{
lean_object* v_val_3446_; lean_object* v_snd_3447_; lean_object* v___x_3448_; 
v_val_3446_ = lean_ctor_get(v_old_x3f_3420_, 0);
v_snd_3447_ = lean_ctor_get(v_val_3446_, 1);
lean_inc(v_snd_3447_);
v___x_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_snd_3447_);
v___y_3430_ = v___x_3448_;
goto v___jp_3429_;
}
v___jp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3425_, v___y_3426_, v_inputCtx_3417_);
lean_dec(v___x_3427_);
v___x_3428_ = l_IO_Promise_result_x21___redArg(v___x_3422_);
lean_dec(v___x_3422_);
return v___x_3428_;
}
v___jp_3429_:
{
uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3431_ = 1;
v___x_3432_ = lean_box(0);
v___x_3433_ = lean_box(v___x_3431_);
lean_inc(v___x_3422_);
v___x_3434_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3434_, 0, v___y_3430_);
lean_closure_set(v___x_3434_, 1, v_parserState_3418_);
lean_closure_set(v___x_3434_, 2, v_commandState_3419_);
lean_closure_set(v___x_3434_, 3, v___x_3422_);
lean_closure_set(v___x_3434_, 4, v___x_3433_);
lean_closure_set(v___x_3434_, 5, v___x_3423_);
lean_closure_set(v___x_3434_, 6, v___x_3432_);
if (lean_obj_tag(v_old_x3f_3420_) == 0)
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_box(0);
v___y_3425_ = v___x_3434_;
v___y_3426_ = v___x_3435_;
goto v___jp_3424_;
}
else
{
lean_object* v_val_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3444_; 
v_val_3436_ = lean_ctor_get(v_old_x3f_3420_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_old_x3f_3420_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3438_ = v_old_x3f_3420_;
v_isShared_3439_ = v_isSharedCheck_3444_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_val_3436_);
lean_dec(v_old_x3f_3420_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3444_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v___x_3442_; 
v_fst_3440_ = lean_ctor_get(v_val_3436_, 0);
lean_inc(v_fst_3440_);
lean_dec(v_val_3436_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v_fst_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_fst_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
v___y_3425_ = v___x_3434_;
v___y_3426_ = v___x_3442_;
goto v___jp_3424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3449_, lean_object* v_parserState_3450_, lean_object* v_commandState_3451_, lean_object* v_old_x3f_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3449_, v_parserState_3450_, v_commandState_3451_, v_old_x3f_3452_);
lean_dec_ref(v_inputCtx_3449_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3455_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3456_; 
v_nextCmdSnap_x3f_3456_ = lean_ctor_get(v_snap_3455_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3456_) == 1)
{
lean_object* v_val_3457_; lean_object* v___x_3458_; 
lean_inc_ref(v_nextCmdSnap_x3f_3456_);
lean_dec_ref(v_snap_3455_);
v_val_3457_ = lean_ctor_get(v_nextCmdSnap_x3f_3456_, 0);
lean_inc(v_val_3457_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3456_, 1);
v___x_3458_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3457_);
v_snap_3455_ = v___x_3458_;
goto _start;
}
else
{
lean_object* v_elabSnap_3460_; lean_object* v_resultSnap_3461_; lean_object* v___x_3462_; lean_object* v_cmdState_3463_; lean_object* v___x_3464_; 
v_elabSnap_3460_ = lean_ctor_get(v_snap_3455_, 3);
lean_inc_ref(v_elabSnap_3460_);
lean_dec_ref(v_snap_3455_);
v_resultSnap_3461_ = lean_ctor_get(v_elabSnap_3460_, 2);
lean_inc_ref(v_resultSnap_3461_);
lean_dec_ref(v_elabSnap_3460_);
v___x_3462_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3461_);
v_cmdState_3463_ = lean_ctor_get(v___x_3462_, 1);
lean_inc_ref(v_cmdState_3463_);
lean_dec(v___x_3462_);
v___x_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_cmdState_3463_);
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3465_){
_start:
{
lean_object* v_result_x3f_3466_; 
v_result_x3f_3466_ = lean_ctor_get(v_snap_3465_, 4);
lean_inc(v_result_x3f_3466_);
lean_dec_ref(v_snap_3465_);
if (lean_obj_tag(v_result_x3f_3466_) == 0)
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_box(0);
return v___x_3467_;
}
else
{
lean_object* v_val_3468_; lean_object* v_processedSnap_3469_; lean_object* v___x_3470_; lean_object* v_result_x3f_3471_; 
v_val_3468_ = lean_ctor_get(v_result_x3f_3466_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v_result_x3f_3466_, 1);
v_processedSnap_3469_ = lean_ctor_get(v_val_3468_, 1);
lean_inc_ref(v_processedSnap_3469_);
lean_dec(v_val_3468_);
v___x_3470_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3469_);
v_result_x3f_3471_ = lean_ctor_get(v___x_3470_, 2);
lean_inc(v_result_x3f_3471_);
lean_dec(v___x_3470_);
if (lean_obj_tag(v_result_x3f_3471_) == 0)
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_box(0);
return v___x_3472_;
}
else
{
lean_object* v_val_3473_; lean_object* v_firstCmdSnap_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_val_3473_ = lean_ctor_get(v_result_x3f_3471_, 0);
lean_inc(v_val_3473_);
lean_dec_ref_known(v_result_x3f_3471_, 1);
v_firstCmdSnap_3474_ = lean_ctor_get(v_val_3473_, 1);
lean_inc_ref(v_firstCmdSnap_3474_);
lean_dec(v_val_3473_);
v___x_3475_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3474_);
v___x_3476_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3475_);
return v___x_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3477_, lean_object* v_snap_3478_, lean_object* v_acc_3479_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3480_; lean_object* v_acc_3481_; 
v_nextCmdSnap_x3f_3480_ = lean_ctor_get(v_snap_3478_, 4);
lean_inc(v_nextCmdSnap_x3f_3480_);
lean_inc(v_f_3477_);
v_acc_3481_ = lean_apply_2(v_f_3477_, v_acc_3479_, v_snap_3478_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3480_) == 1)
{
lean_object* v_val_3482_; lean_object* v___x_3483_; 
v_val_3482_ = lean_ctor_get(v_nextCmdSnap_x3f_3480_, 0);
lean_inc(v_val_3482_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3480_, 1);
v___x_3483_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3482_);
v_snap_3478_ = v___x_3483_;
v_acc_3479_ = v_acc_3481_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3480_);
lean_dec(v_f_3477_);
return v_acc_3481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3485_, lean_object* v_f_3486_, lean_object* v_snap_3487_, lean_object* v_acc_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3486_, v_snap_3487_, v_acc_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3490_, lean_object* v_init_3491_, lean_object* v_f_3492_){
_start:
{
lean_object* v_result_x3f_3493_; 
v_result_x3f_3493_ = lean_ctor_get(v_snap_3490_, 4);
lean_inc(v_result_x3f_3493_);
lean_dec_ref(v_snap_3490_);
if (lean_obj_tag(v_result_x3f_3493_) == 0)
{
lean_object* v___x_3494_; 
lean_dec(v_f_3492_);
lean_dec(v_init_3491_);
v___x_3494_ = lean_box(0);
return v___x_3494_;
}
else
{
lean_object* v_val_3495_; lean_object* v_processedSnap_3496_; lean_object* v___x_3497_; lean_object* v_result_x3f_3498_; 
v_val_3495_ = lean_ctor_get(v_result_x3f_3493_, 0);
lean_inc(v_val_3495_);
lean_dec_ref_known(v_result_x3f_3493_, 1);
v_processedSnap_3496_ = lean_ctor_get(v_val_3495_, 1);
lean_inc_ref(v_processedSnap_3496_);
lean_dec(v_val_3495_);
v___x_3497_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3496_);
v_result_x3f_3498_ = lean_ctor_get(v___x_3497_, 2);
lean_inc(v_result_x3f_3498_);
lean_dec(v___x_3497_);
if (lean_obj_tag(v_result_x3f_3498_) == 0)
{
lean_object* v___x_3499_; 
lean_dec(v_f_3492_);
lean_dec(v_init_3491_);
v___x_3499_ = lean_box(0);
return v___x_3499_;
}
else
{
lean_object* v_val_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3510_; 
v_val_3500_ = lean_ctor_get(v_result_x3f_3498_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_result_x3f_3498_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3502_ = v_result_x3f_3498_;
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_val_3500_);
lean_dec(v_result_x3f_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_firstCmdSnap_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v_firstCmdSnap_3504_ = lean_ctor_get(v_val_3500_, 1);
lean_inc_ref(v_firstCmdSnap_3504_);
lean_dec(v_val_3500_);
v___x_3505_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3504_);
v___x_3506_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3492_, v___x_3505_, v_init_3491_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3506_);
v___x_3508_ = v___x_3502_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3511_, lean_object* v_snap_3512_, lean_object* v_init_3513_, lean_object* v_f_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3512_, v_init_3513_, v_f_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = 1;
v___x_3522_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3523_ = l_Lean_Name_toString(v___x_3522_, v___x_3521_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3524_ = 0;
v___x_3525_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3526_ = lean_box(0);
v___x_3527_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3528_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3529_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3527_);
lean_ctor_set(v___x_3529_, 2, v___x_3526_);
lean_ctor_set(v___x_3529_, 3, v___x_3525_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*4, v___x_3524_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3531_ = lean_box(0);
v___x_3532_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3531_, v___x_3530_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3533_){
_start:
{
lean_object* v_result_x3f_3534_; 
v_result_x3f_3534_ = lean_ctor_get(v_snap_3533_, 4);
lean_inc(v_result_x3f_3534_);
if (lean_obj_tag(v_result_x3f_3534_) == 1)
{
lean_object* v_val_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3610_; 
v_val_3535_ = lean_ctor_get(v_result_x3f_3534_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_result_x3f_3534_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3537_ = v_result_x3f_3534_;
v_isShared_3538_ = v_isSharedCheck_3610_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_val_3535_);
lean_dec(v_result_x3f_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3610_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v_toSnapshot_3539_; lean_object* v_metaSnap_3540_; lean_object* v_ictx_3541_; lean_object* v_stx_3542_; lean_object* v_parserState_3543_; lean_object* v_processedSnap_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3609_; 
v_toSnapshot_3539_ = lean_ctor_get(v_snap_3533_, 0);
v_metaSnap_3540_ = lean_ctor_get(v_snap_3533_, 1);
v_ictx_3541_ = lean_ctor_get(v_snap_3533_, 2);
v_stx_3542_ = lean_ctor_get(v_snap_3533_, 3);
v_parserState_3543_ = lean_ctor_get(v_val_3535_, 0);
v_processedSnap_3544_ = lean_ctor_get(v_val_3535_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_val_3535_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3546_ = v_val_3535_;
v_isShared_3547_ = v_isSharedCheck_3609_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_processedSnap_3544_);
lean_inc(v_parserState_3543_);
lean_dec(v_val_3535_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3609_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v_processed_3548_; lean_object* v_result_x3f_3549_; 
v_processed_3548_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3544_);
v_result_x3f_3549_ = lean_ctor_get(v_processed_3548_, 2);
lean_inc(v_result_x3f_3549_);
if (lean_obj_tag(v_result_x3f_3549_) == 1)
{
lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3603_; 
lean_inc(v_stx_3542_);
lean_inc_ref(v_ictx_3541_);
lean_inc_ref(v_metaSnap_3540_);
lean_inc_ref(v_toSnapshot_3539_);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_snap_3533_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; lean_object* v_unused_3607_; lean_object* v_unused_3608_; 
v_unused_3604_ = lean_ctor_get(v_snap_3533_, 4);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_snap_3533_, 3);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_snap_3533_, 2);
lean_dec(v_unused_3606_);
v_unused_3607_ = lean_ctor_get(v_snap_3533_, 1);
lean_dec(v_unused_3607_);
v_unused_3608_ = lean_ctor_get(v_snap_3533_, 0);
lean_dec(v_unused_3608_);
v___x_3551_ = v_snap_3533_;
v_isShared_3552_ = v_isSharedCheck_3603_;
goto v_resetjp_3550_;
}
else
{
lean_dec(v_snap_3533_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3603_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v_val_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3602_; 
v_val_3553_ = lean_ctor_get(v_result_x3f_3549_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_result_x3f_3549_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3555_ = v_result_x3f_3549_;
v_isShared_3556_ = v_isSharedCheck_3602_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_val_3553_);
lean_dec(v_result_x3f_3549_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3602_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_toSnapshot_3557_; lean_object* v_metaSnap_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3600_; 
v_toSnapshot_3557_ = lean_ctor_get(v_processed_3548_, 0);
v_metaSnap_3558_ = lean_ctor_get(v_processed_3548_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_processed_3548_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v_processed_3548_, 2);
lean_dec(v_unused_3601_);
v___x_3560_ = v_processed_3548_;
v_isShared_3561_ = v_isSharedCheck_3600_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_metaSnap_3558_);
lean_inc(v_toSnapshot_3557_);
lean_dec(v_processed_3548_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3600_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v_cmdState_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3598_; 
v_cmdState_3562_ = lean_ctor_get(v_val_3553_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_val_3553_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v_val_3553_, 1);
lean_dec(v_unused_3599_);
v___x_3564_ = v_val_3553_;
v_isShared_3565_ = v_isSharedCheck_3598_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_cmdState_3562_);
lean_dec(v_val_3553_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3598_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v_resultSnap_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v_elabSnap_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v_termCmd_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3566_ = lean_box(0);
v___x_3567_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3568_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3562_);
v_resultSnap_3569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3569_, 0, v___x_3567_);
lean_ctor_set(v_resultSnap_3569_, 1, v_cmdState_3562_);
lean_ctor_set(v_resultSnap_3569_, 2, v___x_3568_);
v___x_3570_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3571_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3566_, v_resultSnap_3569_);
v___x_3572_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3573_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3574_, 0, v___x_3567_);
lean_ctor_set(v_elabSnap_3574_, 1, v___x_3570_);
lean_ctor_set(v_elabSnap_3574_, 2, v___x_3571_);
lean_ctor_set(v_elabSnap_3574_, 3, v___x_3572_);
lean_ctor_set(v_elabSnap_3574_, 4, v___x_3573_);
v___x_3575_ = lean_box(0);
v___x_3576_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3577_, 0, v___x_3567_);
lean_ctor_set(v_termCmd_3577_, 1, v___x_3575_);
lean_ctor_set(v_termCmd_3577_, 2, v___x_3576_);
lean_ctor_set(v_termCmd_3577_, 3, v_elabSnap_3574_);
lean_ctor_set(v_termCmd_3577_, 4, v___x_3566_);
v___x_3578_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3566_, v_termCmd_3577_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3578_);
v___x_3580_ = v___x_3564_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_cmdState_3562_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3582_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3580_);
v___x_3582_ = v___x_3555_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v_newProcessed_3584_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 2, v___x_3582_);
v_newProcessed_3584_ = v___x_3560_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_toSnapshot_3557_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_metaSnap_3558_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v___x_3582_);
v_newProcessed_3584_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3585_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3566_, v_newProcessed_3584_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 1, v___x_3585_);
v___x_3587_ = v___x_3546_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_parserState_3543_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3587_);
v___x_3589_ = v___x_3537_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 4, v___x_3589_);
v___x_3591_ = v___x_3551_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_toSnapshot_3539_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_metaSnap_3540_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_ictx_3541_);
lean_ctor_set(v_reuseFailAlloc_3592_, 3, v_stx_3542_);
lean_ctor_set(v_reuseFailAlloc_3592_, 4, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
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
lean_dec(v_result_x3f_3549_);
lean_dec(v_processed_3548_);
lean_del_object(v___x_3546_);
lean_dec_ref(v_parserState_3543_);
lean_del_object(v___x_3537_);
return v_snap_3533_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3534_);
return v_snap_3533_;
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

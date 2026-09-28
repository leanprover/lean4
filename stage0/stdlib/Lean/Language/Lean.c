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
lean_object* v___x_642_; lean_object* v_env_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_scopes_646_; lean_object* v___x_647_; lean_object* v_opts_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_642_ = lean_st_ref_get(v___y_640_);
v_env_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_env_643_);
lean_dec(v___x_642_);
v___x_644_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_645_ = lean_st_ref_get(v___y_640_);
v_scopes_646_ = lean_ctor_get(v___x_645_, 2);
lean_inc(v_scopes_646_);
lean_dec(v___x_645_);
v___x_647_ = l_List_head_x21___redArg(v___x_644_, v_scopes_646_);
lean_dec(v_scopes_646_);
v_opts_648_ = lean_ctor_get(v___x_647_, 1);
lean_inc_ref(v_opts_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_650_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_651_, 0, v_env_643_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
lean_ctor_set(v___x_651_, 3, v_opts_648_);
v___x_652_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_msgData_639_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_654_, v___y_655_);
lean_dec(v___y_655_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_658_, uint8_t v___y_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_660_) == 1)
{
lean_object* v_pre_661_; 
v_pre_661_ = lean_ctor_get(v_x_660_, 0);
if (lean_obj_tag(v_pre_661_) == 0)
{
lean_object* v_str_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_str_662_ = lean_ctor_get(v_x_660_, 1);
v___x_663_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_664_ = lean_string_dec_eq(v_str_662_, v___x_663_);
if (v___x_664_ == 0)
{
return v___x_664_;
}
else
{
return v_suppressElabErrors_658_;
}
}
else
{
return v___y_659_;
}
}
else
{
return v___y_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_665_, lean_object* v___y_666_, lean_object* v_x_667_){
_start:
{
uint8_t v_suppressElabErrors_boxed_668_; uint8_t v___y_9361__boxed_669_; uint8_t v_res_670_; lean_object* v_r_671_; 
v_suppressElabErrors_boxed_668_ = lean_unbox(v_suppressElabErrors_665_);
v___y_9361__boxed_669_ = lean_unbox(v___y_666_);
v_res_670_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_668_, v___y_9361__boxed_669_, v_x_667_);
lean_dec(v_x_667_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_673_, lean_object* v_msgData_674_, uint8_t v_severity_675_, uint8_t v_isSilent_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; uint8_t v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; uint8_t v___y_746_; uint8_t v___y_747_; lean_object* v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; uint8_t v___y_774_; uint8_t v___y_775_; lean_object* v___y_776_; uint8_t v___y_777_; lean_object* v___y_778_; uint8_t v___y_782_; uint8_t v___y_783_; uint8_t v___y_784_; uint8_t v___x_799_; uint8_t v___y_801_; uint8_t v___y_802_; uint8_t v___y_803_; uint8_t v___y_805_; uint8_t v___x_817_; 
v___x_799_ = 2;
v___x_817_ = l_Lean_instBEqMessageSeverity_beq(v_severity_675_, v___x_799_);
if (v___x_817_ == 0)
{
v___y_805_ = v___x_817_;
goto v___jp_804_;
}
else
{
uint8_t v___x_818_; 
lean_inc_ref(v_msgData_674_);
v___x_818_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_674_);
v___y_805_ = v___x_818_;
goto v___jp_804_;
}
v___jp_680_:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_Command_getScope___redArg(v___y_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v_currNamespace_691_; lean_object* v___x_692_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v_currNamespace_691_ = lean_ctor_get(v_a_690_, 2);
lean_inc(v_currNamespace_691_);
lean_dec(v_a_690_);
v___x_692_ = l_Lean_Elab_Command_getScope___redArg(v___y_688_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_728_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_728_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_728_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_728_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_openDecls_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_env_702_; lean_object* v_messages_703_; lean_object* v_scopes_704_; lean_object* v_usedQuotCtxts_705_; lean_object* v_nextMacroScope_706_; lean_object* v_maxRecDepth_707_; lean_object* v_ngen_708_; lean_object* v_auxDeclNGen_709_; lean_object* v_infoState_710_; lean_object* v_traceState_711_; lean_object* v_snapshotTasks_712_; lean_object* v_prevLinterStates_713_; lean_object* v_codeQualityEntryTasks_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_727_; 
v_openDecls_697_ = lean_ctor_get(v_a_693_, 3);
lean_inc(v_openDecls_697_);
lean_dec(v_a_693_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_currNamespace_691_);
lean_ctor_set(v___x_698_, 1, v_openDecls_697_);
v___x_699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___y_682_);
lean_inc_ref(v___y_681_);
lean_inc_ref(v___y_686_);
v___x_700_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_700_, 0, v___y_686_);
lean_ctor_set(v___x_700_, 1, v___y_683_);
lean_ctor_set(v___x_700_, 2, v___y_685_);
lean_ctor_set(v___x_700_, 3, v___y_681_);
lean_ctor_set(v___x_700_, 4, v___x_699_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5, v___y_687_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 1, v___y_684_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 2, v_isSilent_676_);
v___x_701_ = lean_st_ref_take(v___y_688_);
v_env_702_ = lean_ctor_get(v___x_701_, 0);
v_messages_703_ = lean_ctor_get(v___x_701_, 1);
v_scopes_704_ = lean_ctor_get(v___x_701_, 2);
v_usedQuotCtxts_705_ = lean_ctor_get(v___x_701_, 3);
v_nextMacroScope_706_ = lean_ctor_get(v___x_701_, 4);
v_maxRecDepth_707_ = lean_ctor_get(v___x_701_, 5);
v_ngen_708_ = lean_ctor_get(v___x_701_, 6);
v_auxDeclNGen_709_ = lean_ctor_get(v___x_701_, 7);
v_infoState_710_ = lean_ctor_get(v___x_701_, 8);
v_traceState_711_ = lean_ctor_get(v___x_701_, 9);
v_snapshotTasks_712_ = lean_ctor_get(v___x_701_, 10);
v_prevLinterStates_713_ = lean_ctor_get(v___x_701_, 11);
v_codeQualityEntryTasks_714_ = lean_ctor_get(v___x_701_, 12);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_727_ == 0)
{
v___x_716_ = v___x_701_;
v_isShared_717_ = v_isSharedCheck_727_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_codeQualityEntryTasks_714_);
lean_inc(v_prevLinterStates_713_);
lean_inc(v_snapshotTasks_712_);
lean_inc(v_traceState_711_);
lean_inc(v_infoState_710_);
lean_inc(v_auxDeclNGen_709_);
lean_inc(v_ngen_708_);
lean_inc(v_maxRecDepth_707_);
lean_inc(v_nextMacroScope_706_);
lean_inc(v_usedQuotCtxts_705_);
lean_inc(v_scopes_704_);
lean_inc(v_messages_703_);
lean_inc(v_env_702_);
lean_dec(v___x_701_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_727_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_MessageLog_add(v___x_700_, v_messages_703_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_719_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_env_702_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_scopes_704_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_usedQuotCtxts_705_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_nextMacroScope_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v_maxRecDepth_707_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_ngen_708_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v_auxDeclNGen_709_);
lean_ctor_set(v_reuseFailAlloc_726_, 8, v_infoState_710_);
lean_ctor_set(v_reuseFailAlloc_726_, 9, v_traceState_711_);
lean_ctor_set(v_reuseFailAlloc_726_, 10, v_snapshotTasks_712_);
lean_ctor_set(v_reuseFailAlloc_726_, 11, v_prevLinterStates_713_);
lean_ctor_set(v_reuseFailAlloc_726_, 12, v_codeQualityEntryTasks_714_);
v___x_721_ = v_reuseFailAlloc_726_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_st_ref_put(v___y_688_, v___x_721_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_718_);
v___x_724_ = v___x_695_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_718_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v_currNamespace_691_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v___y_682_);
v_a_729_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_692_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_692_);
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
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___y_685_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v___y_682_);
v_a_737_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_689_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_689_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
v___jp_745_:
{
lean_object* v_fileName_751_; lean_object* v_fileMap_752_; uint8_t v_suppressElabErrors_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_772_; 
v_fileName_751_ = lean_ctor_get(v___y_677_, 0);
v_fileMap_752_ = lean_ctor_get(v___y_677_, 1);
v_suppressElabErrors_753_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*10);
v___x_754_ = lean_box(v_suppressElabErrors_753_);
v___x_755_ = lean_box(v___y_746_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_756_, 0, v___x_754_);
lean_closure_set(v___f_756_, 1, v___x_755_);
v___x_757_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_674_);
v___x_758_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_757_, v___y_678_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_772_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_772_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_772_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_inc_ref_n(v_fileMap_752_, 2);
v___x_763_ = l_Lean_FileMap_toPosition(v_fileMap_752_, v___y_748_);
lean_dec(v___y_748_);
v___x_764_ = l_Lean_FileMap_toPosition(v_fileMap_752_, v___y_750_);
lean_dec(v___y_750_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_753_ == 0)
{
lean_del_object(v___x_761_);
lean_dec_ref(v___f_756_);
v___y_681_ = v___x_766_;
v___y_682_ = v_a_759_;
v___y_683_ = v___x_763_;
v___y_684_ = v___y_747_;
v___y_685_ = v___x_765_;
v___y_686_ = v_fileName_751_;
v___y_687_ = v___y_749_;
v___y_688_ = v___y_678_;
goto v___jp_680_;
}
else
{
uint8_t v___x_767_; 
lean_inc(v_a_759_);
v___x_767_ = l_Lean_MessageData_hasTag(v___f_756_, v_a_759_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
lean_dec_ref_known(v___x_765_, 1);
lean_dec_ref(v___x_763_);
lean_dec(v_a_759_);
v___x_768_ = lean_box(0);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_768_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_del_object(v___x_761_);
v___y_681_ = v___x_766_;
v___y_682_ = v_a_759_;
v___y_683_ = v___x_763_;
v___y_684_ = v___y_747_;
v___y_685_ = v___x_765_;
v___y_686_ = v_fileName_751_;
v___y_687_ = v___y_749_;
v___y_688_ = v___y_678_;
goto v___jp_680_;
}
}
}
}
v___jp_773_:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Syntax_getTailPos_x3f(v___y_776_, v___y_777_);
lean_dec(v___y_776_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_inc(v___y_778_);
v___y_746_ = v___y_774_;
v___y_747_ = v___y_775_;
v___y_748_ = v___y_778_;
v___y_749_ = v___y_777_;
v___y_750_ = v___y_778_;
goto v___jp_745_;
}
else
{
lean_object* v_val_780_; 
v_val_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v___x_779_, 1);
v___y_746_ = v___y_774_;
v___y_747_ = v___y_775_;
v___y_748_ = v___y_778_;
v___y_749_ = v___y_777_;
v___y_750_ = v_val_780_;
goto v___jp_745_;
}
}
v___jp_781_:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Elab_Command_getRef___redArg(v___y_677_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_ref_787_; lean_object* v___x_788_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v_ref_787_ = l_Lean_replaceRef(v_ref_673_, v_a_786_);
lean_dec(v_a_786_);
v___x_788_ = l_Lean_Syntax_getPos_x3f(v_ref_787_, v___y_783_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_unsigned_to_nat(0u);
v___y_774_ = v___y_782_;
v___y_775_ = v___y_784_;
v___y_776_ = v_ref_787_;
v___y_777_ = v___y_783_;
v___y_778_ = v___x_789_;
goto v___jp_773_;
}
else
{
lean_object* v_val_790_; 
v_val_790_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v___x_788_, 1);
v___y_774_ = v___y_782_;
v___y_775_ = v___y_784_;
v___y_776_ = v_ref_787_;
v___y_777_ = v___y_783_;
v___y_778_ = v_val_790_;
goto v___jp_773_;
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_msgData_674_);
v_a_791_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_785_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_785_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
v___jp_800_:
{
if (v___y_803_ == 0)
{
v___y_782_ = v___y_801_;
v___y_783_ = v___y_802_;
v___y_784_ = v_severity_675_;
goto v___jp_781_;
}
else
{
v___y_782_ = v___y_801_;
v___y_783_ = v___y_802_;
v___y_784_ = v___x_799_;
goto v___jp_781_;
}
}
v___jp_804_:
{
if (v___y_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_scopes_808_; lean_object* v___x_809_; lean_object* v_opts_810_; uint8_t v___x_811_; uint8_t v___x_812_; 
v___x_806_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_807_ = lean_st_ref_get(v___y_678_);
v_scopes_808_ = lean_ctor_get(v___x_807_, 2);
lean_inc(v_scopes_808_);
lean_dec(v___x_807_);
v___x_809_ = l_List_head_x21___redArg(v___x_806_, v_scopes_808_);
lean_dec(v_scopes_808_);
v_opts_810_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref(v_opts_810_);
lean_dec(v___x_809_);
v___x_811_ = 1;
v___x_812_ = l_Lean_instBEqMessageSeverity_beq(v_severity_675_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v_opts_810_);
v___y_801_ = v___y_805_;
v___y_802_ = v___y_805_;
v___y_803_ = v___x_812_;
goto v___jp_800_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = l_Lean_warningAsError;
v___x_814_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_810_, v___x_813_);
lean_dec_ref(v_opts_810_);
v___y_801_ = v___y_805_;
v___y_802_ = v___y_805_;
v___y_803_ = v___x_814_;
goto v___jp_800_;
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref(v_msgData_674_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_819_, lean_object* v_msgData_820_, lean_object* v_severity_821_, lean_object* v_isSilent_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_severity_boxed_826_; uint8_t v_isSilent_boxed_827_; lean_object* v_res_828_; 
v_severity_boxed_826_ = lean_unbox(v_severity_821_);
v_isSilent_boxed_827_ = lean_unbox(v_isSilent_822_);
v_res_828_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_819_, v_msgData_820_, v_severity_boxed_826_, v_isSilent_boxed_827_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v_ref_819_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_829_, uint8_t v_severity_830_, uint8_t v_isSilent_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Elab_Command_getRef___redArg(v___y_832_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_837_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_836_, v_msgData_829_, v_severity_830_, v_isSilent_831_, v___y_832_, v___y_833_);
lean_dec(v_a_836_);
return v___x_837_;
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v_msgData_829_);
v_a_838_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_835_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_835_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_846_, lean_object* v_severity_847_, lean_object* v_isSilent_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v_severity_boxed_852_; uint8_t v_isSilent_boxed_853_; lean_object* v_res_854_; 
v_severity_boxed_852_ = lean_unbox(v_severity_847_);
v_isSilent_boxed_853_ = lean_unbox(v_isSilent_848_);
v_res_854_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_846_, v_severity_boxed_852_, v_isSilent_boxed_853_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 2;
v___x_860_ = 0;
v___x_861_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_855_, v___x_859_, v___x_860_, v___y_856_, v___y_857_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_867_, lean_object* v_msgData_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; 
v___x_872_ = 2;
v___x_873_ = 0;
v___x_874_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_867_, v_msgData_868_, v___x_872_, v___x_873_, v___y_869_, v___y_870_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_875_, lean_object* v_msgData_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_875_, v_msgData_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v_ref_875_);
return v_res_880_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (lean_obj_tag(v_ex_884_) == 0)
{
lean_object* v_ref_888_; lean_object* v_msg_889_; lean_object* v___x_890_; 
v_ref_888_ = lean_ctor_get(v_ex_884_, 0);
lean_inc(v_ref_888_);
v_msg_889_ = lean_ctor_get(v_ex_884_, 1);
lean_inc_ref(v_msg_889_);
lean_dec_ref_known(v_ex_884_, 2);
v___x_890_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_888_, v_msg_889_, v___y_885_, v___y_886_);
lean_dec(v_ref_888_);
return v___x_890_;
}
else
{
lean_object* v_id_891_; uint8_t v___y_893_; uint8_t v___x_915_; 
v_id_891_ = lean_ctor_get(v_ex_884_, 0);
lean_inc(v_id_891_);
v___x_915_ = l_Lean_Elab_isAbortExceptionId(v_id_891_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_Exception_isInterrupt(v_ex_884_);
lean_dec_ref_known(v_ex_884_, 2);
v___y_893_ = v___x_916_;
goto v___jp_892_;
}
else
{
lean_dec_ref_known(v_ex_884_, 2);
v___y_893_ = v___x_915_;
goto v___jp_892_;
}
v___jp_892_:
{
if (v___y_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_InternalExceptionId_getName(v_id_891_);
lean_dec(v_id_891_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_897_ = l_Lean_MessageData_ofName(v_a_895_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_898_, v___y_885_, v___y_886_);
return v___x_899_;
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_912_; 
v_a_900_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_912_ == 0)
{
v___x_902_ = v___x_894_;
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_894_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_ref_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v_ref_904_ = lean_ctor_get(v___y_885_, 7);
v___x_905_ = lean_io_error_to_string(v_a_900_);
v___x_906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = l_Lean_MessageData_ofFormat(v___x_906_);
lean_inc(v_ref_904_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_ref_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_908_);
v___x_910_ = v___x_902_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_id_891_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
v___x_926_ = lean_apply_3(v_x_922_, v___y_923_, v___y_924_, lean_box(0));
if (lean_obj_tag(v___x_926_) == 0)
{
return v___x_926_;
}
else
{
lean_object* v_a_927_; uint8_t v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
v___x_928_ = l_Lean_Exception_isInterrupt(v_a_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec_ref_known(v___x_926_, 1);
v___x_929_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_927_, v___y_923_, v___y_924_);
return v___x_929_;
}
else
{
lean_dec(v_a_927_);
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_935_, lean_object* v___x_936_, lean_object* v_val_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_a_941_; lean_object* v___x_943_; 
v___x_943_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_935_, v___x_936_, v_val_937_);
if (lean_obj_tag(v___x_943_) == 0)
{
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v_a_941_ = v_a_944_;
goto v___jp_940_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_a_945_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v___x_953_; 
lean_dec_ref_known(v___x_943_, 1);
v___x_953_ = lean_box(0);
v_a_941_ = v___x_953_;
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_a_941_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_954_, lean_object* v___x_955_, lean_object* v_val_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_954_, v___x_955_, v_val_956_, v___y_957_);
lean_dec_ref(v___y_957_);
lean_dec(v_val_956_);
lean_dec_ref(v___x_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_960_, lean_object* v_x_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_get_set_stderr(v_h_960_);
lean_inc_ref(v___y_962_);
v___x_965_ = lean_apply_2(v_x_961_, v___y_962_, lean_box(0));
v___x_966_ = lean_get_set_stderr(v___x_964_);
lean_dec_ref(v___x_966_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_967_, v_x_968_, v___y_969_);
lean_dec_ref(v___y_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_972_, lean_object* v_h_973_, lean_object* v_x_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_973_, v_x_974_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_978_, lean_object* v_h_979_, lean_object* v_x_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_978_, v_h_979_, v_x_980_, v___y_981_);
lean_dec_ref(v___y_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_984_, lean_object* v_x_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_get_set_stdin(v_h_984_);
lean_inc_ref(v___y_986_);
v___x_989_ = lean_apply_2(v_x_985_, v___y_986_, lean_box(0));
v___x_990_ = lean_get_set_stdin(v___x_988_);
lean_dec_ref(v___x_990_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_991_, v_x_992_, v___y_993_);
lean_dec_ref(v___y_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_998_ = lean_panic_fn_borrowed(v___x_997_, v_msg_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_999_, lean_object* v_x_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_get_set_stdout(v_h_999_);
lean_inc_ref(v___y_1001_);
v___x_1004_ = lean_apply_2(v_x_1000_, v___y_1001_, lean_box(0));
v___x_1005_ = lean_get_set_stdout(v___x_1003_);
lean_dec_ref(v___x_1005_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1006_, v_x_1007_, v___y_1008_);
lean_dec_ref(v___y_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_1011_, lean_object* v_h_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_1012_, v_x_1013_, v___y_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1017_, lean_object* v_h_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1017_, v_h_1018_, v_x_1019_, v___y_1020_);
lean_dec_ref(v___y_1020_);
return v_res_1022_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_ByteArray_empty;
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1029_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1030_ = lean_unsigned_to_nat(46u);
v___x_1031_ = lean_unsigned_to_nat(193u);
v___x_1032_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1033_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1034_ = l_mkPanicMessageWithDecl(v___x_1033_, v___x_1032_, v___x_1031_, v___x_1030_, v___x_1029_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1035_, uint8_t v_isolateStderr_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___y_1049_; 
v___x_1043_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1044_ = lean_st_mk_ref(v___x_1043_);
v___x_1045_ = lean_st_mk_ref(v___x_1043_);
v___x_1046_ = l_IO_FS_Stream_ofBuffer(v___x_1044_);
lean_inc(v___x_1045_);
v___x_1047_ = l_IO_FS_Stream_ofBuffer(v___x_1045_);
if (v_isolateStderr_1036_ == 0)
{
v___y_1049_ = v_x_1035_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1058_; 
lean_inc_ref(v___x_1047_);
v___x_1058_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1058_, 0, lean_box(0));
lean_closure_set(v___x_1058_, 1, v___x_1047_);
lean_closure_set(v___x_1058_, 2, v_x_1035_);
v___y_1049_ = v___x_1058_;
goto v___jp_1048_;
}
v___jp_1039_:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___y_1041_);
lean_ctor_set(v___x_1042_, 1, v___y_1040_);
return v___x_1042_;
}
v___jp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_data_1053_; uint8_t v___x_1054_; 
v___x_1050_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1050_, 0, lean_box(0));
lean_closure_set(v___x_1050_, 1, v___x_1047_);
lean_closure_set(v___x_1050_, 2, v___y_1049_);
v___x_1051_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1046_, v___x_1050_, v___y_1037_);
v___x_1052_ = lean_st_ref_get(v___x_1045_);
lean_dec(v___x_1045_);
v_data_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_data_1053_);
lean_dec(v___x_1052_);
v___x_1054_ = lean_string_validate_utf8(v_data_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec_ref(v_data_1053_);
v___x_1055_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1056_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1055_);
v___y_1040_ = v___x_1051_;
v___y_1041_ = v___x_1056_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_string_from_utf8_unchecked(v_data_1053_);
v___y_1040_ = v___x_1051_;
v___y_1041_ = v___x_1057_;
goto v___jp_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1059_, lean_object* v_isolateStderr_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v_isolateStderr_boxed_1063_; lean_object* v_res_1064_; 
v_isolateStderr_boxed_1063_ = lean_unbox(v_isolateStderr_1060_);
v_res_1064_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1059_, v_isolateStderr_boxed_1063_, v___y_1061_);
lean_dec_ref(v___y_1061_);
return v_res_1064_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = 1;
v___x_1074_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1075_ = l_Lean_Name_toString(v___x_1074_, v___x_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1076_, lean_object* v_revCmds_1077_, lean_object* v_cmdState_1078_, lean_object* v_beginPos_1079_, lean_object* v_snap_1080_, lean_object* v_cancelTk_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_env_1084_; lean_object* v_scopes_1085_; lean_object* v_usedQuotCtxts_1086_; lean_object* v_nextMacroScope_1087_; lean_object* v_maxRecDepth_1088_; lean_object* v_ngen_1089_; lean_object* v_auxDeclNGen_1090_; lean_object* v_infoState_1091_; lean_object* v_prevLinterStates_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1174_; 
v_env_1084_ = lean_ctor_get(v_cmdState_1078_, 0);
v_scopes_1085_ = lean_ctor_get(v_cmdState_1078_, 2);
v_usedQuotCtxts_1086_ = lean_ctor_get(v_cmdState_1078_, 3);
v_nextMacroScope_1087_ = lean_ctor_get(v_cmdState_1078_, 4);
v_maxRecDepth_1088_ = lean_ctor_get(v_cmdState_1078_, 5);
v_ngen_1089_ = lean_ctor_get(v_cmdState_1078_, 6);
v_auxDeclNGen_1090_ = lean_ctor_get(v_cmdState_1078_, 7);
v_infoState_1091_ = lean_ctor_get(v_cmdState_1078_, 8);
v_prevLinterStates_1092_ = lean_ctor_get(v_cmdState_1078_, 11);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_cmdState_1078_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1175_ = lean_ctor_get(v_cmdState_1078_, 12);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_cmdState_1078_, 10);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_cmdState_1078_, 9);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_cmdState_1078_, 1);
lean_dec(v_unused_1178_);
v___x_1094_ = v_cmdState_1078_;
v_isShared_1095_ = v_isSharedCheck_1174_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_prevLinterStates_1092_);
lean_inc(v_infoState_1091_);
lean_inc(v_auxDeclNGen_1090_);
lean_inc(v_ngen_1089_);
lean_inc(v_maxRecDepth_1088_);
lean_inc(v_nextMacroScope_1087_);
lean_inc(v_usedQuotCtxts_1086_);
lean_inc(v_scopes_1085_);
lean_inc(v_env_1084_);
lean_dec(v_cmdState_1078_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1174_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___f_1096_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1096_, 0, v_stx_1076_);
lean_closure_set(v___f_1096_, 1, v_revCmds_1077_);
v___x_1097_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1098_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1099_ = l_List_head_x21___redArg(v___x_1097_, v_scopes_1085_);
v___x_1100_ = l_Lean_MessageLog_empty;
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1103_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 12, v___x_1103_);
lean_ctor_set(v___x_1094_, 10, v___x_1103_);
lean_ctor_set(v___x_1094_, 9, v___x_1102_);
lean_ctor_set(v___x_1094_, 1, v___x_1100_);
v___x_1105_ = v___x_1094_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_env_1084_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_scopes_1085_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_usedQuotCtxts_1086_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_nextMacroScope_1087_);
lean_ctor_set(v_reuseFailAlloc_1173_, 5, v_maxRecDepth_1088_);
lean_ctor_set(v_reuseFailAlloc_1173_, 6, v_ngen_1089_);
lean_ctor_set(v_reuseFailAlloc_1173_, 7, v_auxDeclNGen_1090_);
lean_ctor_set(v_reuseFailAlloc_1173_, 8, v_infoState_1091_);
lean_ctor_set(v_reuseFailAlloc_1173_, 9, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1173_, 10, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1173_, 11, v_prevLinterStates_1092_);
lean_ctor_set(v_reuseFailAlloc_1173_, 12, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v_toProcessingContext_1107_; lean_object* v_fileName_1108_; lean_object* v_fileMap_1109_; lean_object* v_opts_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v_env_1118_; lean_object* v_scopes_1119_; lean_object* v_usedQuotCtxts_1120_; lean_object* v_nextMacroScope_1121_; lean_object* v_maxRecDepth_1122_; lean_object* v_ngen_1123_; lean_object* v_auxDeclNGen_1124_; lean_object* v_infoState_1125_; lean_object* v_traceState_1126_; lean_object* v_snapshotTasks_1127_; lean_object* v_prevLinterStates_1128_; lean_object* v_codeQualityEntryTasks_1129_; uint8_t v___y_1130_; lean_object* v_messages_1131_; lean_object* v___y_1140_; 
v___x_1106_ = lean_st_mk_ref(v___x_1105_);
v_toProcessingContext_1107_ = lean_ctor_get(v_a_1082_, 0);
v_fileName_1108_ = lean_ctor_get(v_toProcessingContext_1107_, 1);
v_fileMap_1109_ = lean_ctor_get(v_toProcessingContext_1107_, 2);
v_opts_1110_ = lean_ctor_get(v___x_1099_, 1);
lean_inc_ref(v_opts_1110_);
lean_dec(v___x_1099_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Lean_firstFrontendMacroScope;
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Lean_internal_cmdlineSnapshots;
v___x_1116_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1110_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1172_; 
lean_inc_ref(v_snap_1080_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_snap_1080_);
v___y_1140_ = v___x_1172_;
goto v___jp_1139_;
}
else
{
v___y_1140_ = v___x_1112_;
goto v___jp_1139_;
}
v___jp_1117_:
{
lean_object* v_new_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_new_1132_ = lean_ctor_get(v_snap_1080_, 1);
lean_inc(v_new_1132_);
lean_dec_ref(v_snap_1080_);
v___x_1133_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1133_, 0, v_env_1118_);
lean_ctor_set(v___x_1133_, 1, v_messages_1131_);
lean_ctor_set(v___x_1133_, 2, v_scopes_1119_);
lean_ctor_set(v___x_1133_, 3, v_usedQuotCtxts_1120_);
lean_ctor_set(v___x_1133_, 4, v_nextMacroScope_1121_);
lean_ctor_set(v___x_1133_, 5, v_maxRecDepth_1122_);
lean_ctor_set(v___x_1133_, 6, v_ngen_1123_);
lean_ctor_set(v___x_1133_, 7, v_auxDeclNGen_1124_);
lean_ctor_set(v___x_1133_, 8, v_infoState_1125_);
lean_ctor_set(v___x_1133_, 9, v_traceState_1126_);
lean_ctor_set(v___x_1133_, 10, v_snapshotTasks_1127_);
lean_ctor_set(v___x_1133_, 11, v_prevLinterStates_1128_);
lean_ctor_set(v___x_1133_, 12, v_codeQualityEntryTasks_1129_);
v___x_1134_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1135_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1136_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1112_);
lean_ctor_set(v___x_1136_, 3, v___x_1102_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*4, v___y_1130_);
v___x_1137_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1098_, v___x_1136_);
v___x_1138_ = lean_io_promise_resolve(v___x_1137_, v_new_1132_);
lean_dec(v_new_1132_);
return v___x_1133_;
}
v___jp_1139_:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v_fst_1148_; lean_object* v___x_1149_; lean_object* v_env_1150_; lean_object* v_messages_1151_; lean_object* v_scopes_1152_; lean_object* v_usedQuotCtxts_1153_; lean_object* v_nextMacroScope_1154_; lean_object* v_maxRecDepth_1155_; lean_object* v_ngen_1156_; lean_object* v_auxDeclNGen_1157_; lean_object* v_infoState_1158_; lean_object* v_traceState_1159_; lean_object* v_snapshotTasks_1160_; lean_object* v_prevLinterStates_1161_; lean_object* v_codeQualityEntryTasks_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_cancelTk_1081_);
v___x_1142_ = 0;
lean_inc(v_beginPos_1079_);
lean_inc_ref(v_fileMap_1109_);
lean_inc_ref(v_fileName_1108_);
v___x_1143_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1143_, 0, v_fileName_1108_);
lean_ctor_set(v___x_1143_, 1, v_fileMap_1109_);
lean_ctor_set(v___x_1143_, 2, v___x_1101_);
lean_ctor_set(v___x_1143_, 3, v_beginPos_1079_);
lean_ctor_set(v___x_1143_, 4, v___x_1111_);
lean_ctor_set(v___x_1143_, 5, v___x_1112_);
lean_ctor_set(v___x_1143_, 6, v___x_1113_);
lean_ctor_set(v___x_1143_, 7, v___x_1114_);
lean_ctor_set(v___x_1143_, 8, v___y_1140_);
lean_ctor_set(v___x_1143_, 9, v___x_1141_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*10, v___x_1142_);
lean_inc(v___x_1106_);
v___f_1144_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1144_, 0, v___f_1096_);
lean_closure_set(v___f_1144_, 1, v___x_1143_);
lean_closure_set(v___f_1144_, 2, v___x_1106_);
v___x_1145_ = l_Lean_Core_stderrAsMessages;
v___x_1146_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1110_, v___x_1145_);
lean_dec_ref(v_opts_1110_);
v___x_1147_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1144_, v___x_1146_, v_a_1082_);
v_fst_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_fst_1148_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = lean_st_ref_get(v___x_1106_);
lean_dec(v___x_1106_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_env_1150_);
v_messages_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc_ref(v_messages_1151_);
v_scopes_1152_ = lean_ctor_get(v___x_1149_, 2);
lean_inc(v_scopes_1152_);
v_usedQuotCtxts_1153_ = lean_ctor_get(v___x_1149_, 3);
lean_inc(v_usedQuotCtxts_1153_);
v_nextMacroScope_1154_ = lean_ctor_get(v___x_1149_, 4);
lean_inc(v_nextMacroScope_1154_);
v_maxRecDepth_1155_ = lean_ctor_get(v___x_1149_, 5);
lean_inc(v_maxRecDepth_1155_);
v_ngen_1156_ = lean_ctor_get(v___x_1149_, 6);
lean_inc_ref(v_ngen_1156_);
v_auxDeclNGen_1157_ = lean_ctor_get(v___x_1149_, 7);
lean_inc_ref(v_auxDeclNGen_1157_);
v_infoState_1158_ = lean_ctor_get(v___x_1149_, 8);
lean_inc_ref(v_infoState_1158_);
v_traceState_1159_ = lean_ctor_get(v___x_1149_, 9);
lean_inc_ref(v_traceState_1159_);
v_snapshotTasks_1160_ = lean_ctor_get(v___x_1149_, 10);
lean_inc_ref(v_snapshotTasks_1160_);
v_prevLinterStates_1161_ = lean_ctor_get(v___x_1149_, 11);
lean_inc(v_prevLinterStates_1161_);
v_codeQualityEntryTasks_1162_ = lean_ctor_get(v___x_1149_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1162_);
lean_dec(v___x_1149_);
v___x_1163_ = lean_string_utf8_byte_size(v_fst_1148_);
v___x_1164_ = lean_nat_dec_eq(v___x_1163_, v___x_1101_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_inc_ref(v_fileMap_1109_);
v___x_1165_ = l_Lean_FileMap_toPosition(v_fileMap_1109_, v_beginPos_1079_);
lean_dec(v_beginPos_1079_);
v___x_1166_ = 0;
v___x_1167_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_fst_1148_);
v___x_1169_ = l_Lean_MessageData_ofFormat(v___x_1168_);
lean_inc_ref(v_fileName_1108_);
v___x_1170_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1170_, 0, v_fileName_1108_);
lean_ctor_set(v___x_1170_, 1, v___x_1165_);
lean_ctor_set(v___x_1170_, 2, v___x_1112_);
lean_ctor_set(v___x_1170_, 3, v___x_1167_);
lean_ctor_set(v___x_1170_, 4, v___x_1169_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*5, v___x_1142_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*5 + 1, v___x_1166_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*5 + 2, v___x_1142_);
v___x_1171_ = l_Lean_MessageLog_add(v___x_1170_, v_messages_1151_);
v_env_1118_ = v_env_1150_;
v_scopes_1119_ = v_scopes_1152_;
v_usedQuotCtxts_1120_ = v_usedQuotCtxts_1153_;
v_nextMacroScope_1121_ = v_nextMacroScope_1154_;
v_maxRecDepth_1122_ = v_maxRecDepth_1155_;
v_ngen_1123_ = v_ngen_1156_;
v_auxDeclNGen_1124_ = v_auxDeclNGen_1157_;
v_infoState_1125_ = v_infoState_1158_;
v_traceState_1126_ = v_traceState_1159_;
v_snapshotTasks_1127_ = v_snapshotTasks_1160_;
v_prevLinterStates_1128_ = v_prevLinterStates_1161_;
v_codeQualityEntryTasks_1129_ = v_codeQualityEntryTasks_1162_;
v___y_1130_ = v___x_1142_;
v_messages_1131_ = v___x_1171_;
goto v___jp_1117_;
}
else
{
lean_dec(v_fst_1148_);
lean_dec(v_beginPos_1079_);
v_env_1118_ = v_env_1150_;
v_scopes_1119_ = v_scopes_1152_;
v_usedQuotCtxts_1120_ = v_usedQuotCtxts_1153_;
v_nextMacroScope_1121_ = v_nextMacroScope_1154_;
v_maxRecDepth_1122_ = v_maxRecDepth_1155_;
v_ngen_1123_ = v_ngen_1156_;
v_auxDeclNGen_1124_ = v_auxDeclNGen_1157_;
v_infoState_1125_ = v_infoState_1158_;
v_traceState_1126_ = v_traceState_1159_;
v_snapshotTasks_1127_ = v_snapshotTasks_1160_;
v_prevLinterStates_1128_ = v_prevLinterStates_1161_;
v_codeQualityEntryTasks_1129_ = v_codeQualityEntryTasks_1162_;
v___y_1130_ = v___x_1142_;
v_messages_1131_ = v_messages_1151_;
goto v___jp_1117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1179_, lean_object* v_revCmds_1180_, lean_object* v_cmdState_1181_, lean_object* v_beginPos_1182_, lean_object* v_snap_1183_, lean_object* v_cancelTk_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1179_, v_revCmds_1180_, v_cmdState_1181_, v_beginPos_1182_, v_snap_1183_, v_cancelTk_1184_, v_a_1185_);
lean_dec_ref(v_a_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1188_, lean_object* v_h_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1189_, v_x_1190_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_h_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1194_, v_h_1195_, v_x_1196_, v___y_1197_);
lean_dec_ref(v___y_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1200_, lean_object* v_x_1201_, uint8_t v_isolateStderr_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1201_, v_isolateStderr_1202_, v___y_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1206_, lean_object* v_x_1207_, lean_object* v_isolateStderr_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_isolateStderr_boxed_1211_; lean_object* v_res_1212_; 
v_isolateStderr_boxed_1211_ = lean_unbox(v_isolateStderr_1208_);
v_res_1212_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1206_, v_x_1207_, v_isolateStderr_boxed_1211_, v___y_1209_);
lean_dec_ref(v___y_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1213_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1223_){
_start:
{
lean_object* v_toSnapshotTreeM_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_toSnapshotTreeM_1224_ = lean_ctor_get(v_a_1223_, 1);
lean_inc_ref(v_toSnapshotTreeM_1224_);
lean_dec_ref(v_a_1223_);
v___x_1225_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1226_ = lean_apply_1(v_toSnapshotTreeM_1224_, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1227_){
_start:
{
lean_object* v_toSnapshot_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_toSnapshot_1228_ = lean_ctor_get(v_a_1227_, 0);
lean_inc_ref(v_toSnapshot_1228_);
lean_dec_ref(v_a_1227_);
v___x_1229_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1230_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1228_, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1235_ = l_Lean_Language_Snapshot_transform(v_a_1233_, v___x_1234_);
v___x_1236_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1238_, lean_object* v_opt_1239_){
_start:
{
lean_object* v_name_1240_; lean_object* v_defValue_1241_; lean_object* v_map_1242_; lean_object* v___x_1243_; 
v_name_1240_ = lean_ctor_get(v_opt_1239_, 0);
v_defValue_1241_ = lean_ctor_get(v_opt_1239_, 1);
v_map_1242_ = lean_ctor_get(v_opts_1238_, 0);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1242_, v_name_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_inc(v_defValue_1241_);
return v_defValue_1241_;
}
else
{
lean_object* v_val_1244_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v___x_1243_, 1);
if (lean_obj_tag(v_val_1244_) == 3)
{
lean_object* v_v_1245_; 
v_v_1245_ = lean_ctor_get(v_val_1244_, 0);
lean_inc(v_v_1245_);
lean_dec_ref_known(v_val_1244_, 1);
return v_v_1245_;
}
else
{
lean_dec(v_val_1244_);
lean_inc(v_defValue_1241_);
return v_defValue_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1246_, lean_object* v_opt_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1246_, v_opt_1247_);
lean_dec_ref(v_opt_1247_);
lean_dec_ref(v_opts_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1251_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1249_, v___x_1250_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1258_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1259_ = l_Lean_Name_append(v___x_1258_, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1260_, lean_object* v___x_1261_, uint8_t v_val_1262_, lean_object* v_val_1263_, lean_object* v_val_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, uint8_t v___x_1267_, lean_object* v_a_1268_, lean_object* v_pos_1269_, lean_object* v___x_1270_, lean_object* v_infoSt_1271_){
_start:
{
lean_object* v___y_1274_; lean_object* v_msgLog_1275_; lean_object* v___y_1281_; lean_object* v_trees_1313_; lean_object* v_size_1314_; uint8_t v___x_1315_; 
v_trees_1313_ = lean_ctor_get(v_infoSt_1271_, 2);
v_size_1314_ = lean_ctor_get(v_trees_1313_, 2);
v___x_1315_ = lean_nat_dec_lt(v___x_1266_, v_size_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = l_outOfBounds___redArg(v___x_1270_);
v___y_1281_ = v___x_1316_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1270_, v_trees_1313_, v___x_1266_);
v___y_1281_ = v___x_1317_;
goto v___jp_1280_;
}
v___jp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1275_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___y_1274_);
v___x_1278_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1260_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
lean_ctor_set(v___x_1278_, 3, v___x_1261_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*4, v_val_1262_);
v___x_1279_ = lean_io_promise_resolve(v___x_1278_, v_val_1263_);
return v___x_1279_;
}
v___jp_1280_:
{
lean_object* v_scopes_1282_; lean_object* v___x_1283_; lean_object* v_opts_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v_hasTrace_1288_; 
v_scopes_1282_ = lean_ctor_get(v_val_1264_, 2);
v___x_1283_ = l_List_head_x21___redArg(v___x_1265_, v_scopes_1282_);
v_opts_1284_ = lean_ctor_get(v___x_1283_, 1);
lean_inc_ref(v_opts_1284_);
lean_dec(v___x_1283_);
v___x_1285_ = l_Lean_MessageLog_empty;
v___x_1286_ = l_Lean_inheritedTraceOptions;
v___x_1287_ = lean_st_ref_get(v___x_1286_);
v_hasTrace_1288_ = lean_ctor_get_uint8(v_opts_1284_, sizeof(void*)*1);
if (v_hasTrace_1288_ == 0)
{
lean_dec(v___x_1287_);
lean_dec_ref(v_opts_1284_);
lean_dec(v___x_1266_);
v___y_1274_ = v___y_1281_;
v_msgLog_1275_ = v___x_1285_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1290_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1291_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1287_, v_opts_1284_, v___x_1291_);
lean_dec_ref(v_opts_1284_);
lean_dec(v___x_1287_);
if (v___x_1292_ == 0)
{
lean_dec(v___x_1266_);
v___y_1274_ = v___y_1281_;
v_msgLog_1275_ = v___x_1285_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_box(0);
lean_inc_ref(v___y_1281_);
v___x_1294_ = l_Lean_Elab_InfoTree_format(v___y_1281_, v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; double v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_toProcessingContext_1299_; lean_object* v_fileName_1300_; lean_object* v_fileMap_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = lean_float_of_nat(v___x_1266_);
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1298_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1298_, 0, v___x_1289_);
lean_ctor_set(v___x_1298_, 1, v___x_1293_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
lean_ctor_set_float(v___x_1298_, sizeof(void*)*3, v___x_1296_);
lean_ctor_set_float(v___x_1298_, sizeof(void*)*3 + 8, v___x_1296_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*3 + 16, v___x_1267_);
v_toProcessingContext_1299_ = lean_ctor_get(v_a_1268_, 0);
v_fileName_1300_ = lean_ctor_get(v_toProcessingContext_1299_, 1);
v_fileMap_1301_ = lean_ctor_get(v_toProcessingContext_1299_, 2);
v___x_1302_ = l_Lean_MessageData_nil;
v___x_1303_ = l_Lean_MessageData_ofFormat(v_a_1295_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1304_);
v___x_1306_ = lean_array_push(v___x_1305_, v___x_1303_);
v___x_1307_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1298_);
lean_ctor_set(v___x_1307_, 1, v___x_1302_);
lean_ctor_set(v___x_1307_, 2, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1290_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_inc_ref(v_fileMap_1301_);
v___x_1309_ = l_Lean_FileMap_toPosition(v_fileMap_1301_, v_pos_1269_);
v___x_1310_ = 0;
lean_inc_ref(v_fileName_1300_);
v___x_1311_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1311_, 0, v_fileName_1300_);
lean_ctor_set(v___x_1311_, 1, v___x_1309_);
lean_ctor_set(v___x_1311_, 2, v___x_1293_);
lean_ctor_set(v___x_1311_, 3, v___x_1297_);
lean_ctor_set(v___x_1311_, 4, v___x_1308_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5, v_val_1262_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5 + 1, v___x_1310_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5 + 2, v_val_1262_);
v___x_1312_ = l_Lean_MessageLog_add(v___x_1311_, v___x_1285_);
v___y_1274_ = v___y_1281_;
v_msgLog_1275_ = v___x_1312_;
goto v___jp_1273_;
}
else
{
lean_dec_ref_known(v___x_1294_, 1);
lean_dec(v___x_1266_);
v___y_1274_ = v___y_1281_;
v_msgLog_1275_ = v___x_1285_;
goto v___jp_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v_val_1320_, lean_object* v_val_1321_, lean_object* v_val_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v_a_1326_, lean_object* v_pos_1327_, lean_object* v___x_1328_, lean_object* v_infoSt_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_val_36487__boxed_1331_; uint8_t v___x_36492__boxed_1332_; lean_object* v_res_1333_; 
v_val_36487__boxed_1331_ = lean_unbox(v_val_1320_);
v___x_36492__boxed_1332_ = lean_unbox(v___x_1325_);
v_res_1333_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1318_, v___x_1319_, v_val_36487__boxed_1331_, v_val_1321_, v_val_1322_, v___x_1323_, v___x_1324_, v___x_36492__boxed_1332_, v_a_1326_, v_pos_1327_, v___x_1328_, v_infoSt_1329_);
lean_dec_ref(v_infoSt_1329_);
lean_dec_ref(v___x_1328_);
lean_dec(v_pos_1327_);
lean_dec_ref(v_a_1326_);
lean_dec_ref(v___x_1323_);
lean_dec_ref(v_val_1322_);
lean_dec(v_val_1321_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v___x_1336_, uint8_t v_val_1337_, lean_object* v_as_1338_, size_t v_sz_1339_, size_t v_i_1340_, lean_object* v_b_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1340_, v_sz_1339_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1334_);
return v_b_1341_;
}
else
{
lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1362_; 
v_snd_1344_ = lean_ctor_get(v_b_1341_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_b_1341_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v_b_1341_, 0);
lean_dec(v_unused_1363_);
v___x_1346_ = v_b_1341_;
v_isShared_1347_ = v_isSharedCheck_1362_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_dec(v_b_1341_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1362_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_a_1348_; lean_object* v_msg_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v_a_1348_ = lean_array_uget_borrowed(v_as_1338_, v_i_1340_);
v_msg_1349_ = lean_ctor_get(v_a_1348_, 1);
v___x_1350_ = lean_box(0);
lean_inc_ref(v___x_1334_);
v___x_1351_ = l_Lean_FileMap_toPosition(v___x_1334_, v___x_1335_);
v___x_1352_ = 0;
v___x_1353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1349_);
lean_inc_ref(v___x_1336_);
v___x_1354_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1354_, 0, v___x_1336_);
lean_ctor_set(v___x_1354_, 1, v___x_1351_);
lean_ctor_set(v___x_1354_, 2, v___x_1350_);
lean_ctor_set(v___x_1354_, 3, v___x_1353_);
lean_ctor_set(v___x_1354_, 4, v_msg_1349_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*5, v_val_1337_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*5 + 1, v___x_1352_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*5 + 2, v_val_1337_);
v___x_1355_ = l_Lean_MessageLog_add(v___x_1354_, v_snd_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1355_);
lean_ctor_set(v___x_1346_, 0, v___x_1350_);
v___x_1357_ = v___x_1346_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
size_t v___x_1358_; size_t v___x_1359_; 
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_add(v_i_1340_, v___x_1358_);
v_i_1340_ = v___x_1359_;
v_b_1341_ = v___x_1357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1364_, lean_object* v___x_1365_, lean_object* v___x_1366_, lean_object* v_val_1367_, lean_object* v_as_1368_, lean_object* v_sz_1369_, lean_object* v_i_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_){
_start:
{
uint8_t v_val_36600__boxed_1373_; size_t v_sz_boxed_1374_; size_t v_i_boxed_1375_; lean_object* v_res_1376_; 
v_val_36600__boxed_1373_ = lean_unbox(v_val_1367_);
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1369_);
lean_dec(v_sz_1369_);
v_i_boxed_1375_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1364_, v___x_1365_, v___x_1366_, v_val_36600__boxed_1373_, v_as_1368_, v_sz_boxed_1374_, v_i_boxed_1375_, v_b_1371_);
lean_dec_ref(v_as_1368_);
lean_dec(v___x_1365_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v___x_1379_, uint8_t v_val_1380_, lean_object* v_as_1381_, size_t v_sz_1382_, size_t v_i_1383_, lean_object* v_b_1384_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_usize_dec_lt(v_i_1383_, v_sz_1382_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v___x_1379_);
lean_dec_ref(v___x_1377_);
return v_b_1384_;
}
else
{
lean_object* v_snd_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1405_; 
v_snd_1387_ = lean_ctor_get(v_b_1384_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_b_1384_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_b_1384_, 0);
lean_dec(v_unused_1406_);
v___x_1389_ = v_b_1384_;
v_isShared_1390_ = v_isSharedCheck_1405_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1387_);
lean_dec(v_b_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1405_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_a_1391_; lean_object* v_msg_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v_a_1391_ = lean_array_uget_borrowed(v_as_1381_, v_i_1383_);
v_msg_1392_ = lean_ctor_get(v_a_1391_, 1);
v___x_1393_ = lean_box(0);
lean_inc_ref(v___x_1377_);
v___x_1394_ = l_Lean_FileMap_toPosition(v___x_1377_, v___x_1378_);
v___x_1395_ = 0;
v___x_1396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1392_);
lean_inc_ref(v___x_1379_);
v___x_1397_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1397_, 0, v___x_1379_);
lean_ctor_set(v___x_1397_, 1, v___x_1394_);
lean_ctor_set(v___x_1397_, 2, v___x_1393_);
lean_ctor_set(v___x_1397_, 3, v___x_1396_);
lean_ctor_set(v___x_1397_, 4, v_msg_1392_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*5, v_val_1380_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*5 + 1, v___x_1395_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*5 + 2, v_val_1380_);
v___x_1398_ = l_Lean_MessageLog_add(v___x_1397_, v_snd_1387_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v___x_1398_);
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1400_ = v___x_1389_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_add(v_i_1383_, v___x_1401_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1377_, v___x_1378_, v___x_1379_, v_val_1380_, v_as_1381_, v_sz_1382_, v___x_1402_, v___x_1400_);
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v_val_1410_, lean_object* v_as_1411_, lean_object* v_sz_1412_, lean_object* v_i_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v_val_36652__boxed_1416_; size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_val_36652__boxed_1416_ = lean_unbox(v_val_1410_);
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1412_);
lean_dec(v_sz_1412_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1407_, v___x_1408_, v___x_1409_, v_val_36652__boxed_1416_, v_as_1411_, v_sz_boxed_1417_, v_i_boxed_1418_, v_b_1414_);
lean_dec_ref(v_as_1411_);
lean_dec(v___x_1408_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, uint8_t v_val_1424_, lean_object* v_n_1425_, lean_object* v_b_1426_){
_start:
{
if (lean_obj_tag(v_n_1425_) == 0)
{
lean_object* v_cs_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; size_t v_sz_1431_; size_t v___x_1432_; lean_object* v___x_1433_; lean_object* v_fst_1434_; 
v_cs_1428_ = lean_ctor_get(v_n_1425_, 0);
v___x_1429_ = lean_box(0);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v_b_1426_);
v_sz_1431_ = lean_array_size(v_cs_1428_);
v___x_1432_ = ((size_t)0ULL);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1420_, v___x_1421_, v___x_1422_, v___x_1423_, v_val_1424_, v_cs_1428_, v_sz_1431_, v___x_1432_, v___x_1430_);
v_fst_1434_ = lean_ctor_get(v___x_1433_, 0);
if (lean_obj_tag(v_fst_1434_) == 0)
{
lean_object* v_snd_1435_; lean_object* v___x_1436_; 
v_snd_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_snd_1435_);
lean_dec_ref(v___x_1433_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_snd_1435_);
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; 
lean_inc_ref(v_fst_1434_);
lean_dec_ref(v___x_1433_);
v_val_1437_ = lean_ctor_get(v_fst_1434_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v_fst_1434_, 1);
return v_val_1437_;
}
}
else
{
lean_object* v_vs_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; size_t v_sz_1441_; size_t v___x_1442_; lean_object* v___x_1443_; lean_object* v_fst_1444_; 
v_vs_1438_ = lean_ctor_get(v_n_1425_, 0);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_b_1426_);
v_sz_1441_ = lean_array_size(v_vs_1438_);
v___x_1442_ = ((size_t)0ULL);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1421_, v___x_1422_, v___x_1423_, v_val_1424_, v_vs_1438_, v_sz_1441_, v___x_1442_, v___x_1440_);
v_fst_1444_ = lean_ctor_get(v___x_1443_, 0);
if (lean_obj_tag(v_fst_1444_) == 0)
{
lean_object* v_snd_1445_; lean_object* v___x_1446_; 
v_snd_1445_ = lean_ctor_get(v___x_1443_, 1);
lean_inc(v_snd_1445_);
lean_dec_ref(v___x_1443_);
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_snd_1445_);
return v___x_1446_;
}
else
{
lean_object* v_val_1447_; 
lean_inc_ref(v_fst_1444_);
lean_dec_ref(v___x_1443_);
v_val_1447_ = lean_ctor_get(v_fst_1444_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v_fst_1444_, 1);
return v_val_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1448_, lean_object* v___x_1449_, lean_object* v___x_1450_, lean_object* v___x_1451_, uint8_t v_val_1452_, lean_object* v_as_1453_, size_t v_sz_1454_, size_t v_i_1455_, lean_object* v_b_1456_){
_start:
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_usize_dec_lt(v_i_1455_, v_sz_1454_);
if (v___x_1458_ == 0)
{
lean_dec_ref(v___x_1451_);
lean_dec_ref(v___x_1449_);
return v_b_1456_;
}
else
{
lean_object* v_snd_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1477_; 
v_snd_1459_ = lean_ctor_get(v_b_1456_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_b_1456_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_b_1456_, 0);
lean_dec(v_unused_1478_);
v___x_1461_ = v_b_1456_;
v_isShared_1462_ = v_isSharedCheck_1477_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1459_);
lean_dec(v_b_1456_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1477_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v_a_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_box(0);
v_a_1464_ = lean_array_uget_borrowed(v_as_1453_, v_i_1455_);
lean_inc(v_snd_1459_);
lean_inc_ref(v___x_1451_);
lean_inc_ref(v___x_1449_);
v___x_1465_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1448_, v___x_1449_, v___x_1450_, v___x_1451_, v_val_1452_, v_a_1464_, v_snd_1459_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_dec_ref(v___x_1451_);
lean_dec_ref(v___x_1449_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1466_);
v___x_1468_ = v___x_1461_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_snd_1459_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; 
lean_dec(v_snd_1459_);
v_a_1470_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1465_, 1);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v_a_1470_);
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1472_ = v___x_1461_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1470_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
size_t v___x_1473_; size_t v___x_1474_; 
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_add(v_i_1455_, v___x_1473_);
v_i_1455_ = v___x_1474_;
v_b_1456_ = v___x_1472_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v_val_1483_, lean_object* v_as_1484_, lean_object* v_sz_1485_, lean_object* v_i_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v_val_36703__boxed_1489_; size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_val_36703__boxed_1489_ = lean_unbox(v_val_1483_);
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1479_, v___x_1480_, v___x_1481_, v___x_1482_, v_val_36703__boxed_1489_, v_as_1484_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_1487_);
lean_dec_ref(v_as_1484_);
lean_dec(v___x_1481_);
lean_dec_ref(v_init_1479_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1493_, lean_object* v___x_1494_, lean_object* v___x_1495_, lean_object* v___x_1496_, lean_object* v_val_1497_, lean_object* v_n_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_val_36719__boxed_1501_; lean_object* v_res_1502_; 
v_val_36719__boxed_1501_ = lean_unbox(v_val_1497_);
v_res_1502_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1493_, v___x_1494_, v___x_1495_, v___x_1496_, v_val_36719__boxed_1501_, v_n_1498_, v_b_1499_);
lean_dec_ref(v_n_1498_);
lean_dec(v___x_1495_);
lean_dec_ref(v_init_1493_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1503_, lean_object* v___x_1504_, lean_object* v___x_1505_, uint8_t v_val_1506_, lean_object* v_as_1507_, size_t v_sz_1508_, size_t v_i_1509_, lean_object* v_b_1510_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_usize_dec_lt(v_i_1509_, v_sz_1508_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v___x_1505_);
lean_dec_ref(v___x_1503_);
return v_b_1510_;
}
else
{
lean_object* v_snd_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1531_; 
v_snd_1513_ = lean_ctor_get(v_b_1510_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_b_1510_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v_b_1510_, 0);
lean_dec(v_unused_1532_);
v___x_1515_ = v_b_1510_;
v_isShared_1516_ = v_isSharedCheck_1531_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snd_1513_);
lean_dec(v_b_1510_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1531_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_a_1517_; lean_object* v_msg_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v_a_1517_ = lean_array_uget_borrowed(v_as_1507_, v_i_1509_);
v_msg_1518_ = lean_ctor_get(v_a_1517_, 1);
v___x_1519_ = lean_box(0);
lean_inc_ref(v___x_1503_);
v___x_1520_ = l_Lean_FileMap_toPosition(v___x_1503_, v___x_1504_);
v___x_1521_ = 0;
v___x_1522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1518_);
lean_inc_ref(v___x_1505_);
v___x_1523_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1523_, 0, v___x_1505_);
lean_ctor_set(v___x_1523_, 1, v___x_1520_);
lean_ctor_set(v___x_1523_, 2, v___x_1519_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
lean_ctor_set(v___x_1523_, 4, v_msg_1518_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*5, v_val_1506_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*5 + 1, v___x_1521_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*5 + 2, v_val_1506_);
v___x_1524_ = l_Lean_MessageLog_add(v___x_1523_, v_snd_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1524_);
lean_ctor_set(v___x_1515_, 0, v___x_1519_);
v___x_1526_ = v___x_1515_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
size_t v___x_1527_; size_t v___x_1528_; 
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_add(v_i_1509_, v___x_1527_);
v_i_1509_ = v___x_1528_;
v_b_1510_ = v___x_1526_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v___x_1535_, lean_object* v_val_1536_, lean_object* v_as_1537_, lean_object* v_sz_1538_, lean_object* v_i_1539_, lean_object* v_b_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_val_36801__boxed_1542_; size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_val_36801__boxed_1542_ = lean_unbox(v_val_1536_);
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1538_);
lean_dec(v_sz_1538_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1539_);
lean_dec(v_i_1539_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1533_, v___x_1534_, v___x_1535_, v_val_36801__boxed_1542_, v_as_1537_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1540_);
lean_dec_ref(v_as_1537_);
lean_dec(v___x_1534_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v___x_1548_, uint8_t v_val_1549_, lean_object* v_as_1550_, size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_b_1553_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1555_ == 0)
{
lean_dec_ref(v___x_1548_);
lean_dec_ref(v___x_1546_);
return v_b_1553_;
}
else
{
lean_object* v_snd_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1574_; 
v_snd_1556_ = lean_ctor_get(v_b_1553_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_b_1553_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_b_1553_, 0);
lean_dec(v_unused_1575_);
v___x_1558_ = v_b_1553_;
v_isShared_1559_ = v_isSharedCheck_1574_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_snd_1556_);
lean_dec(v_b_1553_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1574_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_a_1560_; lean_object* v_msg_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v_a_1560_ = lean_array_uget_borrowed(v_as_1550_, v_i_1552_);
v_msg_1561_ = lean_ctor_get(v_a_1560_, 1);
v___x_1562_ = lean_box(0);
lean_inc_ref(v___x_1546_);
v___x_1563_ = l_Lean_FileMap_toPosition(v___x_1546_, v___x_1547_);
v___x_1564_ = 0;
v___x_1565_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1561_);
lean_inc_ref(v___x_1548_);
v___x_1566_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1566_, 0, v___x_1548_);
lean_ctor_set(v___x_1566_, 1, v___x_1563_);
lean_ctor_set(v___x_1566_, 2, v___x_1562_);
lean_ctor_set(v___x_1566_, 3, v___x_1565_);
lean_ctor_set(v___x_1566_, 4, v_msg_1561_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*5, v_val_1549_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*5 + 1, v___x_1564_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*5 + 2, v_val_1549_);
v___x_1567_ = l_Lean_MessageLog_add(v___x_1566_, v_snd_1556_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v___x_1567_);
lean_ctor_set(v___x_1558_, 0, v___x_1562_);
v___x_1569_ = v___x_1558_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1552_, v___x_1570_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1546_, v___x_1547_, v___x_1548_, v_val_1549_, v_as_1550_, v_sz_1551_, v___x_1571_, v___x_1569_);
return v___x_1572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v___x_1578_, lean_object* v_val_1579_, lean_object* v_as_1580_, lean_object* v_sz_1581_, lean_object* v_i_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v_val_36853__boxed_1585_; size_t v_sz_boxed_1586_; size_t v_i_boxed_1587_; lean_object* v_res_1588_; 
v_val_36853__boxed_1585_ = lean_unbox(v_val_1579_);
v_sz_boxed_1586_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1587_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1576_, v___x_1577_, v___x_1578_, v_val_36853__boxed_1585_, v_as_1580_, v_sz_boxed_1586_, v_i_boxed_1587_, v_b_1583_);
lean_dec_ref(v_as_1580_);
lean_dec(v___x_1577_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, uint8_t v_val_1592_, lean_object* v_t_1593_, lean_object* v_init_1594_){
_start:
{
lean_object* v_root_1596_; lean_object* v_tail_1597_; lean_object* v___x_1598_; 
v_root_1596_ = lean_ctor_get(v_t_1593_, 0);
v_tail_1597_ = lean_ctor_get(v_t_1593_, 1);
lean_inc_ref(v___x_1591_);
lean_inc_ref(v___x_1589_);
lean_inc_ref(v_init_1594_);
v___x_1598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1594_, v___x_1589_, v___x_1590_, v___x_1591_, v_val_1592_, v_root_1596_, v_init_1594_);
lean_dec_ref(v_init_1594_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1589_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
return v_a_1599_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; lean_object* v_fst_1606_; 
v_a_1600_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v_a_1600_);
v_sz_1603_ = lean_array_size(v_tail_1597_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1589_, v___x_1590_, v___x_1591_, v_val_1592_, v_tail_1597_, v_sz_1603_, v___x_1604_, v___x_1602_);
v_fst_1606_ = lean_ctor_get(v___x_1605_, 0);
if (lean_obj_tag(v_fst_1606_) == 0)
{
lean_object* v_snd_1607_; 
v_snd_1607_ = lean_ctor_get(v___x_1605_, 1);
lean_inc(v_snd_1607_);
lean_dec_ref(v___x_1605_);
return v_snd_1607_;
}
else
{
lean_object* v_val_1608_; 
lean_inc_ref(v_fst_1606_);
lean_dec_ref(v___x_1605_);
v_val_1608_ = lean_ctor_get(v_fst_1606_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v_fst_1606_, 1);
return v_val_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v___x_1611_, lean_object* v_val_1612_, lean_object* v_t_1613_, lean_object* v_init_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v_val_36904__boxed_1616_; lean_object* v_res_1617_; 
v_val_36904__boxed_1616_ = lean_unbox(v_val_1612_);
v_res_1617_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1609_, v___x_1610_, v___x_1611_, v_val_36904__boxed_1616_, v_t_1613_, v_init_1614_);
lean_dec_ref(v_t_1613_);
lean_dec(v___x_1610_);
return v_res_1617_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = l_Lean_firstFrontendMacroScope;
v___x_1620_ = lean_nat_add(v___x_1619_, v___x_1618_);
return v___x_1620_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1631_, lean_object* v_opts_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v___x_1635_, size_t v___x_1636_, uint8_t v___x_1637_, lean_object* v_env_1638_, lean_object* v___x_1639_, lean_object* v___x_1640_, lean_object* v_pos_1641_, uint8_t v_val_1642_, lean_object* v___x_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, uint8_t v___x_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v_toProcessingContext_1651_; lean_object* v_fileName_1652_; lean_object* v_fileMap_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint16_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_fileName_1677_; lean_object* v_fileMap_1678_; lean_object* v_currNamespace_1679_; lean_object* v_openDecls_1680_; lean_object* v_initHeartbeats_1681_; lean_object* v_maxHeartbeats_1682_; lean_object* v_quotContext_1683_; lean_object* v_currMacroScope_1684_; lean_object* v_cancelTk_x3f_1685_; lean_object* v_inheritedTraceOptions_1686_; lean_object* v_currRecDepth_1687_; lean_object* v_ref_1688_; uint8_t v_suppressElabErrors_1689_; uint8_t v_isRecordingDeps_1690_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___y_1710_; uint8_t v___y_1732_; uint8_t v___y_1733_; lean_object* v_env_1734_; uint8_t v___x_1735_; uint8_t v___y_1737_; uint16_t v___x_1738_; uint16_t v___x_1739_; uint16_t v___x_1740_; uint8_t v___x_1741_; 
v_toProcessingContext_1651_ = lean_ctor_get(v_a_1631_, 0);
v_fileName_1652_ = lean_ctor_get(v_toProcessingContext_1651_, 1);
v_fileMap_1653_ = lean_ctor_get(v_toProcessingContext_1651_, 2);
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_Core_getMaxHeartbeats(v_opts_1632_);
v___x_1656_ = l_Lean_firstFrontendMacroScope;
v___x_1657_ = lean_box(0);
v___x_1658_ = l_Lean_OptionFlags_ofOptions(v_opts_1632_);
v___x_1659_ = lean_unsigned_to_nat(1u);
v___x_1660_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1661_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1633_);
v___x_1662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1633_);
lean_ctor_set(v___x_1662_, 1, v___x_1659_);
lean_ctor_set(v___x_1662_, 2, v___x_1654_);
v___x_1663_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1664_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1665_ = lean_mk_empty_array_with_capacity(v___x_1634_);
v___x_1666_ = l_Lean_Options_empty;
lean_inc_n(v___x_1634_, 3);
lean_inc_ref_n(v___x_1665_, 3);
v___x_1667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
lean_ctor_set(v___x_1667_, 2, v___x_1665_);
lean_ctor_set(v___x_1667_, 3, v___x_1634_);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1635_);
lean_inc_ref(v___x_1668_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___x_1668_);
lean_ctor_set(v___x_1670_, 2, v___x_1634_);
lean_ctor_set(v___x_1670_, 3, v___x_1634_);
lean_ctor_set_usize(v___x_1670_, 4, v___x_1636_);
v___x_1671_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1670_, 2);
v___x_1672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1673_, 0, v___x_1663_);
lean_ctor_set(v___x_1673_, 1, v___x_1663_);
lean_ctor_set(v___x_1673_, 2, v___x_1670_);
lean_ctor_set_uint8(v___x_1673_, sizeof(void*)*3, v___x_1637_);
lean_inc_ref(v___x_1639_);
v___x_1674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1674_, 0, v_env_1638_);
lean_ctor_set(v___x_1674_, 1, v___x_1660_);
lean_ctor_set(v___x_1674_, 2, v___x_1661_);
lean_ctor_set(v___x_1674_, 3, v___x_1662_);
lean_ctor_set(v___x_1674_, 4, v___x_1639_);
lean_ctor_set(v___x_1674_, 5, v___x_1664_);
lean_ctor_set(v___x_1674_, 6, v___x_1667_);
lean_ctor_set(v___x_1674_, 7, v___x_1672_);
lean_ctor_set(v___x_1674_, 8, v___x_1673_);
lean_ctor_set(v___x_1674_, 9, v___x_1665_);
v___x_1675_ = lean_st_mk_ref(v___x_1674_);
v___x_1707_ = lean_st_ref_get(v___x_1646_);
v___x_1708_ = lean_st_ref_get(v___x_1675_);
v_env_1734_ = lean_ctor_get(v___x_1708_, 0);
lean_inc_ref(v_env_1734_);
lean_dec(v___x_1708_);
v___x_1735_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1734_);
lean_dec_ref(v_env_1734_);
v___x_1738_ = 512;
v___x_1739_ = lean_uint16_land(v___x_1658_, v___x_1738_);
v___x_1740_ = 0;
v___x_1741_ = lean_uint16_dec_eq(v___x_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
if (v___x_1648_ == 0)
{
v___y_1737_ = v___x_1648_;
goto v___jp_1736_;
}
else
{
v___y_1732_ = v___x_1648_;
v___y_1733_ = v___x_1735_;
goto v___jp_1731_;
}
}
else
{
v___y_1737_ = v_val_1642_;
goto v___jp_1736_;
}
v___jp_1676_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1691_ = l_Lean_maxRecDepth;
v___x_1692_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1632_, v___x_1691_);
lean_inc(v_currMacroScope_1684_);
lean_inc(v_openDecls_1680_);
v___x_1693_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1693_, 0, v_fileName_1677_);
lean_ctor_set(v___x_1693_, 1, v_fileMap_1678_);
lean_ctor_set(v___x_1693_, 2, v_opts_1632_);
lean_ctor_set(v___x_1693_, 3, v___x_1692_);
lean_ctor_set(v___x_1693_, 4, v_currNamespace_1679_);
lean_ctor_set(v___x_1693_, 5, v_openDecls_1680_);
lean_ctor_set(v___x_1693_, 6, v_initHeartbeats_1681_);
lean_ctor_set(v___x_1693_, 7, v_maxHeartbeats_1682_);
lean_ctor_set(v___x_1693_, 8, v_quotContext_1683_);
lean_ctor_set(v___x_1693_, 9, v_currMacroScope_1684_);
lean_ctor_set(v___x_1693_, 10, v_cancelTk_x3f_1685_);
lean_ctor_set(v___x_1693_, 11, v_inheritedTraceOptions_1686_);
lean_inc(v_ref_1688_);
v___x_1694_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_currRecDepth_1687_);
lean_ctor_set(v___x_1694_, 2, v_ref_1688_);
lean_ctor_set_uint16(v___x_1694_, sizeof(void*)*3, v___x_1658_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 2, v_suppressElabErrors_1689_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 3, v_isRecordingDeps_1690_);
v___x_1695_ = l_Lean_Language_SnapshotTree_trace(v___x_1640_, v___x_1694_, v___x_1675_);
lean_dec_ref_known(v___x_1694_, 3);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v___x_1696_; lean_object* v_traceState_1697_; lean_object* v_traces_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref_known(v___x_1695_, 1);
lean_dec_ref(v___x_1645_);
v___x_1696_ = lean_st_ref_get(v___x_1675_);
lean_dec(v___x_1675_);
v_traceState_1697_ = lean_ctor_get(v___x_1696_, 4);
lean_inc_ref(v_traceState_1697_);
lean_dec(v___x_1696_);
v_traces_1698_ = lean_ctor_get(v_traceState_1697_, 0);
lean_inc_ref(v_traces_1698_);
lean_dec_ref(v_traceState_1697_);
v___x_1699_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1652_);
lean_inc_ref(v_fileMap_1653_);
v___x_1700_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1653_, v_pos_1641_, v_fileName_1652_, v_val_1642_, v_traces_1698_, v___x_1699_);
lean_dec_ref(v_traces_1698_);
v___x_1701_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1700_);
v___x_1702_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1702_, 0, v___x_1643_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
lean_ctor_set(v___x_1702_, 2, v___x_1644_);
lean_ctor_set(v___x_1702_, 3, v___x_1639_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*4, v_val_1642_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1665_);
v___x_1704_ = lean_task_pure(v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref_known(v___x_1695_, 1);
lean_dec(v___x_1675_);
lean_dec(v___x_1644_);
lean_dec_ref(v___x_1643_);
lean_dec_ref(v___x_1639_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1645_);
lean_ctor_set(v___x_1705_, 1, v___x_1665_);
v___x_1706_ = lean_task_pure(v___x_1705_);
return v___x_1706_;
}
}
v___jp_1709_:
{
lean_object* v___x_1711_; lean_object* v_env_1712_; lean_object* v_nextMacroScope_1713_; lean_object* v_ngen_1714_; lean_object* v_auxDeclNGen_1715_; lean_object* v_traceState_1716_; lean_object* v_recordedDeps_1717_; lean_object* v_messages_1718_; lean_object* v_infoState_1719_; lean_object* v_snapshotTasks_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1729_; 
v___x_1711_ = lean_st_ref_take(v___x_1675_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
v_nextMacroScope_1713_ = lean_ctor_get(v___x_1711_, 1);
v_ngen_1714_ = lean_ctor_get(v___x_1711_, 2);
v_auxDeclNGen_1715_ = lean_ctor_get(v___x_1711_, 3);
v_traceState_1716_ = lean_ctor_get(v___x_1711_, 4);
v_recordedDeps_1717_ = lean_ctor_get(v___x_1711_, 6);
v_messages_1718_ = lean_ctor_get(v___x_1711_, 7);
v_infoState_1719_ = lean_ctor_get(v___x_1711_, 8);
v_snapshotTasks_1720_ = lean_ctor_get(v___x_1711_, 9);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1711_, 5);
lean_dec(v_unused_1730_);
v___x_1722_ = v___x_1711_;
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_snapshotTasks_1720_);
lean_inc(v_infoState_1719_);
lean_inc(v_messages_1718_);
lean_inc(v_recordedDeps_1717_);
lean_inc(v_traceState_1716_);
lean_inc(v_auxDeclNGen_1715_);
lean_inc(v_ngen_1714_);
lean_inc(v_nextMacroScope_1713_);
lean_inc(v_env_1712_);
lean_dec(v___x_1711_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = l_Lean_Kernel_enableDiag(v_env_1712_, v___y_1710_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 5, v___x_1664_);
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_nextMacroScope_1713_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_ngen_1714_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_auxDeclNGen_1715_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_traceState_1716_);
lean_ctor_set(v_reuseFailAlloc_1728_, 5, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1728_, 6, v_recordedDeps_1717_);
lean_ctor_set(v_reuseFailAlloc_1728_, 7, v_messages_1718_);
lean_ctor_set(v_reuseFailAlloc_1728_, 8, v_infoState_1719_);
lean_ctor_set(v_reuseFailAlloc_1728_, 9, v_snapshotTasks_1720_);
v___x_1726_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_st_ref_put(v___x_1675_, v___x_1726_);
lean_inc(v___x_1634_);
lean_inc(v___x_1633_);
lean_inc_ref(v_fileMap_1653_);
lean_inc_ref(v_fileName_1652_);
v_fileName_1677_ = v_fileName_1652_;
v_fileMap_1678_ = v_fileMap_1653_;
v_currNamespace_1679_ = v___x_1633_;
v_openDecls_1680_ = v___x_1654_;
v_initHeartbeats_1681_ = v___x_1634_;
v_maxHeartbeats_1682_ = v___x_1655_;
v_quotContext_1683_ = v___x_1633_;
v_currMacroScope_1684_ = v___x_1656_;
v_cancelTk_x3f_1685_ = v___x_1647_;
v_inheritedTraceOptions_1686_ = v___x_1707_;
v_currRecDepth_1687_ = v___x_1634_;
v_ref_1688_ = v___x_1657_;
v_suppressElabErrors_1689_ = v_val_1642_;
v_isRecordingDeps_1690_ = v_val_1642_;
goto v___jp_1676_;
}
}
}
v___jp_1731_:
{
if (v___y_1733_ == 0)
{
v___y_1710_ = v___y_1732_;
goto v___jp_1709_;
}
else
{
lean_inc(v___x_1634_);
lean_inc(v___x_1633_);
lean_inc_ref(v_fileMap_1653_);
lean_inc_ref(v_fileName_1652_);
v_fileName_1677_ = v_fileName_1652_;
v_fileMap_1678_ = v_fileMap_1653_;
v_currNamespace_1679_ = v___x_1633_;
v_openDecls_1680_ = v___x_1654_;
v_initHeartbeats_1681_ = v___x_1634_;
v_maxHeartbeats_1682_ = v___x_1655_;
v_quotContext_1683_ = v___x_1633_;
v_currMacroScope_1684_ = v___x_1656_;
v_cancelTk_x3f_1685_ = v___x_1647_;
v_inheritedTraceOptions_1686_ = v___x_1707_;
v_currRecDepth_1687_ = v___x_1634_;
v_ref_1688_ = v___x_1657_;
v_suppressElabErrors_1689_ = v_val_1642_;
v_isRecordingDeps_1690_ = v_val_1642_;
goto v___jp_1676_;
}
}
v___jp_1736_:
{
if (v___x_1735_ == 0)
{
v___y_1732_ = v___y_1737_;
v___y_1733_ = v___x_1648_;
goto v___jp_1731_;
}
else
{
v___y_1710_ = v___y_1737_;
goto v___jp_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1742_ = _args[0];
lean_object* v_opts_1743_ = _args[1];
lean_object* v___x_1744_ = _args[2];
lean_object* v___x_1745_ = _args[3];
lean_object* v___x_1746_ = _args[4];
lean_object* v___x_1747_ = _args[5];
lean_object* v___x_1748_ = _args[6];
lean_object* v_env_1749_ = _args[7];
lean_object* v___x_1750_ = _args[8];
lean_object* v___x_1751_ = _args[9];
lean_object* v_pos_1752_ = _args[10];
lean_object* v_val_1753_ = _args[11];
lean_object* v___x_1754_ = _args[12];
lean_object* v___x_1755_ = _args[13];
lean_object* v___x_1756_ = _args[14];
lean_object* v___x_1757_ = _args[15];
lean_object* v___x_1758_ = _args[16];
lean_object* v___x_1759_ = _args[17];
lean_object* v_x_1760_ = _args[18];
lean_object* v___y_1761_ = _args[19];
_start:
{
size_t v___x_36964__boxed_1762_; uint8_t v___x_36965__boxed_1763_; uint8_t v_val_36968__boxed_1764_; uint8_t v___x_36974__boxed_1765_; lean_object* v_res_1766_; 
v___x_36964__boxed_1762_ = lean_unbox_usize(v___x_1747_);
lean_dec(v___x_1747_);
v___x_36965__boxed_1763_ = lean_unbox(v___x_1748_);
v_val_36968__boxed_1764_ = lean_unbox(v_val_1753_);
v___x_36974__boxed_1765_ = lean_unbox(v___x_1759_);
v_res_1766_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1742_, v_opts_1743_, v___x_1744_, v___x_1745_, v___x_1746_, v___x_36964__boxed_1762_, v___x_36965__boxed_1763_, v_env_1749_, v___x_1750_, v___x_1751_, v_pos_1752_, v_val_36968__boxed_1764_, v___x_1754_, v___x_1755_, v___x_1756_, v___x_1757_, v___x_1758_, v___x_36974__boxed_1765_, v_x_1760_);
lean_dec(v___x_1757_);
lean_dec(v_pos_1752_);
lean_dec(v___x_1746_);
lean_dec_ref(v_a_1742_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1767_, lean_object* v___x_1768_, lean_object* v_parserState_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v_toProcessingContext_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_toProcessingContext_1771_ = lean_ctor_get(v_a_1767_, 0);
v___x_1772_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1771_);
v___x_1773_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1771_, v___x_1768_, v_parserState_1769_, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1774_, lean_object* v___x_1775_, lean_object* v_parserState_1776_, lean_object* v_x_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1774_, v___x_1775_, v_parserState_1776_, v_x_1777_);
lean_dec_ref(v_a_1774_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1780_, size_t v_i_1781_, size_t v_stop_1782_, lean_object* v_b_1783_){
_start:
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_usize_dec_eq(v_i_1781_, v_stop_1782_);
if (v___x_1785_ == 0)
{
lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; size_t v___x_1789_; size_t v___x_1790_; 
v___f_1786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1787_ = lean_array_uget_borrowed(v_as_1780_, v_i_1781_);
lean_inc(v___x_1787_);
v___x_1788_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1786_, v___x_1787_);
v___x_1789_ = ((size_t)1ULL);
v___x_1790_ = lean_usize_add(v_i_1781_, v___x_1789_);
v_i_1781_ = v___x_1790_;
v_b_1783_ = v___x_1788_;
goto _start;
}
else
{
return v_b_1783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1792_, lean_object* v_i_1793_, lean_object* v_stop_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_){
_start:
{
size_t v_i_boxed_1797_; size_t v_stop_boxed_1798_; lean_object* v_res_1799_; 
v_i_boxed_1797_ = lean_unbox_usize(v_i_1793_);
lean_dec(v_i_1793_);
v_stop_boxed_1798_ = lean_unbox_usize(v_stop_1794_);
lean_dec(v_stop_1794_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1792_, v_i_boxed_1797_, v_stop_boxed_1798_, v_b_1795_);
lean_dec_ref(v_as_1792_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1800_, lean_object* v_stx_1801_, lean_object* v_revCmds_1802_, lean_object* v_newParserState_1803_, lean_object* v_val_1804_, lean_object* v_sync_1805_, lean_object* v_val_1806_, lean_object* v_a_1807_, lean_object* v_oldNext_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_sync_boxed_1810_; lean_object* v_res_1811_; 
v_sync_boxed_1810_ = lean_unbox(v_sync_1805_);
v_res_1811_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1800_, v_stx_1801_, v_revCmds_1802_, v_newParserState_1803_, v_val_1804_, v_sync_boxed_1810_, v_val_1806_, v_a_1807_, v_oldNext_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1812_, lean_object* v_stx_1813_, lean_object* v_revCmds_1814_, lean_object* v_newParserState_1815_, lean_object* v_val_1816_, uint8_t v_sync_1817_, lean_object* v_val_1818_, lean_object* v_a_1819_, lean_object* v_oldResult_1820_){
_start:
{
lean_object* v_task_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; 
v_task_1822_ = lean_ctor_get(v_val_1812_, 3);
lean_inc_ref(v_task_1822_);
lean_dec_ref(v_val_1812_);
v___x_1823_ = lean_box(v_sync_1817_);
lean_inc_ref(v_a_1819_);
v___f_1824_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1824_, 0, v_oldResult_1820_);
lean_closure_set(v___f_1824_, 1, v_stx_1813_);
lean_closure_set(v___f_1824_, 2, v_revCmds_1814_);
lean_closure_set(v___f_1824_, 3, v_newParserState_1815_);
lean_closure_set(v___f_1824_, 4, v_val_1816_);
lean_closure_set(v___f_1824_, 5, v___x_1823_);
lean_closure_set(v___f_1824_, 6, v_val_1818_);
lean_closure_set(v___f_1824_, 7, v_a_1819_);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = 1;
v___x_1827_ = l_BaseIO_chainTask___redArg(v_task_1822_, v___f_1824_, v___x_1825_, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1828_, lean_object* v_stx_1829_, lean_object* v_revCmds_1830_, lean_object* v_newParserState_1831_, lean_object* v_val_1832_, lean_object* v_sync_1833_, lean_object* v_val_1834_, lean_object* v_a_1835_, lean_object* v_oldResult_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v_sync_boxed_1838_; lean_object* v_res_1839_; 
v_sync_boxed_1838_ = lean_unbox(v_sync_1833_);
v_res_1839_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1828_, v_stx_1829_, v_revCmds_1830_, v_newParserState_1831_, v_val_1832_, v_sync_boxed_1838_, v_val_1834_, v_a_1835_, v_oldResult_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1839_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1848_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1849_ = l_Lean_Name_append(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1853_, lean_object* v_val_1854_, lean_object* v_fst_1855_, lean_object* v_revCmds_1856_, lean_object* v_fst_1857_, uint8_t v_val_1858_, lean_object* v_a_1859_, lean_object* v_snd_1860_, lean_object* v___x_1861_, uint8_t v___x_1862_, lean_object* v_fst_1863_, lean_object* v_val_1864_, lean_object* v_val_1865_, lean_object* v___x_1866_, lean_object* v___f_1867_, lean_object* v___f_1868_, lean_object* v___f_1869_, lean_object* v_pos_1870_, lean_object* v_cmdState_1871_, lean_object* v_val_1872_, lean_object* v___x_1873_, lean_object* v_opts_1874_, lean_object* v___x_1875_, lean_object* v_snd_1876_, lean_object* v_prom_1877_, lean_object* v_old_x3f_1878_, lean_object* v_parseCancelTk_1879_, lean_object* v_next_x3f_1880_){
_start:
{
lean_object* v___y_1883_; lean_object* v_snapshotTasks_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v_traceTask_1889_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1911_; lean_object* v___y_1912_; size_t v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_env_1928_; lean_object* v_messages_1929_; lean_object* v_scopes_1930_; lean_object* v_infoState_1931_; lean_object* v_traceState_1932_; lean_object* v_snapshotTasks_1933_; lean_object* v_codeQualityEntryTasks_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v_reportedCmdState_1940_; lean_object* v___y_1975_; lean_object* v___y_1976_; size_t v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v_reportedCmdState_1997_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; size_t v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2055_; 
if (lean_obj_tag(v_next_x3f_1880_) == 0)
{
lean_object* v___x_2108_; 
lean_dec_ref(v_parseCancelTk_1879_);
v___x_2108_ = lean_box(0);
v___y_2055_ = v___x_2108_;
goto v___jp_2054_;
}
else
{
lean_object* v_toProcessingContext_2109_; lean_object* v_val_2110_; lean_object* v_pos_2111_; lean_object* v_endPos_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_toProcessingContext_2109_ = lean_ctor_get(v_a_1859_, 0);
v_val_2110_ = lean_ctor_get(v_next_x3f_1880_, 0);
v_pos_2111_ = lean_ctor_get(v_fst_1857_, 0);
v_endPos_2112_ = lean_ctor_get(v_toProcessingContext_2109_, 3);
v___x_2113_ = lean_box(0);
lean_inc(v_endPos_2112_);
lean_inc(v_pos_2111_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_pos_2111_);
lean_ctor_set(v___x_2114_, 1, v_endPos_2112_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_parseCancelTk_1879_);
v___x_2117_ = l_IO_Promise_result_x21___redArg(v_val_2110_);
v___x_2118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2113_);
lean_ctor_set(v___x_2118_, 1, v___x_2115_);
lean_ctor_set(v___x_2118_, 2, v___x_2116_);
lean_ctor_set(v___x_2118_, 3, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
v___y_2055_ = v___x_2119_;
goto v___jp_2054_;
}
v___jp_1882_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1890_, 0, v___y_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1853_);
lean_ctor_set(v___x_1890_, 2, v___y_1885_);
lean_ctor_set(v___x_1890_, 3, v_traceTask_1889_);
v___x_1891_ = lean_array_push(v_snapshotTasks_1884_, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___y_1887_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_io_promise_resolve(v___x_1892_, v_val_1854_);
if (lean_obj_tag(v_next_x3f_1880_) == 1)
{
lean_object* v_val_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_val_1894_ = lean_ctor_get(v_next_x3f_1880_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v_next_x3f_1880_, 1);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_fst_1855_);
lean_ctor_set(v___x_1896_, 1, v_revCmds_1856_);
v___x_1897_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1895_, v_fst_1857_, v___y_1883_, v_val_1894_, v_val_1858_, v___y_1886_, v___x_1896_, v_a_1859_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; 
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1883_);
lean_dec(v_next_x3f_1880_);
lean_dec_ref(v_fst_1857_);
lean_dec(v_revCmds_1856_);
lean_dec(v_fst_1855_);
v___x_1898_ = lean_box(0);
return v___x_1898_;
}
}
v___jp_1899_:
{
lean_object* v_snapshotTasks_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_snapshotTasks_1906_ = lean_ctor_get(v___y_1900_, 10);
lean_inc_ref(v_snapshotTasks_1906_);
v___x_1907_ = lean_mk_empty_array_with_capacity(v___y_1903_);
lean_dec(v___y_1903_);
lean_inc_ref(v___y_1904_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___y_1904_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_task_pure(v___x_1908_);
v___y_1883_ = v___y_1900_;
v_snapshotTasks_1884_ = v_snapshotTasks_1906_;
v___y_1885_ = v___y_1901_;
v___y_1886_ = v___y_1902_;
v___y_1887_ = v___y_1904_;
v___y_1888_ = v___y_1905_;
v_traceTask_1889_ = v___x_1909_;
goto v___jp_1882_;
}
v___jp_1910_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_opts_1950_; uint8_t v_hasTrace_1951_; 
v___x_1941_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1929_);
v___x_1942_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1942_, 0, v___y_1920_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
lean_ctor_set(v___x_1942_, 2, v___y_1935_);
lean_ctor_set(v___x_1942_, 3, v_traceState_1932_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*4, v_val_1858_);
v___x_1943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v_reportedCmdState_1940_);
lean_ctor_set(v___x_1943_, 2, v_codeQualityEntryTasks_1934_);
v___x_1944_ = lean_io_promise_resolve(v___x_1943_, v_val_1865_);
v___x_1945_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1931_);
lean_inc(v___y_1923_);
v___x_1946_ = l_BaseIO_chainTask___redArg(v___x_1945_, v___y_1939_, v___y_1923_, v___x_1862_);
v___x_1947_ = l_Lean_inheritedTraceOptions;
v___x_1948_ = lean_st_ref_get(v___x_1947_);
v___x_1949_ = l_List_head_x21___redArg(v___x_1866_, v_scopes_1930_);
lean_dec(v_scopes_1930_);
lean_dec_ref(v___x_1866_);
v_opts_1950_ = lean_ctor_get(v___x_1949_, 1);
lean_inc_ref(v_opts_1950_);
lean_dec(v___x_1949_);
v_hasTrace_1951_ = lean_ctor_get_uint8(v_opts_1950_, sizeof(void*)*1);
if (v_hasTrace_1951_ == 0)
{
lean_dec_ref(v_opts_1950_);
lean_dec(v___x_1948_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_snapshotTasks_1933_);
lean_dec_ref(v_env_1928_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v_pos_1870_);
lean_dec_ref(v___f_1869_);
lean_dec_ref(v___f_1868_);
lean_dec_ref(v___f_1867_);
lean_dec(v___x_1861_);
v___y_1900_ = v___y_1927_;
v___y_1901_ = v___y_1919_;
v___y_1902_ = v___y_1921_;
v___y_1903_ = v___y_1923_;
v___y_1904_ = v___y_1924_;
v___y_1905_ = v___y_1938_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1952_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1953_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1948_, v_opts_1950_, v___x_1952_);
lean_dec(v___x_1948_);
if (v___x_1953_ == 0)
{
lean_dec_ref(v_opts_1950_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_snapshotTasks_1933_);
lean_dec_ref(v_env_1928_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v_pos_1870_);
lean_dec_ref(v___f_1869_);
lean_dec_ref(v___f_1868_);
lean_dec_ref(v___f_1867_);
lean_dec(v___x_1861_);
v___y_1900_ = v___y_1927_;
v___y_1901_ = v___y_1919_;
v___y_1902_ = v___y_1921_;
v___y_1903_ = v___y_1923_;
v___y_1904_ = v___y_1924_;
v___y_1905_ = v___y_1938_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___f_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_inc_n(v___y_1923_, 3);
v___x_1954_ = lean_task_map(v___f_1867_, v___y_1925_, v___y_1923_, v___x_1862_);
lean_inc_n(v___y_1919_, 3);
lean_inc_n(v___y_1926_, 2);
lean_inc_n(v___y_1937_, 2);
v___x_1955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1955_, 0, v___y_1937_);
lean_ctor_set(v___x_1955_, 1, v___y_1926_);
lean_ctor_set(v___x_1955_, 2, v___y_1919_);
lean_ctor_set(v___x_1955_, 3, v___x_1954_);
v___x_1956_ = lean_task_map(v___f_1868_, v___y_1922_, v___y_1923_, v___x_1862_);
v___x_1957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1957_, 0, v___y_1937_);
lean_ctor_set(v___x_1957_, 1, v___y_1926_);
lean_ctor_set(v___x_1957_, 2, v___y_1919_);
lean_ctor_set(v___x_1957_, 3, v___x_1956_);
v___x_1958_ = lean_task_map(v___f_1869_, v___y_1936_, v___y_1923_, v___x_1862_);
v___x_1959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1959_, 0, v___y_1937_);
lean_ctor_set(v___x_1959_, 1, v___y_1926_);
lean_ctor_set(v___x_1959_, 2, v___y_1919_);
lean_ctor_set(v___x_1959_, 3, v___x_1958_);
v___x_1960_ = lean_unsigned_to_nat(3u);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
v___x_1962_ = lean_array_push(v___x_1961_, v___x_1955_);
v___x_1963_ = lean_array_push(v___x_1962_, v___x_1957_);
v___x_1964_ = lean_array_push(v___x_1963_, v___x_1959_);
v___x_1965_ = l_Array_append___redArg(v___x_1964_, v_snapshotTasks_1933_);
lean_inc_ref(v___y_1924_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___y_1924_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_box_usize(v___y_1913_);
v___x_1968_ = lean_box(v___x_1862_);
v___x_1969_ = lean_box(v_val_1858_);
v___x_1970_ = lean_box(v___x_1953_);
lean_inc_ref(v___x_1966_);
lean_inc_ref(v___y_1912_);
lean_inc_ref(v_a_1859_);
v___f_1971_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1971_, 0, v_a_1859_);
lean_closure_set(v___f_1971_, 1, v_opts_1950_);
lean_closure_set(v___f_1971_, 2, v___x_1861_);
lean_closure_set(v___f_1971_, 3, v___y_1917_);
lean_closure_set(v___f_1971_, 4, v___y_1918_);
lean_closure_set(v___f_1971_, 5, v___x_1967_);
lean_closure_set(v___f_1971_, 6, v___x_1968_);
lean_closure_set(v___f_1971_, 7, v_env_1928_);
lean_closure_set(v___f_1971_, 8, v___y_1912_);
lean_closure_set(v___f_1971_, 9, v___x_1966_);
lean_closure_set(v___f_1971_, 10, v_pos_1870_);
lean_closure_set(v___f_1971_, 11, v___x_1969_);
lean_closure_set(v___f_1971_, 12, v___y_1915_);
lean_closure_set(v___f_1971_, 13, v___y_1911_);
lean_closure_set(v___f_1971_, 14, v___y_1916_);
lean_closure_set(v___f_1971_, 15, v___x_1947_);
lean_closure_set(v___f_1971_, 16, v___y_1914_);
lean_closure_set(v___f_1971_, 17, v___x_1970_);
v___x_1972_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1966_);
v___x_1973_ = lean_io_bind_task(v___x_1972_, v___f_1971_, v___y_1923_, v_val_1858_);
v___y_1883_ = v___y_1927_;
v_snapshotTasks_1884_ = v_snapshotTasks_1933_;
v___y_1885_ = v___y_1919_;
v___y_1886_ = v___y_1921_;
v___y_1887_ = v___y_1924_;
v___y_1888_ = v___y_1938_;
v_traceTask_1889_ = v___x_1973_;
goto v___jp_1882_;
}
}
}
v___jp_1974_:
{
lean_object* v_env_1998_; lean_object* v_messages_1999_; lean_object* v_scopes_2000_; lean_object* v_infoState_2001_; lean_object* v_traceState_2002_; lean_object* v_snapshotTasks_2003_; lean_object* v_codeQualityEntryTasks_2004_; 
v_env_1998_ = lean_ctor_get(v___y_1991_, 0);
lean_inc_ref(v_env_1998_);
v_messages_1999_ = lean_ctor_get(v___y_1991_, 1);
lean_inc_ref(v_messages_1999_);
v_scopes_2000_ = lean_ctor_get(v___y_1991_, 2);
lean_inc(v_scopes_2000_);
v_infoState_2001_ = lean_ctor_get(v___y_1991_, 8);
lean_inc_ref(v_infoState_2001_);
v_traceState_2002_ = lean_ctor_get(v___y_1991_, 9);
lean_inc_ref(v_traceState_2002_);
v_snapshotTasks_2003_ = lean_ctor_get(v___y_1991_, 10);
lean_inc_ref(v_snapshotTasks_2003_);
v_codeQualityEntryTasks_2004_ = lean_ctor_get(v___y_1991_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2004_);
v___y_1911_ = v___y_1975_;
v___y_1912_ = v___y_1976_;
v___y_1913_ = v___y_1977_;
v___y_1914_ = v___y_1978_;
v___y_1915_ = v___y_1979_;
v___y_1916_ = v___y_1981_;
v___y_1917_ = v___y_1980_;
v___y_1918_ = v___y_1982_;
v___y_1919_ = v___y_1983_;
v___y_1920_ = v___y_1984_;
v___y_1921_ = v___y_1985_;
v___y_1922_ = v___y_1986_;
v___y_1923_ = v___y_1987_;
v___y_1924_ = v___y_1988_;
v___y_1925_ = v___y_1989_;
v___y_1926_ = v___y_1990_;
v___y_1927_ = v___y_1991_;
v_env_1928_ = v_env_1998_;
v_messages_1929_ = v_messages_1999_;
v_scopes_1930_ = v_scopes_2000_;
v_infoState_1931_ = v_infoState_2001_;
v_traceState_1932_ = v_traceState_2002_;
v_snapshotTasks_1933_ = v_snapshotTasks_2003_;
v_codeQualityEntryTasks_1934_ = v_codeQualityEntryTasks_2004_;
v___y_1935_ = v___y_1992_;
v___y_1936_ = v___y_1993_;
v___y_1937_ = v___y_1994_;
v___y_1938_ = v___y_1995_;
v___y_1939_ = v___y_1996_;
v_reportedCmdState_1940_ = v_reportedCmdState_1997_;
goto v___jp_1910_;
}
v___jp_2005_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; uint8_t v___x_2027_; 
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_2021_);
lean_ctor_set(v___x_2022_, 1, v_val_1864_);
lean_inc_ref(v___y_2012_);
lean_inc_n(v_pos_1870_, 2);
lean_inc(v_revCmds_1856_);
lean_inc(v_fst_1855_);
v___x_2023_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1855_, v_revCmds_1856_, v_cmdState_1871_, v_pos_1870_, v___x_2022_, v___y_2012_, v_a_1859_);
v___x_2024_ = lean_box(v_val_1858_);
v___x_2025_ = lean_box(v___x_1862_);
lean_inc_ref(v_a_1859_);
lean_inc(v___y_2016_);
lean_inc_ref(v___x_1866_);
lean_inc_ref(v___x_2023_);
lean_inc_ref(v___y_2008_);
lean_inc_ref(v___y_2013_);
v___f_2026_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2026_, 0, v___y_2013_);
lean_closure_set(v___f_2026_, 1, v___y_2008_);
lean_closure_set(v___f_2026_, 2, v___x_2024_);
lean_closure_set(v___f_2026_, 3, v_val_1872_);
lean_closure_set(v___f_2026_, 4, v___x_2023_);
lean_closure_set(v___f_2026_, 5, v___x_1866_);
lean_closure_set(v___f_2026_, 6, v___y_2016_);
lean_closure_set(v___f_2026_, 7, v___x_2025_);
lean_closure_set(v___f_2026_, 8, v_a_1859_);
lean_closure_set(v___f_2026_, 9, v_pos_1870_);
lean_closure_set(v___f_2026_, 10, v___x_1873_);
v___x_2027_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1874_, v___x_1875_);
if (v___x_2027_ == 0)
{
lean_inc_ref(v___x_2023_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2011_);
lean_inc(v___y_2006_);
v___y_1975_ = v___y_2006_;
v___y_1976_ = v___y_2008_;
v___y_1977_ = v___y_2010_;
v___y_1978_ = v___y_2011_;
v___y_1979_ = v___y_2013_;
v___y_1980_ = v___y_2016_;
v___y_1981_ = v___y_2015_;
v___y_1982_ = v___y_2017_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2013_;
v___y_1985_ = v___y_2012_;
v___y_1986_ = v___y_2018_;
v___y_1987_ = v___y_2016_;
v___y_1988_ = v___y_2015_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2009_;
v___y_1991_ = v___x_2023_;
v___y_1992_ = v___y_2006_;
v___y_1993_ = v___y_2019_;
v___y_1994_ = v___y_2007_;
v___y_1995_ = v___y_2020_;
v___y_1996_ = v___f_2026_;
v_reportedCmdState_1997_ = v___x_2023_;
goto v___jp_1974_;
}
else
{
uint8_t v___x_2028_; 
lean_inc(v_fst_1855_);
v___x_2028_ = l_Lean_Parser_isTerminalCommand(v_fst_1855_);
if (v___x_2028_ == 0)
{
if (v___x_2027_ == 0)
{
lean_inc_ref(v___x_2023_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2011_);
lean_inc(v___y_2006_);
v___y_1975_ = v___y_2006_;
v___y_1976_ = v___y_2008_;
v___y_1977_ = v___y_2010_;
v___y_1978_ = v___y_2011_;
v___y_1979_ = v___y_2013_;
v___y_1980_ = v___y_2016_;
v___y_1981_ = v___y_2015_;
v___y_1982_ = v___y_2017_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2013_;
v___y_1985_ = v___y_2012_;
v___y_1986_ = v___y_2018_;
v___y_1987_ = v___y_2016_;
v___y_1988_ = v___y_2015_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2009_;
v___y_1991_ = v___x_2023_;
v___y_1992_ = v___y_2006_;
v___y_1993_ = v___y_2019_;
v___y_1994_ = v___y_2007_;
v___y_1995_ = v___y_2020_;
v___y_1996_ = v___f_2026_;
v_reportedCmdState_1997_ = v___x_2023_;
goto v___jp_1974_;
}
else
{
lean_object* v_env_2029_; lean_object* v_messages_2030_; lean_object* v_scopes_2031_; lean_object* v_infoState_2032_; lean_object* v_traceState_2033_; lean_object* v_snapshotTasks_2034_; lean_object* v_codeQualityEntryTasks_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_env_2029_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref_n(v_env_2029_, 2);
v_messages_2030_ = lean_ctor_get(v___x_2023_, 1);
lean_inc_ref(v_messages_2030_);
v_scopes_2031_ = lean_ctor_get(v___x_2023_, 2);
lean_inc(v_scopes_2031_);
v_infoState_2032_ = lean_ctor_get(v___x_2023_, 8);
lean_inc_ref(v_infoState_2032_);
v_traceState_2033_ = lean_ctor_get(v___x_2023_, 9);
lean_inc_ref(v_traceState_2033_);
v_snapshotTasks_2034_ = lean_ctor_get(v___x_2023_, 10);
lean_inc_ref(v_snapshotTasks_2034_);
v_codeQualityEntryTasks_2035_ = lean_ctor_get(v___x_2023_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2035_);
v___x_2036_ = lean_mk_empty_array_with_capacity(v___y_2017_);
lean_inc_ref(v___x_2036_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_inc_n(v___y_2016_, 4);
v___x_2038_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
lean_ctor_set(v___x_2038_, 2, v___y_2016_);
lean_ctor_set(v___x_2038_, 3, v___y_2016_);
lean_ctor_set_usize(v___x_2038_, 4, v___y_2010_);
v___x_2039_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2038_, 2);
v___x_2040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2038_);
lean_ctor_set(v___x_2040_, 2, v___x_2039_);
v___x_2041_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2042_ = l_Lean_Options_empty;
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_mk_empty_array_with_capacity(v___y_2016_);
lean_inc_ref_n(v___x_2044_, 3);
lean_inc_n(v___x_1861_, 2);
v___x_2045_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2045_, 0, v___x_2041_);
lean_ctor_set(v___x_2045_, 1, v___x_2042_);
lean_ctor_set(v___x_2045_, 2, v___x_1861_);
lean_ctor_set(v___x_2045_, 3, v___x_2043_);
lean_ctor_set(v___x_2045_, 4, v___x_2043_);
lean_ctor_set(v___x_2045_, 5, v___x_2044_);
lean_ctor_set(v___x_2045_, 6, v___x_2044_);
lean_ctor_set(v___x_2045_, 7, v___x_2043_);
lean_ctor_set(v___x_2045_, 8, v___x_2043_);
lean_ctor_set(v___x_2045_, 9, v___x_2043_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*10, v_val_1858_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*10 + 1, v_val_1858_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*10 + 2, v_val_1858_);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2043_);
v___x_2047_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2048_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2049_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1861_);
v___x_2050_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2051_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
lean_ctor_set(v___x_2051_, 2, v___x_2038_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*3, v___x_1862_);
v___x_2052_ = lean_box(0);
lean_inc_ref(v___y_2008_);
v___x_2053_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2053_, 0, v_env_2029_);
lean_ctor_set(v___x_2053_, 1, v___x_2040_);
lean_ctor_set(v___x_2053_, 2, v___x_2046_);
lean_ctor_set(v___x_2053_, 3, v___x_2039_);
lean_ctor_set(v___x_2053_, 4, v___x_2047_);
lean_ctor_set(v___x_2053_, 5, v___y_2016_);
lean_ctor_set(v___x_2053_, 6, v___x_2048_);
lean_ctor_set(v___x_2053_, 7, v___x_2049_);
lean_ctor_set(v___x_2053_, 8, v___x_2051_);
lean_ctor_set(v___x_2053_, 9, v___y_2008_);
lean_ctor_set(v___x_2053_, 10, v___x_2044_);
lean_ctor_set(v___x_2053_, 11, v___x_2052_);
lean_ctor_set(v___x_2053_, 12, v___x_2044_);
lean_inc_ref(v___y_2015_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2011_);
lean_inc(v___y_2006_);
v___y_1911_ = v___y_2006_;
v___y_1912_ = v___y_2008_;
v___y_1913_ = v___y_2010_;
v___y_1914_ = v___y_2011_;
v___y_1915_ = v___y_2013_;
v___y_1916_ = v___y_2015_;
v___y_1917_ = v___y_2016_;
v___y_1918_ = v___y_2017_;
v___y_1919_ = v___y_2011_;
v___y_1920_ = v___y_2013_;
v___y_1921_ = v___y_2012_;
v___y_1922_ = v___y_2018_;
v___y_1923_ = v___y_2016_;
v___y_1924_ = v___y_2015_;
v___y_1925_ = v___y_2014_;
v___y_1926_ = v___y_2009_;
v___y_1927_ = v___x_2023_;
v_env_1928_ = v_env_2029_;
v_messages_1929_ = v_messages_2030_;
v_scopes_1930_ = v_scopes_2031_;
v_infoState_1931_ = v_infoState_2032_;
v_traceState_1932_ = v_traceState_2033_;
v_snapshotTasks_1933_ = v_snapshotTasks_2034_;
v_codeQualityEntryTasks_1934_ = v_codeQualityEntryTasks_2035_;
v___y_1935_ = v___y_2006_;
v___y_1936_ = v___y_2019_;
v___y_1937_ = v___y_2007_;
v___y_1938_ = v___y_2020_;
v___y_1939_ = v___f_2026_;
v_reportedCmdState_1940_ = v___x_2053_;
goto v___jp_1910_;
}
}
else
{
lean_inc_ref(v___x_2023_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2011_);
lean_inc(v___y_2006_);
v___y_1975_ = v___y_2006_;
v___y_1976_ = v___y_2008_;
v___y_1977_ = v___y_2010_;
v___y_1978_ = v___y_2011_;
v___y_1979_ = v___y_2013_;
v___y_1980_ = v___y_2016_;
v___y_1981_ = v___y_2015_;
v___y_1982_ = v___y_2017_;
v___y_1983_ = v___y_2011_;
v___y_1984_ = v___y_2013_;
v___y_1985_ = v___y_2012_;
v___y_1986_ = v___y_2018_;
v___y_1987_ = v___y_2016_;
v___y_1988_ = v___y_2015_;
v___y_1989_ = v___y_2014_;
v___y_1990_ = v___y_2009_;
v___y_1991_ = v___x_2023_;
v___y_1992_ = v___y_2006_;
v___y_1993_ = v___y_2019_;
v___y_1994_ = v___y_2007_;
v___y_1995_ = v___y_2020_;
v___y_1996_ = v___f_2026_;
v_reportedCmdState_1997_ = v___x_2023_;
goto v___jp_1974_;
}
}
}
v___jp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2056_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1860_);
v___x_2057_ = l_IO_CancelToken_new();
v___x_2058_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1861_);
v___x_2059_ = l_Lean_Name_str___override(v___x_1861_, v___x_2058_);
v___x_2060_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2061_ = l_Lean_Name_str___override(v___x_2059_, v___x_2060_);
v___x_2062_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2063_ = l_Lean_Name_str___override(v___x_2061_, v___x_2062_);
v___x_2064_ = l_Lean_Name_str___override(v___x_2063_, v___x_2060_);
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = l_Lean_Name_num___override(v___x_2064_, v___x_2065_);
v___x_2067_ = l_Lean_Name_str___override(v___x_2066_, v___x_2060_);
v___x_2068_ = l_Lean_Name_str___override(v___x_2067_, v___x_2062_);
v___x_2069_ = l_Lean_Name_str___override(v___x_2068_, v___x_2060_);
v___x_2070_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2071_ = l_Lean_Name_str___override(v___x_2069_, v___x_2070_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2073_ = l_Lean_Name_str___override(v___x_2071_, v___x_2072_);
v___x_2074_ = l_Lean_Name_toString(v___x_2073_, v___x_1862_);
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_unsigned_to_nat(32u);
v___x_2077_ = ((size_t)5ULL);
v___x_2078_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2074_, 2);
v___x_2079_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2079_, 0, v___x_2074_);
lean_ctor_set(v___x_2079_, 1, v___x_2056_);
lean_ctor_set(v___x_2079_, 2, v___x_2075_);
lean_ctor_set(v___x_2079_, 3, v___x_2078_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*4, v_val_1858_);
v___x_2080_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2081_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2074_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
lean_ctor_set(v___x_2081_, 2, v___x_2075_);
lean_ctor_set(v___x_2081_, 3, v___x_2078_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*4, v_val_1858_);
lean_inc(v_fst_1863_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_fst_1863_);
v___x_2083_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2082_);
lean_inc_ref(v___x_2057_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2057_);
v___x_2085_ = l_IO_Promise_result_x21___redArg(v_val_1864_);
lean_inc_ref(v___x_2085_);
lean_inc(v___x_2083_);
lean_inc_ref_n(v___x_2082_, 3);
v___x_2086_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2082_);
lean_ctor_set(v___x_2086_, 1, v___x_2083_);
lean_ctor_set(v___x_2086_, 2, v___x_2084_);
lean_ctor_set(v___x_2086_, 3, v___x_2085_);
v___x_2087_ = l_IO_Promise_result_x21___redArg(v_val_1865_);
lean_inc_ref(v___x_2087_);
lean_inc_n(v___x_1853_, 3);
v___x_2088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2082_);
lean_ctor_set(v___x_2088_, 1, v___x_1853_);
lean_ctor_set(v___x_2088_, 2, v___x_2075_);
lean_ctor_set(v___x_2088_, 3, v___x_2087_);
v___x_2089_ = l_IO_Promise_result_x21___redArg(v_val_1872_);
lean_inc_ref(v___x_2089_);
v___x_2090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2082_);
lean_ctor_set(v___x_2090_, 1, v___x_1853_);
lean_ctor_set(v___x_2090_, 2, v___x_2075_);
lean_ctor_set(v___x_2090_, 3, v___x_2089_);
v___x_2091_ = l_IO_Promise_result_x21___redArg(v_val_1854_);
v___x_2092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2075_);
lean_ctor_set(v___x_2092_, 1, v___x_1853_);
lean_ctor_set(v___x_2092_, 2, v___x_2075_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
lean_inc_ref(v___x_2081_);
v___x_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2081_);
lean_ctor_set(v___x_2093_, 1, v___x_2086_);
lean_ctor_set(v___x_2093_, 2, v___x_2088_);
lean_ctor_set(v___x_2093_, 3, v___x_2090_);
lean_ctor_set(v___x_2093_, 4, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2079_);
lean_ctor_set(v___x_2094_, 1, v_fst_1863_);
lean_ctor_set(v___x_2094_, 2, v_snd_1876_);
lean_ctor_set(v___x_2094_, 3, v___x_2093_);
lean_ctor_set(v___x_2094_, 4, v___y_2055_);
v___x_2095_ = lean_io_promise_resolve(v___x_2094_, v_prom_1877_);
if (lean_obj_tag(v_old_x3f_1878_) == 0)
{
v___y_2006_ = v___x_2075_;
v___y_2007_ = v___x_2082_;
v___y_2008_ = v___x_2078_;
v___y_2009_ = v___x_2083_;
v___y_2010_ = v___x_2077_;
v___y_2011_ = v___x_2075_;
v___y_2012_ = v___x_2057_;
v___y_2013_ = v___x_2074_;
v___y_2014_ = v___x_2085_;
v___y_2015_ = v___x_2081_;
v___y_2016_ = v___x_2065_;
v___y_2017_ = v___x_2076_;
v___y_2018_ = v___x_2087_;
v___y_2019_ = v___x_2089_;
v___y_2020_ = v___x_2075_;
v___y_2021_ = v___x_2075_;
goto v___jp_2005_;
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2107_; 
v_val_2096_ = lean_ctor_get(v_old_x3f_1878_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_old_x3f_1878_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2098_ = v_old_x3f_1878_;
v_isShared_2099_ = v_isSharedCheck_2107_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_dec(v_old_x3f_1878_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2107_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_elabSnap_2100_; lean_object* v_stx_2101_; lean_object* v_elabSnap_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_elabSnap_2100_ = lean_ctor_get(v_val_2096_, 3);
lean_inc_ref(v_elabSnap_2100_);
v_stx_2101_ = lean_ctor_get(v_val_2096_, 1);
lean_inc(v_stx_2101_);
lean_dec(v_val_2096_);
v_elabSnap_2102_ = lean_ctor_get(v_elabSnap_2100_, 1);
lean_inc_ref(v_elabSnap_2102_);
lean_dec_ref(v_elabSnap_2100_);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_stx_2101_);
lean_ctor_set(v___x_2103_, 1, v_elabSnap_2102_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2103_);
v___x_2105_ = v___x_2098_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
v___y_2006_ = v___x_2075_;
v___y_2007_ = v___x_2082_;
v___y_2008_ = v___x_2078_;
v___y_2009_ = v___x_2083_;
v___y_2010_ = v___x_2077_;
v___y_2011_ = v___x_2075_;
v___y_2012_ = v___x_2057_;
v___y_2013_ = v___x_2074_;
v___y_2014_ = v___x_2085_;
v___y_2015_ = v___x_2081_;
v___y_2016_ = v___x_2065_;
v___y_2017_ = v___x_2076_;
v___y_2018_ = v___x_2087_;
v___y_2019_ = v___x_2089_;
v___y_2020_ = v___x_2075_;
v___y_2021_ = v___x_2105_;
goto v___jp_2005_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2121_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2125_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2126_, lean_object* v_revCmds_2127_, lean_object* v_fst_2128_, uint8_t v_val_2129_, lean_object* v_a_2130_, lean_object* v_snd_2131_, lean_object* v___x_2132_, uint8_t v___x_2133_, lean_object* v___x_2134_, lean_object* v___f_2135_, lean_object* v___f_2136_, lean_object* v___f_2137_, lean_object* v_pos_2138_, lean_object* v_cmdState_2139_, lean_object* v___x_2140_, lean_object* v_opts_2141_, lean_object* v_prom_2142_, lean_object* v_old_x3f_2143_, lean_object* v_parseCancelTk_2144_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v_snapshotTasks_2157_; lean_object* v___y_2158_; lean_object* v_traceTask_2159_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2183_; size_t v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v_env_2195_; lean_object* v_messages_2196_; lean_object* v_scopes_2197_; lean_object* v_infoState_2198_; lean_object* v_traceState_2199_; lean_object* v_snapshotTasks_2200_; lean_object* v_codeQualityEntryTasks_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v_reportedCmdState_2214_; size_t v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v_reportedCmdState_2273_; lean_object* v___x_2281_; size_t v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v_fst_2412_; lean_object* v_snd_2413_; uint8_t v___x_2425_; 
v___x_2146_ = lean_io_promise_new();
v___x_2147_ = lean_io_promise_new();
v___x_2148_ = lean_io_promise_new();
v___x_2149_ = lean_io_promise_new();
v___x_2281_ = l_Lean_internal_cmdlineSnapshots;
v___x_2425_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2141_, v___x_2281_);
if (v___x_2425_ == 0)
{
lean_inc_ref(v_fst_2128_);
lean_inc(v_fst_2126_);
v_fst_2412_ = v_fst_2126_;
v_snd_2413_ = v_fst_2128_;
goto v___jp_2411_;
}
else
{
uint8_t v___x_2426_; 
lean_inc(v_fst_2126_);
v___x_2426_ = l_Lean_Parser_isTerminalCommand(v_fst_2126_);
if (v___x_2426_ == 0)
{
if (v___x_2425_ == 0)
{
lean_inc_ref(v_fst_2128_);
lean_inc(v_fst_2126_);
v_fst_2412_ = v_fst_2126_;
v_snd_2413_ = v_fst_2128_;
goto v___jp_2411_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_box(0);
v___x_2428_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2412_ = v___x_2427_;
v_snd_2413_ = v___x_2428_;
goto v___jp_2411_;
}
}
else
{
lean_inc_ref(v_fst_2128_);
lean_inc(v_fst_2126_);
v_fst_2412_ = v_fst_2126_;
v_snd_2413_ = v_fst_2128_;
goto v___jp_2411_;
}
}
v___jp_2150_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2160_, 0, v___y_2155_);
lean_ctor_set(v___x_2160_, 1, v___y_2151_);
lean_ctor_set(v___x_2160_, 2, v___y_2158_);
lean_ctor_set(v___x_2160_, 3, v_traceTask_2159_);
v___x_2161_ = lean_array_push(v_snapshotTasks_2157_, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2153_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_io_promise_resolve(v___x_2162_, v___x_2149_);
lean_dec(v___x_2149_);
if (lean_obj_tag(v___y_2152_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_val_2164_ = lean_ctor_get(v___y_2152_, 0);
lean_inc(v_val_2164_);
lean_dec_ref_known(v___y_2152_, 1);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2166_, 0, v_fst_2126_);
lean_ctor_set(v___x_2166_, 1, v_revCmds_2127_);
v___x_2167_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2165_, v_fst_2128_, v___y_2156_, v_val_2164_, v_val_2129_, v___y_2154_, v___x_2166_, v_a_2130_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; 
lean_dec_ref(v___y_2156_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2152_);
lean_dec_ref(v_fst_2128_);
lean_dec(v_revCmds_2127_);
lean_dec(v_fst_2126_);
v___x_2168_ = lean_box(0);
return v___x_2168_;
}
}
v___jp_2169_:
{
lean_object* v_snapshotTasks_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_snapshotTasks_2178_ = lean_ctor_get(v___y_2174_, 10);
lean_inc_ref(v_snapshotTasks_2178_);
v___x_2179_ = lean_mk_empty_array_with_capacity(v___y_2176_);
lean_dec(v___y_2176_);
lean_inc_ref(v___y_2172_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___y_2172_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_task_pure(v___x_2180_);
v___y_2151_ = v___y_2170_;
v___y_2152_ = v___y_2171_;
v___y_2153_ = v___y_2172_;
v___y_2154_ = v___y_2173_;
v___y_2155_ = v___y_2175_;
v___y_2156_ = v___y_2174_;
v_snapshotTasks_2157_ = v_snapshotTasks_2178_;
v___y_2158_ = v___y_2177_;
v_traceTask_2159_ = v___x_2181_;
goto v___jp_2150_;
}
v___jp_2182_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_opts_2224_; uint8_t v_hasTrace_2225_; 
v___x_2215_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2196_);
v___x_2216_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2216_, 0, v___y_2210_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
lean_ctor_set(v___x_2216_, 2, v___y_2213_);
lean_ctor_set(v___x_2216_, 3, v_traceState_2199_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*4, v_val_2129_);
v___x_2217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v_reportedCmdState_2214_);
lean_ctor_set(v___x_2217_, 2, v_codeQualityEntryTasks_2201_);
v___x_2218_ = lean_io_promise_resolve(v___x_2217_, v___x_2147_);
lean_dec(v___x_2147_);
v___x_2219_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2198_);
lean_inc(v___y_2204_);
v___x_2220_ = l_BaseIO_chainTask___redArg(v___x_2219_, v___y_2211_, v___y_2204_, v___x_2133_);
v___x_2221_ = l_Lean_inheritedTraceOptions;
v___x_2222_ = lean_st_ref_get(v___x_2221_);
v___x_2223_ = l_List_head_x21___redArg(v___x_2134_, v_scopes_2197_);
lean_dec(v_scopes_2197_);
lean_dec_ref(v___x_2134_);
v_opts_2224_ = lean_ctor_get(v___x_2223_, 1);
lean_inc_ref(v_opts_2224_);
lean_dec(v___x_2223_);
v_hasTrace_2225_ = lean_ctor_get_uint8(v_opts_2224_, sizeof(void*)*1);
if (v_hasTrace_2225_ == 0)
{
lean_dec_ref(v_opts_2224_);
lean_dec(v___x_2222_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_snapshotTasks_2200_);
lean_dec_ref(v_env_2195_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec_ref(v___y_2183_);
lean_dec(v_pos_2138_);
lean_dec_ref(v___f_2137_);
lean_dec_ref(v___f_2136_);
lean_dec_ref(v___f_2135_);
lean_dec(v___x_2132_);
v___y_2170_ = v___y_2209_;
v___y_2171_ = v___y_2192_;
v___y_2172_ = v___y_2193_;
v___y_2173_ = v___y_2212_;
v___y_2174_ = v___y_2194_;
v___y_2175_ = v___y_2202_;
v___y_2176_ = v___y_2204_;
v___y_2177_ = v___y_2207_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2227_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2222_, v_opts_2224_, v___x_2226_);
lean_dec(v___x_2222_);
if (v___x_2227_ == 0)
{
lean_dec_ref(v_opts_2224_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_snapshotTasks_2200_);
lean_dec_ref(v_env_2195_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec_ref(v___y_2183_);
lean_dec(v_pos_2138_);
lean_dec_ref(v___f_2137_);
lean_dec_ref(v___f_2136_);
lean_dec_ref(v___f_2135_);
lean_dec(v___x_2132_);
v___y_2170_ = v___y_2209_;
v___y_2171_ = v___y_2192_;
v___y_2172_ = v___y_2193_;
v___y_2173_ = v___y_2212_;
v___y_2174_ = v___y_2194_;
v___y_2175_ = v___y_2202_;
v___y_2176_ = v___y_2204_;
v___y_2177_ = v___y_2207_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_inc_n(v___y_2204_, 3);
v___x_2228_ = lean_task_map(v___f_2135_, v___y_2191_, v___y_2204_, v___x_2133_);
lean_inc_n(v___y_2207_, 3);
lean_inc_n(v___y_2206_, 2);
lean_inc_n(v___y_2205_, 2);
v___x_2229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2229_, 0, v___y_2205_);
lean_ctor_set(v___x_2229_, 1, v___y_2206_);
lean_ctor_set(v___x_2229_, 2, v___y_2207_);
lean_ctor_set(v___x_2229_, 3, v___x_2228_);
v___x_2230_ = lean_task_map(v___f_2136_, v___y_2208_, v___y_2204_, v___x_2133_);
v___x_2231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2231_, 0, v___y_2205_);
lean_ctor_set(v___x_2231_, 1, v___y_2206_);
lean_ctor_set(v___x_2231_, 2, v___y_2207_);
lean_ctor_set(v___x_2231_, 3, v___x_2230_);
v___x_2232_ = lean_task_map(v___f_2137_, v___y_2203_, v___y_2204_, v___x_2133_);
v___x_2233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2233_, 0, v___y_2205_);
lean_ctor_set(v___x_2233_, 1, v___y_2206_);
lean_ctor_set(v___x_2233_, 2, v___y_2207_);
lean_ctor_set(v___x_2233_, 3, v___x_2232_);
v___x_2234_ = lean_unsigned_to_nat(3u);
v___x_2235_ = lean_mk_empty_array_with_capacity(v___x_2234_);
v___x_2236_ = lean_array_push(v___x_2235_, v___x_2229_);
v___x_2237_ = lean_array_push(v___x_2236_, v___x_2231_);
v___x_2238_ = lean_array_push(v___x_2237_, v___x_2233_);
v___x_2239_ = l_Array_append___redArg(v___x_2238_, v_snapshotTasks_2200_);
lean_inc_ref(v___y_2193_);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2193_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_box_usize(v___y_2184_);
v___x_2242_ = lean_box(v___x_2133_);
v___x_2243_ = lean_box(v_val_2129_);
v___x_2244_ = lean_box(v___x_2227_);
lean_inc_ref(v___x_2240_);
lean_inc_ref(v___y_2189_);
lean_inc_ref(v_a_2130_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2245_, 0, v_a_2130_);
lean_closure_set(v___f_2245_, 1, v_opts_2224_);
lean_closure_set(v___f_2245_, 2, v___x_2132_);
lean_closure_set(v___f_2245_, 3, v___y_2186_);
lean_closure_set(v___f_2245_, 4, v___y_2190_);
lean_closure_set(v___f_2245_, 5, v___x_2241_);
lean_closure_set(v___f_2245_, 6, v___x_2242_);
lean_closure_set(v___f_2245_, 7, v_env_2195_);
lean_closure_set(v___f_2245_, 8, v___y_2189_);
lean_closure_set(v___f_2245_, 9, v___x_2240_);
lean_closure_set(v___f_2245_, 10, v_pos_2138_);
lean_closure_set(v___f_2245_, 11, v___x_2243_);
lean_closure_set(v___f_2245_, 12, v___y_2185_);
lean_closure_set(v___f_2245_, 13, v___y_2188_);
lean_closure_set(v___f_2245_, 14, v___y_2183_);
lean_closure_set(v___f_2245_, 15, v___x_2221_);
lean_closure_set(v___f_2245_, 16, v___y_2187_);
lean_closure_set(v___f_2245_, 17, v___x_2244_);
v___x_2246_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2240_);
v___x_2247_ = lean_io_bind_task(v___x_2246_, v___f_2245_, v___y_2204_, v_val_2129_);
v___y_2151_ = v___y_2209_;
v___y_2152_ = v___y_2192_;
v___y_2153_ = v___y_2193_;
v___y_2154_ = v___y_2212_;
v___y_2155_ = v___y_2202_;
v___y_2156_ = v___y_2194_;
v_snapshotTasks_2157_ = v_snapshotTasks_2200_;
v___y_2158_ = v___y_2207_;
v_traceTask_2159_ = v___x_2247_;
goto v___jp_2150_;
}
}
}
v___jp_2248_:
{
lean_object* v_env_2274_; lean_object* v_messages_2275_; lean_object* v_scopes_2276_; lean_object* v_infoState_2277_; lean_object* v_traceState_2278_; lean_object* v_snapshotTasks_2279_; lean_object* v_codeQualityEntryTasks_2280_; 
v_env_2274_ = lean_ctor_get(v___y_2260_, 0);
lean_inc_ref(v_env_2274_);
v_messages_2275_ = lean_ctor_get(v___y_2260_, 1);
lean_inc_ref(v_messages_2275_);
v_scopes_2276_ = lean_ctor_get(v___y_2260_, 2);
lean_inc(v_scopes_2276_);
v_infoState_2277_ = lean_ctor_get(v___y_2260_, 8);
lean_inc_ref(v_infoState_2277_);
v_traceState_2278_ = lean_ctor_get(v___y_2260_, 9);
lean_inc_ref(v_traceState_2278_);
v_snapshotTasks_2279_ = lean_ctor_get(v___y_2260_, 10);
lean_inc_ref(v_snapshotTasks_2279_);
v_codeQualityEntryTasks_2280_ = lean_ctor_get(v___y_2260_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2280_);
v___y_2183_ = v___y_2250_;
v___y_2184_ = v___y_2249_;
v___y_2185_ = v___y_2252_;
v___y_2186_ = v___y_2251_;
v___y_2187_ = v___y_2253_;
v___y_2188_ = v___y_2254_;
v___y_2189_ = v___y_2255_;
v___y_2190_ = v___y_2256_;
v___y_2191_ = v___y_2257_;
v___y_2192_ = v___y_2258_;
v___y_2193_ = v___y_2259_;
v___y_2194_ = v___y_2260_;
v_env_2195_ = v_env_2274_;
v_messages_2196_ = v_messages_2275_;
v_scopes_2197_ = v_scopes_2276_;
v_infoState_2198_ = v_infoState_2277_;
v_traceState_2199_ = v_traceState_2278_;
v_snapshotTasks_2200_ = v_snapshotTasks_2279_;
v_codeQualityEntryTasks_2201_ = v_codeQualityEntryTasks_2280_;
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
v_reportedCmdState_2214_ = v_reportedCmdState_2273_;
goto v___jp_2182_;
}
v___jp_2282_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___f_2305_; uint8_t v___x_2306_; 
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2146_);
lean_inc_ref(v___y_2293_);
lean_inc_n(v_pos_2138_, 2);
lean_inc(v_revCmds_2127_);
lean_inc(v_fst_2126_);
v___x_2302_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2126_, v_revCmds_2127_, v_cmdState_2139_, v_pos_2138_, v___x_2301_, v___y_2293_, v_a_2130_);
v___x_2303_ = lean_box(v_val_2129_);
v___x_2304_ = lean_box(v___x_2133_);
lean_inc_ref(v_a_2130_);
lean_inc(v___y_2288_);
lean_inc_ref(v___x_2134_);
lean_inc_ref(v___x_2302_);
lean_inc_ref(v___y_2292_);
lean_inc_ref(v___y_2289_);
v___f_2305_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2305_, 0, v___y_2289_);
lean_closure_set(v___f_2305_, 1, v___y_2292_);
lean_closure_set(v___f_2305_, 2, v___x_2303_);
lean_closure_set(v___f_2305_, 3, v___x_2148_);
lean_closure_set(v___f_2305_, 4, v___x_2302_);
lean_closure_set(v___f_2305_, 5, v___x_2134_);
lean_closure_set(v___f_2305_, 6, v___y_2288_);
lean_closure_set(v___f_2305_, 7, v___x_2304_);
lean_closure_set(v___f_2305_, 8, v_a_2130_);
lean_closure_set(v___f_2305_, 9, v_pos_2138_);
lean_closure_set(v___f_2305_, 10, v___x_2140_);
v___x_2306_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2141_, v___x_2281_);
if (v___x_2306_ == 0)
{
lean_inc_ref(v___x_2302_);
lean_inc(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2285_);
v___y_2249_ = v___y_2283_;
v___y_2250_ = v___y_2285_;
v___y_2251_ = v___y_2288_;
v___y_2252_ = v___y_2289_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v___y_2255_ = v___y_2292_;
v___y_2256_ = v___y_2294_;
v___y_2257_ = v___y_2286_;
v___y_2258_ = v___y_2295_;
v___y_2259_ = v___y_2285_;
v___y_2260_ = v___x_2302_;
v___y_2261_ = v___y_2296_;
v___y_2262_ = v___y_2297_;
v___y_2263_ = v___y_2288_;
v___y_2264_ = v___y_2284_;
v___y_2265_ = v___y_2287_;
v___y_2266_ = v___y_2290_;
v___y_2267_ = v___y_2299_;
v___y_2268_ = v___y_2298_;
v___y_2269_ = v___y_2289_;
v___y_2270_ = v___f_2305_;
v___y_2271_ = v___y_2293_;
v___y_2272_ = v___y_2291_;
v_reportedCmdState_2273_ = v___x_2302_;
goto v___jp_2248_;
}
else
{
uint8_t v___x_2307_; 
lean_inc(v_fst_2126_);
v___x_2307_ = l_Lean_Parser_isTerminalCommand(v_fst_2126_);
if (v___x_2307_ == 0)
{
if (v___x_2306_ == 0)
{
lean_inc_ref(v___x_2302_);
lean_inc(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2285_);
v___y_2249_ = v___y_2283_;
v___y_2250_ = v___y_2285_;
v___y_2251_ = v___y_2288_;
v___y_2252_ = v___y_2289_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v___y_2255_ = v___y_2292_;
v___y_2256_ = v___y_2294_;
v___y_2257_ = v___y_2286_;
v___y_2258_ = v___y_2295_;
v___y_2259_ = v___y_2285_;
v___y_2260_ = v___x_2302_;
v___y_2261_ = v___y_2296_;
v___y_2262_ = v___y_2297_;
v___y_2263_ = v___y_2288_;
v___y_2264_ = v___y_2284_;
v___y_2265_ = v___y_2287_;
v___y_2266_ = v___y_2290_;
v___y_2267_ = v___y_2299_;
v___y_2268_ = v___y_2298_;
v___y_2269_ = v___y_2289_;
v___y_2270_ = v___f_2305_;
v___y_2271_ = v___y_2293_;
v___y_2272_ = v___y_2291_;
v_reportedCmdState_2273_ = v___x_2302_;
goto v___jp_2248_;
}
else
{
lean_object* v_env_2308_; lean_object* v_messages_2309_; lean_object* v_scopes_2310_; lean_object* v_infoState_2311_; lean_object* v_traceState_2312_; lean_object* v_snapshotTasks_2313_; lean_object* v_codeQualityEntryTasks_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_env_2308_ = lean_ctor_get(v___x_2302_, 0);
lean_inc_ref_n(v_env_2308_, 2);
v_messages_2309_ = lean_ctor_get(v___x_2302_, 1);
lean_inc_ref(v_messages_2309_);
v_scopes_2310_ = lean_ctor_get(v___x_2302_, 2);
lean_inc(v_scopes_2310_);
v_infoState_2311_ = lean_ctor_get(v___x_2302_, 8);
lean_inc_ref(v_infoState_2311_);
v_traceState_2312_ = lean_ctor_get(v___x_2302_, 9);
lean_inc_ref(v_traceState_2312_);
v_snapshotTasks_2313_ = lean_ctor_get(v___x_2302_, 10);
lean_inc_ref(v_snapshotTasks_2313_);
v_codeQualityEntryTasks_2314_ = lean_ctor_get(v___x_2302_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2314_);
v___x_2315_ = lean_mk_empty_array_with_capacity(v___y_2294_);
lean_inc_ref(v___x_2315_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_inc_n(v___y_2288_, 4);
v___x_2317_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v___x_2315_);
lean_ctor_set(v___x_2317_, 2, v___y_2288_);
lean_ctor_set(v___x_2317_, 3, v___y_2288_);
lean_ctor_set_usize(v___x_2317_, 4, v___y_2283_);
v___x_2318_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2317_, 2);
v___x_2319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2317_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
v___x_2320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2321_ = l_Lean_Options_empty;
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___y_2288_);
lean_inc_ref_n(v___x_2323_, 3);
lean_inc_n(v___x_2132_, 2);
v___x_2324_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2324_, 0, v___x_2320_);
lean_ctor_set(v___x_2324_, 1, v___x_2321_);
lean_ctor_set(v___x_2324_, 2, v___x_2132_);
lean_ctor_set(v___x_2324_, 3, v___x_2322_);
lean_ctor_set(v___x_2324_, 4, v___x_2322_);
lean_ctor_set(v___x_2324_, 5, v___x_2323_);
lean_ctor_set(v___x_2324_, 6, v___x_2323_);
lean_ctor_set(v___x_2324_, 7, v___x_2322_);
lean_ctor_set(v___x_2324_, 8, v___x_2322_);
lean_ctor_set(v___x_2324_, 9, v___x_2322_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*10, v_val_2129_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*10 + 1, v_val_2129_);
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*10 + 2, v_val_2129_);
v___x_2325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___x_2322_);
v___x_2326_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2327_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2328_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2132_);
v___x_2329_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2330_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
lean_ctor_set(v___x_2330_, 2, v___x_2317_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*3, v___x_2133_);
v___x_2331_ = lean_box(0);
lean_inc_ref(v___y_2292_);
v___x_2332_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2332_, 0, v_env_2308_);
lean_ctor_set(v___x_2332_, 1, v___x_2319_);
lean_ctor_set(v___x_2332_, 2, v___x_2325_);
lean_ctor_set(v___x_2332_, 3, v___x_2318_);
lean_ctor_set(v___x_2332_, 4, v___x_2326_);
lean_ctor_set(v___x_2332_, 5, v___y_2288_);
lean_ctor_set(v___x_2332_, 6, v___x_2327_);
lean_ctor_set(v___x_2332_, 7, v___x_2328_);
lean_ctor_set(v___x_2332_, 8, v___x_2330_);
lean_ctor_set(v___x_2332_, 9, v___y_2292_);
lean_ctor_set(v___x_2332_, 10, v___x_2323_);
lean_ctor_set(v___x_2332_, 11, v___x_2331_);
lean_ctor_set(v___x_2332_, 12, v___x_2323_);
lean_inc(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc_ref(v___y_2285_);
v___y_2183_ = v___y_2285_;
v___y_2184_ = v___y_2283_;
v___y_2185_ = v___y_2289_;
v___y_2186_ = v___y_2288_;
v___y_2187_ = v___y_2290_;
v___y_2188_ = v___y_2291_;
v___y_2189_ = v___y_2292_;
v___y_2190_ = v___y_2294_;
v___y_2191_ = v___y_2286_;
v___y_2192_ = v___y_2295_;
v___y_2193_ = v___y_2285_;
v___y_2194_ = v___x_2302_;
v_env_2195_ = v_env_2308_;
v_messages_2196_ = v_messages_2309_;
v_scopes_2197_ = v_scopes_2310_;
v_infoState_2198_ = v_infoState_2311_;
v_traceState_2199_ = v_traceState_2312_;
v_snapshotTasks_2200_ = v_snapshotTasks_2313_;
v_codeQualityEntryTasks_2201_ = v_codeQualityEntryTasks_2314_;
v___y_2202_ = v___y_2296_;
v___y_2203_ = v___y_2297_;
v___y_2204_ = v___y_2288_;
v___y_2205_ = v___y_2284_;
v___y_2206_ = v___y_2287_;
v___y_2207_ = v___y_2290_;
v___y_2208_ = v___y_2299_;
v___y_2209_ = v___y_2298_;
v___y_2210_ = v___y_2289_;
v___y_2211_ = v___f_2305_;
v___y_2212_ = v___y_2293_;
v___y_2213_ = v___y_2291_;
v_reportedCmdState_2214_ = v___x_2332_;
goto v___jp_2182_;
}
}
else
{
lean_inc_ref(v___x_2302_);
lean_inc(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2285_);
v___y_2249_ = v___y_2283_;
v___y_2250_ = v___y_2285_;
v___y_2251_ = v___y_2288_;
v___y_2252_ = v___y_2289_;
v___y_2253_ = v___y_2290_;
v___y_2254_ = v___y_2291_;
v___y_2255_ = v___y_2292_;
v___y_2256_ = v___y_2294_;
v___y_2257_ = v___y_2286_;
v___y_2258_ = v___y_2295_;
v___y_2259_ = v___y_2285_;
v___y_2260_ = v___x_2302_;
v___y_2261_ = v___y_2296_;
v___y_2262_ = v___y_2297_;
v___y_2263_ = v___y_2288_;
v___y_2264_ = v___y_2284_;
v___y_2265_ = v___y_2287_;
v___y_2266_ = v___y_2290_;
v___y_2267_ = v___y_2299_;
v___y_2268_ = v___y_2298_;
v___y_2269_ = v___y_2289_;
v___y_2270_ = v___f_2305_;
v___y_2271_ = v___y_2293_;
v___y_2272_ = v___y_2291_;
v_reportedCmdState_2273_ = v___x_2302_;
goto v___jp_2248_;
}
}
}
v___jp_2333_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2339_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2131_);
v___x_2340_ = l_IO_CancelToken_new();
v___x_2341_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2132_);
v___x_2342_ = l_Lean_Name_str___override(v___x_2132_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2344_ = l_Lean_Name_str___override(v___x_2342_, v___x_2343_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2346_ = l_Lean_Name_str___override(v___x_2344_, v___x_2345_);
v___x_2347_ = l_Lean_Name_str___override(v___x_2346_, v___x_2343_);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = l_Lean_Name_num___override(v___x_2347_, v___x_2348_);
v___x_2350_ = l_Lean_Name_str___override(v___x_2349_, v___x_2343_);
v___x_2351_ = l_Lean_Name_str___override(v___x_2350_, v___x_2345_);
v___x_2352_ = l_Lean_Name_str___override(v___x_2351_, v___x_2343_);
v___x_2353_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2354_ = l_Lean_Name_str___override(v___x_2352_, v___x_2353_);
v___x_2355_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2356_ = l_Lean_Name_str___override(v___x_2354_, v___x_2355_);
v___x_2357_ = l_Lean_Name_toString(v___x_2356_, v___x_2133_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_unsigned_to_nat(32u);
v___x_2360_ = lean_mk_empty_array_with_capacity(v___x_2359_);
lean_dec_ref(v___x_2360_);
v___x_2361_ = ((size_t)5ULL);
v___x_2362_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2357_, 2);
v___x_2363_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2357_);
lean_ctor_set(v___x_2363_, 1, v___x_2339_);
lean_ctor_set(v___x_2363_, 2, v___x_2358_);
lean_ctor_set(v___x_2363_, 3, v___x_2362_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*4, v_val_2129_);
v___x_2364_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2365_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2365_, 0, v___x_2357_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
lean_ctor_set(v___x_2365_, 2, v___x_2358_);
lean_ctor_set(v___x_2365_, 3, v___x_2362_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*4, v_val_2129_);
lean_inc(v___y_2337_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___y_2337_);
v___x_2367_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2366_);
lean_inc_ref(v___x_2340_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2340_);
v___x_2369_ = l_IO_Promise_result_x21___redArg(v___x_2146_);
lean_inc_ref(v___x_2369_);
lean_inc(v___x_2367_);
lean_inc_ref_n(v___x_2366_, 3);
v___x_2370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2366_);
lean_ctor_set(v___x_2370_, 1, v___x_2367_);
lean_ctor_set(v___x_2370_, 2, v___x_2368_);
lean_ctor_set(v___x_2370_, 3, v___x_2369_);
v___x_2371_ = l_IO_Promise_result_x21___redArg(v___x_2147_);
lean_inc_ref(v___x_2371_);
lean_inc_n(v___y_2334_, 3);
v___x_2372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2366_);
lean_ctor_set(v___x_2372_, 1, v___y_2334_);
lean_ctor_set(v___x_2372_, 2, v___x_2358_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
v___x_2373_ = l_IO_Promise_result_x21___redArg(v___x_2148_);
lean_inc_ref(v___x_2373_);
v___x_2374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2366_);
lean_ctor_set(v___x_2374_, 1, v___y_2334_);
lean_ctor_set(v___x_2374_, 2, v___x_2358_);
lean_ctor_set(v___x_2374_, 3, v___x_2373_);
v___x_2375_ = l_IO_Promise_result_x21___redArg(v___x_2149_);
v___x_2376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2358_);
lean_ctor_set(v___x_2376_, 1, v___y_2334_);
lean_ctor_set(v___x_2376_, 2, v___x_2358_);
lean_ctor_set(v___x_2376_, 3, v___x_2375_);
lean_inc_ref(v___x_2365_);
v___x_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2365_);
lean_ctor_set(v___x_2377_, 1, v___x_2370_);
lean_ctor_set(v___x_2377_, 2, v___x_2372_);
lean_ctor_set(v___x_2377_, 3, v___x_2374_);
lean_ctor_set(v___x_2377_, 4, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2363_);
lean_ctor_set(v___x_2378_, 1, v___y_2337_);
lean_ctor_set(v___x_2378_, 2, v___y_2336_);
lean_ctor_set(v___x_2378_, 3, v___x_2377_);
lean_ctor_set(v___x_2378_, 4, v___y_2338_);
v___x_2379_ = lean_io_promise_resolve(v___x_2378_, v_prom_2142_);
if (lean_obj_tag(v_old_x3f_2143_) == 0)
{
v___y_2283_ = v___x_2361_;
v___y_2284_ = v___x_2366_;
v___y_2285_ = v___x_2365_;
v___y_2286_ = v___x_2369_;
v___y_2287_ = v___x_2367_;
v___y_2288_ = v___x_2348_;
v___y_2289_ = v___x_2357_;
v___y_2290_ = v___x_2358_;
v___y_2291_ = v___x_2358_;
v___y_2292_ = v___x_2362_;
v___y_2293_ = v___x_2340_;
v___y_2294_ = v___x_2359_;
v___y_2295_ = v___y_2335_;
v___y_2296_ = v___x_2358_;
v___y_2297_ = v___x_2373_;
v___y_2298_ = v___y_2334_;
v___y_2299_ = v___x_2371_;
v___y_2300_ = v___x_2358_;
goto v___jp_2282_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2391_; 
v_val_2380_ = lean_ctor_get(v_old_x3f_2143_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_old_x3f_2143_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2382_ = v_old_x3f_2143_;
v_isShared_2383_ = v_isSharedCheck_2391_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v_old_x3f_2143_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2391_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_elabSnap_2384_; lean_object* v_stx_2385_; lean_object* v_elabSnap_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v_elabSnap_2384_ = lean_ctor_get(v_val_2380_, 3);
lean_inc_ref(v_elabSnap_2384_);
v_stx_2385_ = lean_ctor_get(v_val_2380_, 1);
lean_inc(v_stx_2385_);
lean_dec(v_val_2380_);
v_elabSnap_2386_ = lean_ctor_get(v_elabSnap_2384_, 1);
lean_inc_ref(v_elabSnap_2386_);
lean_dec_ref(v_elabSnap_2384_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_stx_2385_);
lean_ctor_set(v___x_2387_, 1, v_elabSnap_2386_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2387_);
v___x_2389_ = v___x_2382_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
v___y_2283_ = v___x_2361_;
v___y_2284_ = v___x_2366_;
v___y_2285_ = v___x_2365_;
v___y_2286_ = v___x_2369_;
v___y_2287_ = v___x_2367_;
v___y_2288_ = v___x_2348_;
v___y_2289_ = v___x_2357_;
v___y_2290_ = v___x_2358_;
v___y_2291_ = v___x_2358_;
v___y_2292_ = v___x_2362_;
v___y_2293_ = v___x_2340_;
v___y_2294_ = v___x_2359_;
v___y_2295_ = v___y_2335_;
v___y_2296_ = v___x_2358_;
v___y_2297_ = v___x_2373_;
v___y_2298_ = v___y_2334_;
v___y_2299_ = v___x_2371_;
v___y_2300_ = v___x_2389_;
goto v___jp_2282_;
}
}
}
}
v___jp_2392_:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2395_);
lean_inc(v_fst_2126_);
v___x_2397_ = l_Lean_Parser_isTerminalCommand(v_fst_2126_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v_toProcessingContext_2399_; lean_object* v_pos_2400_; lean_object* v_endPos_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2398_ = lean_io_promise_new();
v_toProcessingContext_2399_ = lean_ctor_get(v_a_2130_, 0);
v_pos_2400_ = lean_ctor_get(v_fst_2128_, 0);
v_endPos_2401_ = lean_ctor_get(v_toProcessingContext_2399_, 3);
lean_inc(v___x_2398_);
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2398_);
v___x_2403_ = lean_box(0);
lean_inc(v_endPos_2401_);
lean_inc(v_pos_2400_);
v___x_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2404_, 0, v_pos_2400_);
lean_ctor_set(v___x_2404_, 1, v_endPos_2401_);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v_parseCancelTk_2144_);
v___x_2407_ = l_IO_Promise_result_x21___redArg(v___x_2398_);
lean_dec(v___x_2398_);
v___x_2408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2403_);
lean_ctor_set(v___x_2408_, 1, v___x_2405_);
lean_ctor_set(v___x_2408_, 2, v___x_2406_);
lean_ctor_set(v___x_2408_, 3, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
v___y_2334_ = v___x_2396_;
v___y_2335_ = v___x_2402_;
v___y_2336_ = v___y_2393_;
v___y_2337_ = v___y_2394_;
v___y_2338_ = v___x_2409_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2410_; 
lean_dec_ref(v_parseCancelTk_2144_);
v___x_2410_ = lean_box(0);
v___y_2334_ = v___x_2396_;
v___y_2335_ = v___x_2410_;
v___y_2336_ = v___y_2393_;
v___y_2337_ = v___y_2394_;
v___y_2338_ = v___x_2410_;
goto v___jp_2333_;
}
}
v___jp_2411_:
{
lean_object* v___x_2414_; 
lean_inc(v_fst_2126_);
v___x_2414_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2126_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_box(0);
v___y_2393_ = v_snd_2413_;
v___y_2394_ = v_fst_2412_;
v___y_2395_ = v___x_2415_;
goto v___jp_2392_;
}
else
{
lean_object* v_val_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_val_2416_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v___x_2414_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_val_2416_);
lean_dec(v___x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
lean_inc(v_val_2416_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v_val_2416_);
lean_ctor_set(v___x_2420_, 1, v_val_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
v___y_2393_ = v_snd_2413_;
v___y_2394_ = v_fst_2412_;
v___y_2395_ = v___x_2422_;
goto v___jp_2392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2429_ = _args[0];
lean_object* v_revCmds_2430_ = _args[1];
lean_object* v_fst_2431_ = _args[2];
lean_object* v_val_2432_ = _args[3];
lean_object* v_a_2433_ = _args[4];
lean_object* v_snd_2434_ = _args[5];
lean_object* v___x_2435_ = _args[6];
lean_object* v___x_2436_ = _args[7];
lean_object* v___x_2437_ = _args[8];
lean_object* v___f_2438_ = _args[9];
lean_object* v___f_2439_ = _args[10];
lean_object* v___f_2440_ = _args[11];
lean_object* v_pos_2441_ = _args[12];
lean_object* v_cmdState_2442_ = _args[13];
lean_object* v___x_2443_ = _args[14];
lean_object* v_opts_2444_ = _args[15];
lean_object* v_prom_2445_ = _args[16];
lean_object* v_old_x3f_2446_ = _args[17];
lean_object* v_parseCancelTk_2447_ = _args[18];
lean_object* v___y_2448_ = _args[19];
_start:
{
uint8_t v_val_37622__boxed_2449_; uint8_t v___x_37625__boxed_2450_; lean_object* v_res_2451_; 
v_val_37622__boxed_2449_ = lean_unbox(v_val_2432_);
v___x_37625__boxed_2450_ = lean_unbox(v___x_2436_);
v_res_2451_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2429_, v_revCmds_2430_, v_fst_2431_, v_val_37622__boxed_2449_, v_a_2433_, v_snd_2434_, v___x_2435_, v___x_37625__boxed_2450_, v___x_2437_, v___f_2438_, v___f_2439_, v___f_2440_, v_pos_2441_, v_cmdState_2442_, v___x_2443_, v_opts_2444_, v_prom_2445_, v_old_x3f_2446_, v_parseCancelTk_2447_);
lean_dec(v_prom_2445_);
lean_dec_ref(v_opts_2444_);
lean_dec_ref(v_a_2433_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2454_, lean_object* v_parserState_2455_, lean_object* v_cmdState_2456_, lean_object* v_prom_2457_, uint8_t v_sync_2458_, lean_object* v_parseCancelTk_2459_, lean_object* v_revCmds_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v___y_2466_; lean_object* v_toSnapshot_2468_; lean_object* v_stx_2469_; lean_object* v_parserState_2470_; lean_object* v_elabSnap_2471_; lean_object* v_val_2472_; lean_object* v_newParserState_2473_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___y_2510_; uint8_t v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; uint8_t v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v_fst_2549_; lean_object* v_snd_2550_; uint8_t v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___x_2645_; 
v___f_2504_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2505_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2506_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2507_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2508_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2645_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2454_) == 1)
{
lean_object* v_val_2678_; lean_object* v_nextCmdSnap_x3f_2679_; 
v_val_2678_ = lean_ctor_get(v_old_x3f_2454_, 0);
v_nextCmdSnap_x3f_2679_ = lean_ctor_get(v_val_2678_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2679_) == 0)
{
goto v___jp_2646_;
}
else
{
lean_object* v_toSnapshot_2680_; lean_object* v_stx_2681_; lean_object* v_parserState_2682_; lean_object* v_elabSnap_2683_; lean_object* v_val_2684_; lean_object* v___x_2685_; 
v_toSnapshot_2680_ = lean_ctor_get(v_val_2678_, 0);
v_stx_2681_ = lean_ctor_get(v_val_2678_, 1);
v_parserState_2682_ = lean_ctor_get(v_val_2678_, 2);
v_elabSnap_2683_ = lean_ctor_get(v_val_2678_, 3);
v_val_2684_ = lean_ctor_get(v_nextCmdSnap_x3f_2679_, 0);
lean_inc(v_val_2684_);
v___x_2685_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2684_);
if (lean_obj_tag(v___x_2685_) == 1)
{
lean_object* v_val_2686_; lean_object* v_nextCmdSnap_x3f_2687_; 
v_val_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_val_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v_nextCmdSnap_x3f_2687_ = lean_ctor_get(v_val_2686_, 4);
lean_inc(v_nextCmdSnap_x3f_2687_);
lean_dec(v_val_2686_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2687_) == 0)
{
goto v___jp_2646_;
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2689_; 
v_val_2688_ = lean_ctor_get(v_nextCmdSnap_x3f_2687_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2687_, 1);
v___x_2689_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2688_);
if (lean_obj_tag(v___x_2689_) == 1)
{
lean_object* v_val_2690_; lean_object* v_parserState_2691_; lean_object* v_pos_2692_; uint8_t v___x_2693_; 
v_val_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_val_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v_parserState_2691_ = lean_ctor_get(v_val_2690_, 2);
lean_inc_ref(v_parserState_2691_);
lean_dec(v_val_2690_);
v_pos_2692_ = lean_ctor_get(v_parserState_2691_, 0);
lean_inc(v_pos_2692_);
lean_dec_ref(v_parserState_2691_);
v___x_2693_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2692_, v_a_2461_);
lean_dec(v_pos_2692_);
if (v___x_2693_ == 0)
{
goto v___jp_2646_;
}
else
{
lean_inc(v_val_2684_);
lean_inc_ref(v_elabSnap_2683_);
lean_inc_ref_n(v_parserState_2682_, 2);
lean_inc(v_stx_2681_);
lean_inc_ref(v_toSnapshot_2680_);
lean_dec_ref_known(v_old_x3f_2454_, 1);
lean_dec_ref(v_parseCancelTk_2459_);
lean_dec_ref(v_cmdState_2456_);
lean_dec_ref(v_parserState_2455_);
v_toSnapshot_2468_ = v_toSnapshot_2680_;
v_stx_2469_ = v_stx_2681_;
v_parserState_2470_ = v_parserState_2682_;
v_elabSnap_2471_ = v_elabSnap_2683_;
v_val_2472_ = v_val_2684_;
v_newParserState_2473_ = v_parserState_2682_;
goto v___jp_2467_;
}
}
else
{
lean_dec(v___x_2689_);
goto v___jp_2646_;
}
}
}
else
{
lean_dec(v___x_2685_);
goto v___jp_2646_;
}
}
}
else
{
goto v___jp_2646_;
}
v___jp_2463_:
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_box(0);
return v___x_2464_;
}
v___jp_2465_:
{
goto v___jp_2463_;
}
v___jp_2467_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_resultSnap_2476_; lean_object* v_task_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2500_; 
v___x_2474_ = lean_io_promise_new();
v___x_2475_ = l_IO_CancelToken_new();
v_resultSnap_2476_ = lean_ctor_get(v_elabSnap_2471_, 2);
lean_inc_ref(v_resultSnap_2476_);
v_task_2477_ = lean_ctor_get(v_resultSnap_2476_, 3);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_resultSnap_2476_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; lean_object* v_unused_2502_; lean_object* v_unused_2503_; 
v_unused_2501_ = lean_ctor_get(v_resultSnap_2476_, 2);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_resultSnap_2476_, 1);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_resultSnap_2476_, 0);
lean_dec(v_unused_2503_);
v___x_2479_ = v_resultSnap_2476_;
v_isShared_2480_ = v_isSharedCheck_2500_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_task_2477_);
lean_dec(v_resultSnap_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2500_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v_toProcessingContext_2486_; lean_object* v_pos_2487_; lean_object* v_endPos_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2481_ = lean_box(v_sync_2458_);
lean_inc_ref(v_a_2461_);
lean_inc_ref(v___x_2475_);
lean_inc(v___x_2474_);
lean_inc_ref(v_newParserState_2473_);
lean_inc(v_stx_2469_);
v___f_2482_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2482_, 0, v_val_2472_);
lean_closure_set(v___f_2482_, 1, v_stx_2469_);
lean_closure_set(v___f_2482_, 2, v_revCmds_2460_);
lean_closure_set(v___f_2482_, 3, v_newParserState_2473_);
lean_closure_set(v___f_2482_, 4, v___x_2474_);
lean_closure_set(v___f_2482_, 5, v___x_2481_);
lean_closure_set(v___f_2482_, 6, v___x_2475_);
lean_closure_set(v___f_2482_, 7, v_a_2461_);
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = 1;
v___x_2485_ = l_BaseIO_chainTask___redArg(v_task_2477_, v___f_2482_, v___x_2483_, v___x_2484_);
v_toProcessingContext_2486_ = lean_ctor_get(v_a_2461_, 0);
v_pos_2487_ = lean_ctor_get(v_newParserState_2473_, 0);
lean_inc(v_pos_2487_);
lean_dec_ref(v_newParserState_2473_);
v_endPos_2488_ = lean_ctor_get(v_toProcessingContext_2486_, 3);
v___x_2489_ = lean_box(0);
lean_inc(v_endPos_2488_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_pos_2487_);
lean_ctor_set(v___x_2490_, 1, v_endPos_2488_);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2475_);
v___x_2493_ = l_IO_Promise_result_x21___redArg(v___x_2474_);
lean_dec(v___x_2474_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 3, v___x_2493_);
lean_ctor_set(v___x_2479_, 2, v___x_2492_);
lean_ctor_set(v___x_2479_, 1, v___x_2491_);
lean_ctor_set(v___x_2479_, 0, v___x_2489_);
v___x_2495_ = v___x_2479_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2497_, 0, v_toSnapshot_2468_);
lean_ctor_set(v___x_2497_, 1, v_stx_2469_);
lean_ctor_set(v___x_2497_, 2, v_parserState_2470_);
lean_ctor_set(v___x_2497_, 3, v_elabSnap_2471_);
lean_ctor_set(v___x_2497_, 4, v___x_2496_);
v___x_2498_ = lean_io_promise_resolve(v___x_2497_, v_prom_2457_);
lean_dec(v_prom_2457_);
return v___x_2498_;
}
}
}
v___jp_2509_:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2526_);
v___x_2528_ = l_Lean_Parser_isTerminalCommand(v___y_2525_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_io_promise_new();
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
v___x_2531_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2527_, v___y_2514_, v___y_2520_, v_revCmds_2460_, v___y_2516_, v___y_2510_, v_a_2461_, v___y_2518_, v___y_2515_, v___y_2511_, v___y_2523_, v___y_2521_, v___y_2522_, v___x_2507_, v___f_2506_, v___f_2505_, v___f_2504_, v___y_2524_, v_cmdState_2456_, v___y_2512_, v___x_2508_, v___y_2513_, v___y_2517_, v___y_2519_, v_prom_2457_, v_old_x3f_2454_, v_parseCancelTk_2459_, v___x_2530_);
lean_dec(v_prom_2457_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2522_);
lean_dec(v___y_2514_);
v___y_2466_ = v___x_2531_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_box(0);
v___x_2533_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2527_, v___y_2514_, v___y_2520_, v_revCmds_2460_, v___y_2516_, v___y_2510_, v_a_2461_, v___y_2518_, v___y_2515_, v___y_2511_, v___y_2523_, v___y_2521_, v___y_2522_, v___x_2507_, v___f_2506_, v___f_2505_, v___f_2504_, v___y_2524_, v_cmdState_2456_, v___y_2512_, v___x_2508_, v___y_2513_, v___y_2517_, v___y_2519_, v_prom_2457_, v_old_x3f_2454_, v_parseCancelTk_2459_, v___x_2532_);
lean_dec(v_prom_2457_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2522_);
lean_dec(v___y_2514_);
v___y_2466_ = v___x_2533_;
goto v___jp_2465_;
}
}
v___jp_2534_:
{
lean_object* v___x_2551_; 
lean_inc(v___y_2548_);
v___x_2551_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2548_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_box(0);
v___y_2510_ = v___y_2535_;
v___y_2511_ = v___y_2536_;
v___y_2512_ = v___y_2537_;
v___y_2513_ = v___y_2538_;
v___y_2514_ = v___y_2539_;
v___y_2515_ = v___y_2540_;
v___y_2516_ = v___y_2541_;
v___y_2517_ = v___y_2542_;
v___y_2518_ = v___y_2543_;
v___y_2519_ = v_snd_2550_;
v___y_2520_ = v___y_2544_;
v___y_2521_ = v___y_2545_;
v___y_2522_ = v___y_2546_;
v___y_2523_ = v_fst_2549_;
v___y_2524_ = v___y_2547_;
v___y_2525_ = v___y_2548_;
v___y_2526_ = v___x_2552_;
goto v___jp_2509_;
}
else
{
lean_object* v_val_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2561_; 
v_val_2553_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2555_ = v___x_2551_;
v_isShared_2556_ = v_isSharedCheck_2561_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_val_2553_);
lean_dec(v___x_2551_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2561_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_inc(v_val_2553_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_val_2553_);
lean_ctor_set(v___x_2557_, 1, v_val_2553_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2557_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
v___y_2510_ = v___y_2535_;
v___y_2511_ = v___y_2536_;
v___y_2512_ = v___y_2537_;
v___y_2513_ = v___y_2538_;
v___y_2514_ = v___y_2539_;
v___y_2515_ = v___y_2540_;
v___y_2516_ = v___y_2541_;
v___y_2517_ = v___y_2542_;
v___y_2518_ = v___y_2543_;
v___y_2519_ = v_snd_2550_;
v___y_2520_ = v___y_2544_;
v___y_2521_ = v___y_2545_;
v___y_2522_ = v___y_2546_;
v___y_2523_ = v_fst_2549_;
v___y_2524_ = v___y_2547_;
v___y_2525_ = v___y_2548_;
v___y_2526_ = v___x_2559_;
goto v___jp_2509_;
}
}
}
}
v___jp_2562_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2567_ = l_Lean_Name_str___override(v___y_2564_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2569_ = l_Lean_Name_str___override(v___x_2567_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2571_ = l_Lean_Name_str___override(v___x_2569_, v___x_2570_);
v___x_2572_ = l_Lean_Name_str___override(v___x_2571_, v___x_2568_);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = l_Lean_Name_num___override(v___x_2572_, v___x_2573_);
v___x_2575_ = l_Lean_Name_str___override(v___x_2574_, v___x_2568_);
v___x_2576_ = l_Lean_Name_str___override(v___x_2575_, v___x_2570_);
v___x_2577_ = l_Lean_Name_str___override(v___x_2576_, v___x_2568_);
v___x_2578_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2579_ = l_Lean_Name_str___override(v___x_2577_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2581_ = l_Lean_Name_str___override(v___x_2579_, v___x_2580_);
v___x_2582_ = l_Lean_Name_toString(v___x_2581_, v___y_2563_);
v___x_2583_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2586_ = 0;
v___x_2587_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2587_, 0, v___x_2582_);
lean_ctor_set(v___x_2587_, 1, v___x_2583_);
lean_ctor_set(v___x_2587_, 2, v___x_2584_);
lean_ctor_set(v___x_2587_, 3, v___x_2585_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*4, v___x_2586_);
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2590_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2587_, 3);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v_cmdState_2456_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
v___x_2592_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2584_, v___x_2591_);
v___x_2593_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2584_, v___x_2587_);
v___x_2594_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2587_);
lean_ctor_set(v___x_2595_, 1, v___x_2589_);
lean_ctor_set(v___x_2595_, 2, v___x_2592_);
lean_ctor_set(v___x_2595_, 3, v___x_2593_);
lean_ctor_set(v___x_2595_, 4, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2587_);
lean_ctor_set(v___x_2596_, 1, v___x_2588_);
lean_ctor_set(v___x_2596_, 2, v___y_2565_);
lean_ctor_set(v___x_2596_, 3, v___x_2595_);
lean_ctor_set(v___x_2596_, 4, v___x_2584_);
v___x_2597_ = lean_io_promise_resolve(v___x_2596_, v_prom_2457_);
lean_dec(v_prom_2457_);
v___x_2598_ = lean_box(0);
return v___x_2598_;
}
v___jp_2599_:
{
v___y_2563_ = v___y_2600_;
v___y_2564_ = v___y_2601_;
v___y_2565_ = v___y_2602_;
goto v___jp_2562_;
}
v___jp_2604_:
{
uint8_t v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = l_IO_CancelToken_isSet(v_parseCancelTk_2459_);
v___x_2616_ = 1;
if (v___x_2615_ == 0)
{
lean_dec(v___y_2612_);
if (v_sync_2458_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2617_ = lean_io_promise_new();
v___x_2618_ = lean_io_promise_new();
v___x_2619_ = lean_io_promise_new();
v___x_2620_ = lean_io_promise_new();
v___x_2621_ = l_Lean_internal_cmdlineSnapshots;
v___x_2622_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2611_, v___x_2621_);
lean_dec_ref(v___y_2611_);
if (v___x_2622_ == 0)
{
lean_inc(v___y_2613_);
v___y_2535_ = v___x_2615_;
v___y_2536_ = v___x_2616_;
v___y_2537_ = v___x_2619_;
v___y_2538_ = v___y_2606_;
v___y_2539_ = v___x_2620_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2609_;
v___y_2542_ = v___x_2621_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2608_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___x_2618_;
v___y_2547_ = v___y_2610_;
v___y_2548_ = v___y_2613_;
v_fst_2549_ = v___y_2613_;
v_snd_2550_ = v___y_2614_;
goto v___jp_2534_;
}
else
{
uint8_t v___x_2623_; 
lean_inc(v___y_2613_);
v___x_2623_ = l_Lean_Parser_isTerminalCommand(v___y_2613_);
if (v___x_2623_ == 0)
{
if (v___x_2622_ == 0)
{
lean_inc(v___y_2613_);
v___y_2535_ = v___x_2615_;
v___y_2536_ = v___x_2616_;
v___y_2537_ = v___x_2619_;
v___y_2538_ = v___y_2606_;
v___y_2539_ = v___x_2620_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2609_;
v___y_2542_ = v___x_2621_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2608_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___x_2618_;
v___y_2547_ = v___y_2610_;
v___y_2548_ = v___y_2613_;
v_fst_2549_ = v___y_2613_;
v_snd_2550_ = v___y_2614_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v___y_2614_);
v___x_2624_ = lean_box(0);
v___x_2625_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2535_ = v___x_2615_;
v___y_2536_ = v___x_2616_;
v___y_2537_ = v___x_2619_;
v___y_2538_ = v___y_2606_;
v___y_2539_ = v___x_2620_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2609_;
v___y_2542_ = v___x_2621_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2608_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___x_2618_;
v___y_2547_ = v___y_2610_;
v___y_2548_ = v___y_2613_;
v_fst_2549_ = v___x_2624_;
v_snd_2550_ = v___x_2625_;
goto v___jp_2534_;
}
}
else
{
lean_inc(v___y_2613_);
v___y_2535_ = v___x_2615_;
v___y_2536_ = v___x_2616_;
v___y_2537_ = v___x_2619_;
v___y_2538_ = v___y_2606_;
v___y_2539_ = v___x_2620_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2609_;
v___y_2542_ = v___x_2621_;
v___y_2543_ = v___y_2605_;
v___y_2544_ = v___y_2608_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___x_2618_;
v___y_2547_ = v___y_2610_;
v___y_2548_ = v___y_2613_;
v_fst_2549_ = v___y_2613_;
v_snd_2550_ = v___y_2614_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2611_);
v___x_2626_ = lean_box(v___x_2615_);
v___x_2627_ = lean_box(v___x_2616_);
lean_inc_ref(v_a_2461_);
v___f_2628_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2628_, 0, v___y_2608_);
lean_closure_set(v___f_2628_, 1, v_revCmds_2460_);
lean_closure_set(v___f_2628_, 2, v___y_2609_);
lean_closure_set(v___f_2628_, 3, v___x_2626_);
lean_closure_set(v___f_2628_, 4, v_a_2461_);
lean_closure_set(v___f_2628_, 5, v___y_2605_);
lean_closure_set(v___f_2628_, 6, v___y_2607_);
lean_closure_set(v___f_2628_, 7, v___x_2627_);
lean_closure_set(v___f_2628_, 8, v___x_2507_);
lean_closure_set(v___f_2628_, 9, v___f_2506_);
lean_closure_set(v___f_2628_, 10, v___f_2505_);
lean_closure_set(v___f_2628_, 11, v___f_2504_);
lean_closure_set(v___f_2628_, 12, v___y_2610_);
lean_closure_set(v___f_2628_, 13, v_cmdState_2456_);
lean_closure_set(v___f_2628_, 14, v___x_2508_);
lean_closure_set(v___f_2628_, 15, v___y_2606_);
lean_closure_set(v___f_2628_, 16, v_prom_2457_);
lean_closure_set(v___f_2628_, 17, v_old_x3f_2454_);
lean_closure_set(v___f_2628_, 18, v_parseCancelTk_2459_);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_io_as_task(v___f_2628_, v___x_2629_);
lean_dec_ref(v___x_2630_);
goto v___jp_2463_;
}
}
else
{
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v_revCmds_2460_);
lean_dec_ref(v_parseCancelTk_2459_);
if (lean_obj_tag(v_old_x3f_2454_) == 1)
{
lean_object* v_val_2631_; lean_object* v___x_2632_; lean_object* v_children_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_val_2631_ = lean_ctor_get(v_old_x3f_2454_, 0);
lean_inc(v_val_2631_);
lean_dec_ref_known(v_old_x3f_2454_, 1);
v___x_2632_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2631_);
v_children_2633_ = lean_ctor_get(v___x_2632_, 1);
lean_inc_ref(v_children_2633_);
lean_dec_ref(v___x_2632_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_array_get_size(v_children_2633_);
v___x_2636_ = lean_nat_dec_lt(v___x_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_dec_ref(v_children_2633_);
v___y_2563_ = v___x_2616_;
v___y_2564_ = v___y_2612_;
v___y_2565_ = v___y_2614_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_nat_dec_le(v___x_2635_, v___x_2635_);
if (v___x_2638_ == 0)
{
if (v___x_2636_ == 0)
{
lean_dec_ref(v_children_2633_);
v___y_2563_ = v___x_2616_;
v___y_2564_ = v___y_2612_;
v___y_2565_ = v___y_2614_;
goto v___jp_2562_;
}
else
{
size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = lean_usize_of_nat(v___x_2635_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2633_, v___x_2639_, v___x_2640_, v___x_2637_);
lean_dec_ref(v_children_2633_);
v___y_2600_ = v___x_2616_;
v___y_2601_ = v___y_2612_;
v___y_2602_ = v___y_2614_;
v___y_2603_ = v___x_2641_;
goto v___jp_2599_;
}
}
else
{
size_t v___x_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = lean_usize_of_nat(v___x_2635_);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2633_, v___x_2642_, v___x_2643_, v___x_2637_);
lean_dec_ref(v_children_2633_);
v___y_2600_ = v___x_2616_;
v___y_2601_ = v___y_2612_;
v___y_2602_ = v___y_2614_;
v___y_2603_ = v___x_2644_;
goto v___jp_2599_;
}
}
}
else
{
lean_dec(v_old_x3f_2454_);
v___y_2563_ = v___x_2616_;
v___y_2564_ = v___y_2612_;
v___y_2565_ = v___y_2614_;
goto v___jp_2562_;
}
}
}
v___jp_2646_:
{
lean_object* v_env_2647_; lean_object* v_scopes_2648_; lean_object* v___x_2649_; lean_object* v_opts_2650_; lean_object* v_currNamespace_2651_; lean_object* v_openDecls_2652_; lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v_snd_2658_; 
v_env_2647_ = lean_ctor_get(v_cmdState_2456_, 0);
v_scopes_2648_ = lean_ctor_get(v_cmdState_2456_, 2);
v___x_2649_ = l_List_head_x21___redArg(v___x_2507_, v_scopes_2648_);
v_opts_2650_ = lean_ctor_get(v___x_2649_, 1);
lean_inc_ref_n(v_opts_2650_, 2);
v_currNamespace_2651_ = lean_ctor_get(v___x_2649_, 2);
lean_inc(v_currNamespace_2651_);
v_openDecls_2652_ = lean_ctor_get(v___x_2649_, 3);
lean_inc(v_openDecls_2652_);
lean_dec(v___x_2649_);
lean_inc_ref(v_env_2647_);
v___x_2653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2653_, 0, v_env_2647_);
lean_ctor_set(v___x_2653_, 1, v_opts_2650_);
lean_ctor_set(v___x_2653_, 2, v_currNamespace_2651_);
lean_ctor_set(v___x_2653_, 3, v_openDecls_2652_);
lean_inc_ref(v_parserState_2455_);
lean_inc_ref(v_a_2461_);
v___f_2654_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2654_, 0, v_a_2461_);
lean_closure_set(v___f_2654_, 1, v___x_2653_);
lean_closure_set(v___f_2654_, 2, v_parserState_2455_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_profileit(v___x_2655_, v_opts_2650_, v___f_2654_, v___x_2656_);
v_snd_2658_ = lean_ctor_get(v___x_2657_, 1);
lean_inc(v_snd_2658_);
if (lean_obj_tag(v_old_x3f_2454_) == 1)
{
lean_object* v_val_2659_; lean_object* v_fst_2660_; lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v_pos_2663_; lean_object* v_toSnapshot_2664_; lean_object* v_stx_2665_; lean_object* v_parserState_2666_; lean_object* v_elabSnap_2667_; lean_object* v_nextCmdSnap_x3f_2668_; uint8_t v___x_2669_; 
v_val_2659_ = lean_ctor_get(v_old_x3f_2454_, 0);
v_fst_2660_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_fst_2660_, 2);
lean_dec(v___x_2657_);
v_fst_2661_ = lean_ctor_get(v_snd_2658_, 0);
lean_inc(v_fst_2661_);
v_snd_2662_ = lean_ctor_get(v_snd_2658_, 1);
lean_inc(v_snd_2662_);
lean_dec(v_snd_2658_);
v_pos_2663_ = lean_ctor_get(v_parserState_2455_, 0);
lean_inc(v_pos_2663_);
lean_dec_ref(v_parserState_2455_);
v_toSnapshot_2664_ = lean_ctor_get(v_val_2659_, 0);
v_stx_2665_ = lean_ctor_get(v_val_2659_, 1);
v_parserState_2666_ = lean_ctor_get(v_val_2659_, 2);
v_elabSnap_2667_ = lean_ctor_get(v_val_2659_, 3);
v_nextCmdSnap_x3f_2668_ = lean_ctor_get(v_val_2659_, 4);
lean_inc(v_stx_2665_);
v___x_2669_ = l_Lean_Syntax_eqWithInfo(v_fst_2660_, v_stx_2665_);
if (v___x_2669_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2668_) == 0)
{
lean_inc(v_fst_2661_);
lean_inc(v_fst_2660_);
lean_inc_ref(v_opts_2650_);
v___y_2605_ = v_snd_2662_;
v___y_2606_ = v_opts_2650_;
v___y_2607_ = v___x_2656_;
v___y_2608_ = v_fst_2660_;
v___y_2609_ = v_fst_2661_;
v___y_2610_ = v_pos_2663_;
v___y_2611_ = v_opts_2650_;
v___y_2612_ = v___x_2656_;
v___y_2613_ = v_fst_2660_;
v___y_2614_ = v_fst_2661_;
goto v___jp_2604_;
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2671_; 
v_val_2670_ = lean_ctor_get(v_nextCmdSnap_x3f_2668_, 0);
lean_inc(v_val_2670_);
v___x_2671_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2645_, v_val_2670_);
lean_inc(v_fst_2661_);
lean_inc(v_fst_2660_);
lean_inc_ref(v_opts_2650_);
v___y_2605_ = v_snd_2662_;
v___y_2606_ = v_opts_2650_;
v___y_2607_ = v___x_2656_;
v___y_2608_ = v_fst_2660_;
v___y_2609_ = v_fst_2661_;
v___y_2610_ = v_pos_2663_;
v___y_2611_ = v_opts_2650_;
v___y_2612_ = v___x_2656_;
v___y_2613_ = v_fst_2660_;
v___y_2614_ = v_fst_2661_;
goto v___jp_2604_;
}
}
else
{
lean_inc(v_val_2659_);
lean_dec(v_pos_2663_);
lean_dec(v_snd_2662_);
lean_dec(v_fst_2660_);
lean_dec_ref_known(v_old_x3f_2454_, 1);
lean_dec_ref(v_opts_2650_);
lean_dec_ref(v_parseCancelTk_2459_);
lean_dec_ref(v_cmdState_2456_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2668_) == 1)
{
lean_object* v_val_2672_; 
lean_inc_ref(v_nextCmdSnap_x3f_2668_);
lean_inc_ref(v_elabSnap_2667_);
lean_inc_ref(v_parserState_2666_);
lean_inc(v_stx_2665_);
lean_inc_ref(v_toSnapshot_2664_);
lean_dec(v_val_2659_);
v_val_2672_ = lean_ctor_get(v_nextCmdSnap_x3f_2668_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2668_, 1);
v_toSnapshot_2468_ = v_toSnapshot_2664_;
v_stx_2469_ = v_stx_2665_;
v_parserState_2470_ = v_parserState_2666_;
v_elabSnap_2471_ = v_elabSnap_2667_;
v_val_2472_ = v_val_2672_;
v_newParserState_2473_ = v_fst_2661_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2673_; 
lean_dec(v_fst_2661_);
lean_dec(v_revCmds_2460_);
v___x_2673_ = lean_io_promise_resolve(v_val_2659_, v_prom_2457_);
lean_dec(v_prom_2457_);
return v___x_2673_;
}
}
}
else
{
lean_object* v_fst_2674_; lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v_pos_2677_; 
v_fst_2674_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_fst_2674_, 2);
lean_dec(v___x_2657_);
v_fst_2675_ = lean_ctor_get(v_snd_2658_, 0);
lean_inc_n(v_fst_2675_, 2);
v_snd_2676_ = lean_ctor_get(v_snd_2658_, 1);
lean_inc(v_snd_2676_);
lean_dec(v_snd_2658_);
v_pos_2677_ = lean_ctor_get(v_parserState_2455_, 0);
lean_inc(v_pos_2677_);
lean_dec_ref(v_parserState_2455_);
lean_inc_ref(v_opts_2650_);
v___y_2605_ = v_snd_2676_;
v___y_2606_ = v_opts_2650_;
v___y_2607_ = v___x_2656_;
v___y_2608_ = v_fst_2674_;
v___y_2609_ = v_fst_2675_;
v___y_2610_ = v_pos_2677_;
v___y_2611_ = v_opts_2650_;
v___y_2612_ = v___x_2656_;
v___y_2613_ = v_fst_2674_;
v___y_2614_ = v_fst_2675_;
goto v___jp_2604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2694_, lean_object* v_stx_2695_, lean_object* v_revCmds_2696_, lean_object* v_newParserState_2697_, lean_object* v_val_2698_, uint8_t v_sync_2699_, lean_object* v_val_2700_, lean_object* v_a_2701_, lean_object* v_oldNext_2702_){
_start:
{
lean_object* v_cmdState_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_cmdState_2704_ = lean_ctor_get(v_oldResult_2694_, 1);
lean_inc_ref(v_cmdState_2704_);
lean_dec_ref(v_oldResult_2694_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v_oldNext_2702_);
v___x_2706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_stx_2695_);
lean_ctor_set(v___x_2706_, 1, v_revCmds_2696_);
v___x_2707_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2705_, v_newParserState_2697_, v_cmdState_2704_, v_val_2698_, v_sync_2699_, v_val_2700_, v___x_2706_, v_a_2701_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2708_ = _args[0];
lean_object* v_val_2709_ = _args[1];
lean_object* v_fst_2710_ = _args[2];
lean_object* v_revCmds_2711_ = _args[3];
lean_object* v_fst_2712_ = _args[4];
lean_object* v_val_2713_ = _args[5];
lean_object* v_a_2714_ = _args[6];
lean_object* v_snd_2715_ = _args[7];
lean_object* v___x_2716_ = _args[8];
lean_object* v___x_2717_ = _args[9];
lean_object* v_fst_2718_ = _args[10];
lean_object* v_val_2719_ = _args[11];
lean_object* v_val_2720_ = _args[12];
lean_object* v___x_2721_ = _args[13];
lean_object* v___f_2722_ = _args[14];
lean_object* v___f_2723_ = _args[15];
lean_object* v___f_2724_ = _args[16];
lean_object* v_pos_2725_ = _args[17];
lean_object* v_cmdState_2726_ = _args[18];
lean_object* v_val_2727_ = _args[19];
lean_object* v___x_2728_ = _args[20];
lean_object* v_opts_2729_ = _args[21];
lean_object* v___x_2730_ = _args[22];
lean_object* v_snd_2731_ = _args[23];
lean_object* v_prom_2732_ = _args[24];
lean_object* v_old_x3f_2733_ = _args[25];
lean_object* v_parseCancelTk_2734_ = _args[26];
lean_object* v_next_x3f_2735_ = _args[27];
lean_object* v___y_2736_ = _args[28];
_start:
{
uint8_t v_val_37412__boxed_2737_; uint8_t v___x_37415__boxed_2738_; lean_object* v_res_2739_; 
v_val_37412__boxed_2737_ = lean_unbox(v_val_2713_);
v___x_37415__boxed_2738_ = lean_unbox(v___x_2717_);
v_res_2739_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2708_, v_val_2709_, v_fst_2710_, v_revCmds_2711_, v_fst_2712_, v_val_37412__boxed_2737_, v_a_2714_, v_snd_2715_, v___x_2716_, v___x_37415__boxed_2738_, v_fst_2718_, v_val_2719_, v_val_2720_, v___x_2721_, v___f_2722_, v___f_2723_, v___f_2724_, v_pos_2725_, v_cmdState_2726_, v_val_2727_, v___x_2728_, v_opts_2729_, v___x_2730_, v_snd_2731_, v_prom_2732_, v_old_x3f_2733_, v_parseCancelTk_2734_, v_next_x3f_2735_);
lean_dec(v_prom_2732_);
lean_dec_ref(v___x_2730_);
lean_dec_ref(v_opts_2729_);
lean_dec(v_val_2720_);
lean_dec_ref(v_a_2714_);
lean_dec(v_val_2709_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2740_, lean_object* v_parserState_2741_, lean_object* v_cmdState_2742_, lean_object* v_prom_2743_, lean_object* v_sync_2744_, lean_object* v_parseCancelTk_2745_, lean_object* v_revCmds_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
uint8_t v_sync_boxed_2749_; lean_object* v_res_2750_; 
v_sync_boxed_2749_ = lean_unbox(v_sync_2744_);
v_res_2750_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2740_, v_parserState_2741_, v_cmdState_2742_, v_prom_2743_, v_sync_boxed_2749_, v_parseCancelTk_2745_, v_revCmds_2746_, v_a_2747_);
lean_dec_ref(v_a_2747_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2751_, size_t v_i_2752_, size_t v_stop_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2751_, v_i_2752_, v_stop_2753_, v_b_2754_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2758_, lean_object* v_i_2759_, lean_object* v_stop_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
size_t v_i_boxed_2764_; size_t v_stop_boxed_2765_; lean_object* v_res_2766_; 
v_i_boxed_2764_ = lean_unbox_usize(v_i_2759_);
lean_dec(v_i_2759_);
v_stop_boxed_2765_ = lean_unbox_usize(v_stop_2760_);
lean_dec(v_stop_2760_);
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2758_, v_i_boxed_2764_, v_stop_boxed_2765_, v_b_2761_, v___y_2762_);
lean_dec_ref(v___y_2762_);
lean_dec_ref(v_as_2758_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2767_, lean_object* v_opt_2768_){
_start:
{
lean_object* v_name_2769_; lean_object* v_map_2770_; lean_object* v___x_2771_; 
v_name_2769_ = lean_ctor_get(v_opt_2768_, 0);
v_map_2770_ = lean_ctor_get(v_opts_2767_, 0);
v___x_2771_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2770_, v_name_2769_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_box(0);
return v___x_2772_;
}
else
{
lean_object* v_val_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2782_; 
v_val_2773_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2775_ = v___x_2771_;
v_isShared_2776_ = v_isSharedCheck_2782_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_val_2773_);
lean_dec(v___x_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2782_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
if (lean_obj_tag(v_val_2773_) == 0)
{
lean_object* v_v_2777_; lean_object* v___x_2779_; 
v_v_2777_ = lean_ctor_get(v_val_2773_, 0);
lean_inc_ref(v_v_2777_);
lean_dec_ref_known(v_val_2773_, 1);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v_v_2777_);
v___x_2779_ = v___x_2775_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_v_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
else
{
lean_object* v___x_2781_; 
lean_del_object(v___x_2775_);
lean_dec(v_val_2773_);
v___x_2781_ = lean_box(0);
return v___x_2781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2783_, lean_object* v_opt_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2783_, v_opt_2784_);
lean_dec_ref(v_opt_2784_);
lean_dec_ref(v_opts_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2786_, lean_object* v_x_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2786_);
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2790_, 0, v_x_2787_);
lean_ctor_set(v___x_2790_, 1, v___x_2788_);
lean_ctor_set(v___x_2790_, 2, v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2797_ = l_Lean_Array_toPArray_x27___redArg(v___x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
if (lean_obj_tag(v_a_2798_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = l_List_reverse___redArg(v_a_2799_);
return v___x_2800_;
}
else
{
lean_object* v_head_2801_; lean_object* v_tail_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2815_; 
v_head_2801_ = lean_ctor_get(v_a_2798_, 0);
v_tail_2802_ = lean_ctor_get(v_a_2798_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2804_ = v_a_2798_;
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_tail_2802_);
lean_inc(v_head_2801_);
lean_dec(v_a_2798_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2806_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v_head_2801_);
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 1, v_a_2799_);
lean_ctor_set(v___x_2804_, 0, v___x_2810_);
v___x_2812_ = v___x_2804_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_a_2799_);
v___x_2812_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
v_a_2798_ = v_tail_2802_;
v_a_2799_ = v___x_2812_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2816_; double v___x_2817_; 
v___x_2816_ = lean_unsigned_to_nat(1000000000u);
v___x_2817_ = lean_float_of_nat(v___x_2816_);
return v___x_2817_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2835_ = l_Lean_MessageData_ofFormat(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2836_, lean_object* v_stx_2837_, lean_object* v_origStx_2838_, lean_object* v_toProcessingContext_2839_, lean_object* v___x_2840_, lean_object* v_fileMap_2841_, lean_object* v_parserState_2842_, lean_object* v_a_2843_, lean_object* v___x_2844_, lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_toProcessingContext_2849_; lean_object* v___x_2850_; 
v_toProcessingContext_2849_ = lean_ctor_get(v___y_2847_, 0);
lean_inc_ref(v_toProcessingContext_2849_);
lean_inc(v_stx_2837_);
v___x_2850_ = lean_apply_3(v_setupImports_2836_, v_stx_2837_, v_toProcessingContext_2849_, lean_box(0));
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_3063_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_3063_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_3063_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
if (lean_obj_tag(v_a_2851_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; 
lean_dec_ref(v___x_2846_);
lean_dec(v___x_2844_);
lean_dec_ref(v_parserState_2842_);
lean_dec_ref(v_fileMap_2841_);
lean_dec(v___x_2840_);
lean_dec_ref(v_toProcessingContext_2839_);
lean_dec(v_origStx_2838_);
lean_dec(v_stx_2837_);
v_a_2855_ = lean_ctor_get(v_a_2851_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v_a_2851_, 1);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_a_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_3062_; 
v_a_2859_ = lean_ctor_get(v_a_2851_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_2861_ = v_a_2851_;
v_isShared_2862_ = v_isSharedCheck_3062_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v_a_2851_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_3062_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v_mainModuleName_2864_; lean_object* v_package_x3f_2865_; uint8_t v_isModule_2866_; lean_object* v_imports_2867_; lean_object* v_opts_2868_; uint32_t v_trustLevel_2869_; lean_object* v_importArts_2870_; lean_object* v_plugins_2871_; double v___x_2872_; double v___x_2873_; double v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2879_; 
v___x_2863_ = lean_io_mono_nanos_now();
v_mainModuleName_2864_ = lean_ctor_get(v_a_2859_, 0);
lean_inc(v_mainModuleName_2864_);
v_package_x3f_2865_ = lean_ctor_get(v_a_2859_, 1);
lean_inc(v_package_x3f_2865_);
v_isModule_2866_ = lean_ctor_get_uint8(v_a_2859_, sizeof(void*)*6 + 4);
v_imports_2867_ = lean_ctor_get(v_a_2859_, 2);
lean_inc_ref(v_imports_2867_);
v_opts_2868_ = lean_ctor_get(v_a_2859_, 3);
lean_inc_ref(v_opts_2868_);
v_trustLevel_2869_ = lean_ctor_get_uint32(v_a_2859_, sizeof(void*)*6);
v_importArts_2870_ = lean_ctor_get(v_a_2859_, 4);
lean_inc(v_importArts_2870_);
v_plugins_2871_ = lean_ctor_get(v_a_2859_, 5);
lean_inc_ref(v_plugins_2871_);
lean_dec(v_a_2859_);
v___x_2872_ = lean_float_of_nat(v___x_2863_);
v___x_2873_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2874_ = lean_float_div(v___x_2872_, v___x_2873_);
v___x_2875_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2837_);
v___x_2876_ = l_Lean_MessageLog_empty;
v___x_2877_ = 1;
lean_inc(v_stx_2837_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v_stx_2837_);
v___x_2879_ = v___x_2861_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_stx_2837_);
v___x_2879_ = v_reuseFailAlloc_3061_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_origStx_2838_);
lean_inc_ref(v___x_2879_);
lean_inc_ref(v_opts_2868_);
v___x_2881_ = l_Lean_Elab_processHeaderCore(v___x_2875_, v_imports_2867_, v_isModule_2866_, v_opts_2868_, v___x_2876_, v_toProcessingContext_2839_, v_trustLevel_2869_, v_plugins_2871_, v___x_2877_, v_mainModuleName_2864_, v_package_x3f_2865_, v_importArts_2870_, v___x_2879_, v___x_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_3052_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_3052_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_3052_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v_fst_2886_; lean_object* v_snd_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_3051_; 
v_fst_2886_ = lean_ctor_get(v_a_2882_, 0);
v_snd_2887_ = lean_ctor_get(v_a_2882_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_a_2882_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_2889_ = v_a_2882_;
v_isShared_2890_ = v_isSharedCheck_3051_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_snd_2887_);
lean_inc(v_fst_2886_);
lean_dec(v_a_2882_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_3051_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; double v___x_2892_; double v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v_traceState_2911_; 
v___x_2891_ = lean_io_mono_nanos_now();
v___x_2892_ = lean_float_of_nat(v___x_2891_);
v___x_2893_ = lean_float_div(v___x_2892_, v___x_2873_);
lean_inc(v_snd_2887_);
v___x_2894_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2887_);
v___x_2895_ = l_Lean_MessageLog_hasErrors(v_snd_2887_);
if (v___x_2895_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_del_object(v___x_2853_);
lean_dec_ref(v___x_2846_);
v___x_3020_ = l_Lean_trace_profiler_output;
v___x_3021_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2868_, v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = l_Lean_trace_profiler_serve;
v___x_3023_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2868_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2911_ = v___x_3024_;
goto v___jp_2910_;
}
else
{
goto v___jp_3004_;
}
}
else
{
lean_dec_ref_known(v___x_3021_, 1);
goto v___jp_3004_;
}
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint64_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; size_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_del_object(v___x_2889_);
lean_dec(v_snd_2887_);
lean_dec(v_fst_2886_);
lean_del_object(v___x_2884_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v_opts_2868_);
lean_dec(v___x_2844_);
lean_dec_ref(v_parserState_2842_);
lean_dec_ref(v_fileMap_2841_);
lean_dec(v_stx_2837_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3026_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3027_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2840_, 2);
v___x_3028_ = l_Lean_Name_num___override(v___x_3027_, v___x_2840_);
v___x_3029_ = l_Lean_Name_str___override(v___x_3028_, v___x_3025_);
v___x_3030_ = l_Lean_Name_str___override(v___x_3029_, v___x_3026_);
v___x_3031_ = l_Lean_Name_str___override(v___x_3030_, v___x_3025_);
v___x_3032_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3033_ = l_Lean_Name_str___override(v___x_3031_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3035_ = l_Lean_Name_str___override(v___x_3033_, v___x_3034_);
v___x_3036_ = l_Lean_Name_toString(v___x_3035_, v___x_2877_);
v___x_3037_ = lean_box(0);
v___x_3038_ = 0ULL;
v___x_3039_ = lean_unsigned_to_nat(32u);
v___x_3040_ = lean_mk_empty_array_with_capacity(v___x_3039_);
v___x_3041_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3042_ = ((size_t)5ULL);
v___x_3043_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set(v___x_3043_, 1, v___x_3040_);
lean_ctor_set(v___x_3043_, 2, v___x_2840_);
lean_ctor_set(v___x_3043_, 3, v___x_2840_);
lean_ctor_set_usize(v___x_3043_, 4, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set_uint64(v___x_3044_, sizeof(void*)*1, v___x_3038_);
v___x_3045_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3045_, 0, v___x_3036_);
lean_ctor_set(v___x_3045_, 1, v___x_2894_);
lean_ctor_set(v___x_3045_, 2, v___x_3037_);
lean_ctor_set(v___x_3045_, 3, v___x_3044_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*4, v___x_2895_);
v___x_3046_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2846_);
v___x_3047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
lean_ctor_set(v___x_3047_, 2, v___x_3037_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_3047_);
v___x_3049_ = v___x_2853_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
v___jp_2896_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___y_2902_);
v___x_2904_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2904_, 0, v___y_2899_);
lean_ctor_set(v___x_2904_, 1, v___x_2894_);
lean_ctor_set(v___x_2904_, 2, v___x_2903_);
lean_ctor_set(v___x_2904_, 3, v___y_2897_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*4, v___x_2895_);
v___x_2905_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2900_, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2906_, 0, v___y_2898_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
lean_ctor_set(v___x_2906_, 2, v___y_2901_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2906_);
v___x_2908_ = v___x_2884_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
v___jp_2910_:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Language_Lean_reparseOptions(v_opts_2868_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; lean_object* v_env_2915_; lean_object* v_messages_2916_; lean_object* v_scopes_2917_; lean_object* v_usedQuotCtxts_2918_; lean_object* v_nextMacroScope_2919_; lean_object* v_maxRecDepth_2920_; lean_object* v_ngen_2921_; lean_object* v_auxDeclNGen_2922_; lean_object* v_snapshotTasks_2923_; lean_object* v_prevLinterStates_2924_; lean_object* v_codeQualityEntryTasks_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2993_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
lean_inc(v_fst_2886_);
v___x_2914_ = l_Lean_Elab_Command_mkState(v_fst_2886_, v_snd_2887_, v_a_2913_);
v_env_2915_ = lean_ctor_get(v___x_2914_, 0);
v_messages_2916_ = lean_ctor_get(v___x_2914_, 1);
v_scopes_2917_ = lean_ctor_get(v___x_2914_, 2);
v_usedQuotCtxts_2918_ = lean_ctor_get(v___x_2914_, 3);
v_nextMacroScope_2919_ = lean_ctor_get(v___x_2914_, 4);
v_maxRecDepth_2920_ = lean_ctor_get(v___x_2914_, 5);
v_ngen_2921_ = lean_ctor_get(v___x_2914_, 6);
v_auxDeclNGen_2922_ = lean_ctor_get(v___x_2914_, 7);
v_snapshotTasks_2923_ = lean_ctor_get(v___x_2914_, 10);
v_prevLinterStates_2924_ = lean_ctor_get(v___x_2914_, 11);
v_codeQualityEntryTasks_2925_ = lean_ctor_get(v___x_2914_, 12);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; lean_object* v_unused_2995_; 
v_unused_2994_ = lean_ctor_get(v___x_2914_, 9);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v___x_2914_, 8);
lean_dec(v_unused_2995_);
v___x_2927_ = v___x_2914_;
v_isShared_2928_ = v_isSharedCheck_2993_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2925_);
lean_inc(v_prevLinterStates_2924_);
lean_inc(v_snapshotTasks_2923_);
lean_inc(v_auxDeclNGen_2922_);
lean_inc(v_ngen_2921_);
lean_inc(v_maxRecDepth_2920_);
lean_inc(v_nextMacroScope_2919_);
lean_inc(v_usedQuotCtxts_2918_);
lean_inc(v_scopes_2917_);
lean_inc(v_messages_2916_);
lean_inc(v_env_2915_);
lean_dec(v___x_2914_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2993_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2929_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2930_ = lean_box(0);
lean_inc_n(v___x_2840_, 4);
v___x_2931_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2840_);
lean_ctor_set(v___x_2931_, 1, v___x_2840_);
lean_ctor_set(v___x_2931_, 2, v___x_2840_);
lean_ctor_set(v___x_2931_, 3, v___x_2840_);
lean_ctor_set(v___x_2931_, 4, v___x_2929_);
lean_ctor_set(v___x_2931_, 5, v___x_2929_);
lean_ctor_set(v___x_2931_, 6, v___x_2929_);
lean_ctor_set(v___x_2931_, 7, v___x_2929_);
lean_ctor_set(v___x_2931_, 8, v___x_2929_);
lean_ctor_set(v___x_2931_, 9, v___x_2929_);
lean_ctor_set(v___x_2931_, 10, v___x_2929_);
v___x_2932_ = l_Lean_Options_empty;
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_box(0);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2937_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2937_, 0, v_fst_2886_);
lean_ctor_set(v___x_2937_, 1, v___x_2930_);
lean_ctor_set(v___x_2937_, 2, v_fileMap_2841_);
lean_ctor_set(v___x_2937_, 3, v___x_2931_);
lean_ctor_set(v___x_2937_, 4, v___x_2932_);
lean_ctor_set(v___x_2937_, 5, v___x_2933_);
lean_ctor_set(v___x_2937_, 6, v___x_2934_);
lean_ctor_set(v___x_2937_, 7, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
v___x_2939_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2837_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v_stx_2837_);
lean_ctor_set(v___x_2889_, 0, v___x_2939_);
v___x_2941_ = v___x_2889_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_stx_2837_);
v___x_2941_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
v___x_2943_ = lean_unsigned_to_nat(2u);
v___x_2944_ = l_Lean_Syntax_getArg(v_stx_2837_, v___x_2943_);
lean_dec(v_stx_2837_);
v___x_2945_ = l_Lean_Syntax_getArgs(v___x_2944_);
lean_dec(v___x_2944_);
v___x_2946_ = lean_array_to_list(v___x_2945_);
v___x_2947_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2946_, v___x_2934_);
v___x_2948_ = l_Lean_List_toPArray_x27___redArg(v___x_2947_);
v___x_2949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2942_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2938_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_mk_empty_array_with_capacity(v___x_2935_);
v___x_2952_ = lean_array_push(v___x_2951_, v___x_2950_);
v___x_2953_ = l_Lean_Array_toPArray_x27___redArg(v___x_2952_);
lean_dec_ref(v___x_2952_);
lean_inc_ref(v___x_2953_);
v___x_2954_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2954_, 0, v___x_2929_);
lean_ctor_set(v___x_2954_, 1, v___x_2929_);
lean_ctor_set(v___x_2954_, 2, v___x_2953_);
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*3, v___x_2877_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 9, v_traceState_2911_);
lean_ctor_set(v___x_2927_, 8, v___x_2954_);
v___x_2956_ = v___x_2927_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_env_2915_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_messages_2916_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_scopes_2917_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_usedQuotCtxts_2918_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_nextMacroScope_2919_);
lean_ctor_set(v_reuseFailAlloc_2991_, 5, v_maxRecDepth_2920_);
lean_ctor_set(v_reuseFailAlloc_2991_, 6, v_ngen_2921_);
lean_ctor_set(v_reuseFailAlloc_2991_, 7, v_auxDeclNGen_2922_);
lean_ctor_set(v_reuseFailAlloc_2991_, 8, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2991_, 9, v_traceState_2911_);
lean_ctor_set(v_reuseFailAlloc_2991_, 10, v_snapshotTasks_2923_);
lean_ctor_set(v_reuseFailAlloc_2991_, 11, v_prevLinterStates_2924_);
lean_ctor_set(v_reuseFailAlloc_2991_, 12, v_codeQualityEntryTasks_2925_);
v___x_2956_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; size_t v___x_2967_; lean_object* v___x_2968_; lean_object* v_size_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint64_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2957_ = lean_io_promise_new();
v___x_2958_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_2958_);
lean_inc(v___x_2957_);
lean_inc_ref(v___x_2956_);
v___x_2959_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2930_, v_parserState_2842_, v___x_2956_, v___x_2957_, v___x_2877_, v___x_2958_, v___x_2934_, v_a_2843_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2961_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2962_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2840_, 3);
v___x_2963_ = l_Lean_Name_num___override(v___x_2962_, v___x_2840_);
v___x_2964_ = lean_unsigned_to_nat(32u);
v___x_2965_ = lean_mk_empty_array_with_capacity(v___x_2964_);
v___x_2966_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2967_ = ((size_t)5ULL);
v___x_2968_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2965_);
lean_ctor_set(v___x_2968_, 2, v___x_2840_);
lean_ctor_set(v___x_2968_, 3, v___x_2840_);
lean_ctor_set_usize(v___x_2968_, 4, v___x_2967_);
v_size_2969_ = lean_ctor_get(v___x_2953_, 2);
v___x_2970_ = l_Lean_Name_str___override(v___x_2963_, v___x_2960_);
v___x_2971_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2844_);
v___x_2972_ = l_Lean_Name_str___override(v___x_2970_, v___x_2961_);
v___x_2973_ = l_Lean_Name_str___override(v___x_2972_, v___x_2960_);
v___x_2974_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2975_ = l_Lean_Name_str___override(v___x_2973_, v___x_2974_);
v___x_2976_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2977_ = l_Lean_Name_str___override(v___x_2975_, v___x_2976_);
v___x_2978_ = l_Lean_Name_toString(v___x_2977_, v___x_2877_);
v___x_2979_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2980_ = 0ULL;
v___x_2981_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2981_, 0, v___x_2968_);
lean_ctor_set_uint64(v___x_2981_, sizeof(void*)*1, v___x_2980_);
v___x_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2958_);
v___x_2983_ = l_IO_Promise_result_x21___redArg(v___x_2957_);
lean_dec(v___x_2957_);
v___x_2984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2844_);
lean_ctor_set(v___x_2984_, 1, v___x_2971_);
lean_ctor_set(v___x_2984_, 2, v___x_2982_);
lean_ctor_set(v___x_2984_, 3, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2956_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_inc_ref(v___x_2981_);
lean_inc_ref(v___x_2978_);
v___x_2987_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2987_, 0, v___x_2978_);
lean_ctor_set(v___x_2987_, 1, v___x_2979_);
lean_ctor_set(v___x_2987_, 2, v___x_2930_);
lean_ctor_set(v___x_2987_, 3, v___x_2981_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*4, v___x_2895_);
v___x_2988_ = lean_nat_dec_lt(v___x_2840_, v_size_2969_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref(v___x_2953_);
lean_dec(v___x_2840_);
v___x_2989_ = l_outOfBounds___redArg(v___x_2845_);
v___y_2897_ = v___x_2981_;
v___y_2898_ = v___x_2987_;
v___y_2899_ = v___x_2978_;
v___y_2900_ = v___x_2879_;
v___y_2901_ = v___x_2986_;
v___y_2902_ = v___x_2989_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2845_, v___x_2953_, v___x_2840_);
lean_dec(v___x_2840_);
lean_dec_ref(v___x_2953_);
v___y_2897_ = v___x_2981_;
v___y_2898_ = v___x_2987_;
v___y_2899_ = v___x_2978_;
v___y_2900_ = v___x_2879_;
v___y_2901_ = v___x_2986_;
v___y_2902_ = v___x_2990_;
goto v___jp_2896_;
}
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v_traceState_2911_);
lean_dec_ref(v___x_2894_);
lean_del_object(v___x_2889_);
lean_dec(v_snd_2887_);
lean_dec(v_fst_2886_);
lean_del_object(v___x_2884_);
lean_dec_ref(v___x_2879_);
lean_dec(v___x_2844_);
lean_dec_ref(v_parserState_2842_);
lean_dec_ref(v_fileMap_2841_);
lean_dec(v___x_2840_);
lean_dec(v_stx_2837_);
v_a_2996_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2912_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2912_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
v___jp_3004_:
{
uint64_t v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3005_ = 0ULL;
v___x_3006_ = lean_box(0);
v___x_3007_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_3008_ = lean_box(0);
v___x_3009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3010_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3010_, 0, v___x_3007_);
lean_ctor_set(v___x_3010_, 1, v___x_3008_);
lean_ctor_set(v___x_3010_, 2, v___x_3009_);
lean_ctor_set_float(v___x_3010_, sizeof(void*)*3, v___x_2874_);
lean_ctor_set_float(v___x_3010_, sizeof(void*)*3 + 8, v___x_2893_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*3 + 16, v___x_2877_);
v___x_3011_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_2840_);
v___x_3013_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3010_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3006_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(1u);
v___x_3016_ = lean_mk_empty_array_with_capacity(v___x_3015_);
v___x_3017_ = lean_array_push(v___x_3016_, v___x_3014_);
v___x_3018_ = l_Lean_Array_toPArray_x27___redArg(v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set_uint64(v___x_3019_, sizeof(void*)*1, v___x_3005_);
v_traceState_2911_ = v___x_3019_;
goto v___jp_2910_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v___x_2879_);
lean_dec_ref(v_opts_2868_);
lean_del_object(v___x_2853_);
lean_dec_ref(v___x_2846_);
lean_dec(v___x_2844_);
lean_dec_ref(v_parserState_2842_);
lean_dec_ref(v_fileMap_2841_);
lean_dec(v___x_2840_);
lean_dec(v_stx_2837_);
v_a_3053_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2881_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2881_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
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
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v___x_2846_);
lean_dec(v___x_2844_);
lean_dec_ref(v_parserState_2842_);
lean_dec_ref(v_fileMap_2841_);
lean_dec(v___x_2840_);
lean_dec_ref(v_toProcessingContext_2839_);
lean_dec(v_origStx_2838_);
lean_dec(v_stx_2837_);
v_a_3064_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2850_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2850_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3072_, lean_object* v_stx_3073_, lean_object* v_origStx_3074_, lean_object* v_toProcessingContext_3075_, lean_object* v___x_3076_, lean_object* v_fileMap_3077_, lean_object* v_parserState_3078_, lean_object* v_a_3079_, lean_object* v___x_3080_, lean_object* v___x_3081_, lean_object* v___x_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3072_, v_stx_3073_, v_origStx_3074_, v_toProcessingContext_3075_, v___x_3076_, v_fileMap_3077_, v_parserState_3078_, v_a_3079_, v___x_3080_, v___x_3081_, v___x_3082_, v___y_3083_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v___x_3081_);
lean_dec_ref(v_a_3079_);
return v_res_3085_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___f_3087_; 
v___x_3086_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3087_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3087_, 0, v___x_3086_);
return v___f_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3088_, lean_object* v_stx_3089_, lean_object* v_origStx_3090_, lean_object* v_parserState_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v_toProcessingContext_3094_; lean_object* v_fileMap_3095_; lean_object* v_endPos_3096_; lean_object* v___x_3097_; lean_object* v___f_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_toProcessingContext_3094_ = lean_ctor_get(v_a_3092_, 0);
v_fileMap_3095_ = lean_ctor_get(v_toProcessingContext_3094_, 2);
v_endPos_3096_ = lean_ctor_get(v_toProcessingContext_3094_, 3);
v___x_3097_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3098_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3099_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3092_, 2);
lean_inc_ref(v_fileMap_3095_);
lean_inc_ref(v_toProcessingContext_3094_);
v___f_3102_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3102_, 0, v_setupImports_3088_);
lean_closure_set(v___f_3102_, 1, v_stx_3089_);
lean_closure_set(v___f_3102_, 2, v_origStx_3090_);
lean_closure_set(v___f_3102_, 3, v_toProcessingContext_3094_);
lean_closure_set(v___f_3102_, 4, v___x_3101_);
lean_closure_set(v___f_3102_, 5, v_fileMap_3095_);
lean_closure_set(v___f_3102_, 6, v_parserState_3091_);
lean_closure_set(v___f_3102_, 7, v_a_3092_);
lean_closure_set(v___f_3102_, 8, v___x_3100_);
lean_closure_set(v___f_3102_, 9, v___x_3099_);
lean_closure_set(v___f_3102_, 10, v___x_3097_);
lean_inc(v_endPos_3096_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v_endPos_3096_);
v___x_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
v___x_3105_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3105_, 0, lean_box(0));
lean_closure_set(v___x_3105_, 1, v___f_3098_);
lean_closure_set(v___x_3105_, 2, v___f_3102_);
lean_closure_set(v___x_3105_, 3, v_a_3092_);
v___x_3106_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3100_, v___x_3100_, v___x_3104_, v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3107_, lean_object* v_stx_3108_, lean_object* v_origStx_3109_, lean_object* v_parserState_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3107_, v_stx_3108_, v_origStx_3109_, v_parserState_3110_, v_a_3111_);
lean_dec_ref(v_a_3111_);
return v_res_3113_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_box(0);
v___x_3115_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3114_);
return v___x_3115_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = 1;
v___x_3121_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3122_ = l_Lean_Name_toString(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3123_ = 0;
v___x_3124_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3125_ = lean_box(0);
v___x_3126_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3127_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3128_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___x_3126_);
lean_ctor_set(v___x_3128_, 2, v___x_3125_);
lean_ctor_set(v___x_3128_, 3, v___x_3124_);
lean_ctor_set_uint8(v___x_3128_, sizeof(void*)*4, v___x_3123_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3129_, lean_object* v_cmdState_3130_, lean_object* v_a_3131_, lean_object* v_toSnapshot_3132_, lean_object* v_newStx_3133_, lean_object* v_oldCmd_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_diagnostics_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3164_; 
v___x_3136_ = lean_io_promise_new();
v___x_3137_ = l_IO_CancelToken_new();
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_oldCmd_3134_);
v___x_3139_ = 1;
v___x_3140_ = lean_box(0);
lean_inc_ref(v___x_3137_);
lean_inc(v___x_3136_);
lean_inc_ref(v_cmdState_3130_);
v___x_3141_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3138_, v_newParserState_3129_, v_cmdState_3130_, v___x_3136_, v___x_3139_, v___x_3137_, v___x_3140_, v_a_3131_);
v_diagnostics_3142_ = lean_ctor_get(v_toSnapshot_3132_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_toSnapshot_3132_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; lean_object* v_unused_3166_; lean_object* v_unused_3167_; 
v_unused_3165_ = lean_ctor_get(v_toSnapshot_3132_, 3);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_toSnapshot_3132_, 2);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_toSnapshot_3132_, 0);
lean_dec(v_unused_3167_);
v___x_3144_ = v_toSnapshot_3132_;
v_isShared_3145_ = v_isSharedCheck_3164_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_diagnostics_3142_);
lean_dec(v_toSnapshot_3132_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3164_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3148_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3149_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3137_);
v___x_3151_ = l_IO_Promise_result_x21___redArg(v___x_3136_);
lean_dec(v___x_3136_);
v___x_3152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3146_);
lean_ctor_set(v___x_3152_, 1, v___x_3147_);
lean_ctor_set(v___x_3152_, 2, v___x_3150_);
lean_ctor_set(v___x_3152_, 3, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v_cmdState_3130_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
v___x_3155_ = 0;
v___x_3156_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_newStx_3133_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 3, v___x_3149_);
lean_ctor_set(v___x_3144_, 2, v___x_3146_);
lean_ctor_set(v___x_3144_, 0, v___x_3148_);
v___x_3159_ = v___x_3144_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_diagnostics_3142_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v___x_3149_);
v___x_3159_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_ctor_set_uint8(v___x_3159_, sizeof(void*)*4, v___x_3155_);
v___x_3160_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3157_, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3156_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
lean_ctor_set(v___x_3161_, 2, v___x_3154_);
v___x_3162_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3146_, v___x_3161_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3168_, lean_object* v_cmdState_3169_, lean_object* v_a_3170_, lean_object* v_toSnapshot_3171_, lean_object* v_newStx_3172_, lean_object* v_oldCmd_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3168_, v_cmdState_3169_, v_a_3170_, v_toSnapshot_3171_, v_newStx_3172_, v_oldCmd_3173_);
lean_dec_ref(v_a_3170_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3176_, lean_object* v_a_3177_, lean_object* v_newStx_3178_, lean_object* v___x_3179_, lean_object* v_oldProcessed_3180_){
_start:
{
lean_object* v_result_x3f_3182_; 
v_result_x3f_3182_ = lean_ctor_get(v_oldProcessed_3180_, 2);
if (lean_obj_tag(v_result_x3f_3182_) == 1)
{
lean_object* v_val_3183_; lean_object* v_firstCmdSnap_3184_; lean_object* v_toSnapshot_3185_; lean_object* v_cmdState_3186_; lean_object* v_stx_x3f_3187_; lean_object* v___f_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; lean_object* v___x_3191_; 
v_val_3183_ = lean_ctor_get(v_result_x3f_3182_, 0);
lean_inc(v_val_3183_);
v_firstCmdSnap_3184_ = lean_ctor_get(v_val_3183_, 1);
lean_inc_ref(v_firstCmdSnap_3184_);
v_toSnapshot_3185_ = lean_ctor_get(v_oldProcessed_3180_, 0);
lean_inc_ref(v_toSnapshot_3185_);
lean_dec_ref(v_oldProcessed_3180_);
v_cmdState_3186_ = lean_ctor_get(v_val_3183_, 0);
lean_inc_ref(v_cmdState_3186_);
lean_dec(v_val_3183_);
v_stx_x3f_3187_ = lean_ctor_get(v_firstCmdSnap_3184_, 0);
lean_inc(v_stx_x3f_3187_);
lean_inc_ref(v_a_3177_);
v___f_3188_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3188_, 0, v_newParserState_3176_);
lean_closure_set(v___f_3188_, 1, v_cmdState_3186_);
lean_closure_set(v___f_3188_, 2, v_a_3177_);
lean_closure_set(v___f_3188_, 3, v_toSnapshot_3185_);
lean_closure_set(v___f_3188_, 4, v_newStx_3178_);
v___x_3189_ = lean_box(0);
v___x_3190_ = 1;
v___x_3191_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3184_, v___f_3188_, v_stx_x3f_3187_, v___x_3179_, v___x_3189_, v___x_3190_);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec(v___x_3179_);
lean_dec_ref(v_newParserState_3176_);
v___x_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_newStx_3178_);
v___x_3193_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3192_, v_oldProcessed_3180_);
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3194_, lean_object* v_a_3195_, lean_object* v_newStx_3196_, lean_object* v___x_3197_, lean_object* v_oldProcessed_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3194_, v_a_3195_, v_newStx_3196_, v___x_3197_, v_oldProcessed_3198_);
lean_dec_ref(v_a_3195_);
return v_res_3200_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3201_ = 0;
v___x_3202_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3203_ = lean_box(0);
v___x_3204_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3205_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3206_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3204_);
lean_ctor_set(v___x_3206_, 2, v___x_3203_);
lean_ctor_set(v___x_3206_, 3, v___x_3202_);
lean_ctor_set_uint8(v___x_3206_, sizeof(void*)*4, v___x_3201_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3207_, lean_object* v_a_3208_, lean_object* v_old_3209_, lean_object* v_newStx_3210_, lean_object* v_newParserState_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_result_x3f_3214_; 
v_result_x3f_3214_ = lean_ctor_get(v_old_3209_, 4);
lean_inc(v_result_x3f_3214_);
if (lean_obj_tag(v_result_x3f_3214_) == 1)
{
lean_object* v_val_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3269_; 
v_val_3215_ = lean_ctor_get(v_result_x3f_3214_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_result_x3f_3214_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3217_ = v_result_x3f_3214_;
v_isShared_3218_ = v_isSharedCheck_3269_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_val_3215_);
lean_dec(v_result_x3f_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3269_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v_processedSnap_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3267_; 
v_processedSnap_3219_ = lean_ctor_get(v_val_3215_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_val_3215_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_val_3215_, 0);
lean_dec(v_unused_3268_);
v___x_3221_ = v_val_3215_;
v_isShared_3222_ = v_isSharedCheck_3267_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_processedSnap_3219_);
lean_dec(v_val_3215_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3267_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_toSnapshot_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3262_; 
v_toSnapshot_3223_ = lean_ctor_get(v_old_3209_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_old_3209_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; lean_object* v_unused_3264_; lean_object* v_unused_3265_; lean_object* v_unused_3266_; 
v_unused_3263_ = lean_ctor_get(v_old_3209_, 4);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_old_3209_, 3);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_old_3209_, 2);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_old_3209_, 1);
lean_dec(v_unused_3266_);
v___x_3225_ = v_old_3209_;
v_isShared_3226_ = v_isSharedCheck_3262_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_toSnapshot_3223_);
lean_dec(v_old_3209_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3262_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_pos_3227_; lean_object* v_endPos_3228_; lean_object* v_stx_x3f_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___f_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v_diagnostics_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3258_; 
v_pos_3227_ = lean_ctor_get(v_newParserState_3211_, 0);
v_endPos_3228_ = lean_ctor_get(v_toProcessingContext_3207_, 3);
v_stx_x3f_3229_ = lean_ctor_get(v_processedSnap_3219_, 0);
lean_inc(v_stx_x3f_3229_);
lean_inc(v_endPos_3228_);
lean_inc(v_pos_3227_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_pos_3227_);
lean_ctor_set(v___x_3230_, 1, v_endPos_3228_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_inc_ref(v___x_3231_);
lean_inc(v_newStx_3210_);
lean_inc_ref(v_a_3208_);
lean_inc_ref(v_newParserState_3211_);
v___f_3232_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3232_, 0, v_newParserState_3211_);
lean_closure_set(v___f_3232_, 1, v_a_3208_);
lean_closure_set(v___f_3232_, 2, v_newStx_3210_);
lean_closure_set(v___f_3232_, 3, v___x_3231_);
v___x_3233_ = lean_box(0);
v___x_3234_ = 1;
v___x_3235_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3219_, v___f_3232_, v_stx_x3f_3229_, v___x_3231_, v___x_3233_, v___x_3234_);
v_diagnostics_3236_ = lean_ctor_get(v_toSnapshot_3223_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_toSnapshot_3223_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; lean_object* v_unused_3260_; lean_object* v_unused_3261_; 
v_unused_3259_ = lean_ctor_get(v_toSnapshot_3223_, 3);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_toSnapshot_3223_, 2);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_toSnapshot_3223_, 0);
lean_dec(v_unused_3261_);
v___x_3238_ = v_toSnapshot_3223_;
v_isShared_3239_ = v_isSharedCheck_3258_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_diagnostics_3236_);
lean_dec(v_toSnapshot_3223_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3258_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3240_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3241_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 1, v___x_3235_);
lean_ctor_set(v___x_3221_, 0, v_newParserState_3211_);
v___x_3243_ = v___x_3221_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_newParserState_3211_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3235_);
v___x_3243_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3245_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3243_);
v___x_3245_ = v___x_3217_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
uint8_t v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3246_ = 0;
v___x_3247_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3210_);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_newStx_3210_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 3, v___x_3241_);
lean_ctor_set(v___x_3238_, 2, v___x_3233_);
lean_ctor_set(v___x_3238_, 0, v___x_3240_);
v___x_3250_ = v___x_3238_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_diagnostics_3236_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3255_, 3, v___x_3241_);
v___x_3250_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*4, v___x_3246_);
v___x_3251_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3248_, v___x_3250_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 4, v___x_3245_);
lean_ctor_set(v___x_3225_, 3, v_newStx_3210_);
lean_ctor_set(v___x_3225_, 2, v_toProcessingContext_3207_);
lean_ctor_set(v___x_3225_, 1, v___x_3251_);
lean_ctor_set(v___x_3225_, 0, v___x_3247_);
v___x_3253_ = v___x_3225_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v_toProcessingContext_3207_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v_newStx_3210_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v___x_3245_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
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
lean_dec(v_result_x3f_3214_);
lean_dec_ref(v_newParserState_3211_);
lean_dec(v_newStx_3210_);
lean_dec_ref(v_toProcessingContext_3207_);
return v_old_3209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3270_, lean_object* v_a_3271_, lean_object* v_old_3272_, lean_object* v_newStx_3273_, lean_object* v_newParserState_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3270_, v_a_3271_, v_old_3272_, v_newStx_3273_, v_newParserState_3274_, v___y_3275_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v_a_3271_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3278_, lean_object* v_setupImports_3279_, lean_object* v_old_x3f_3280_, lean_object* v___x_3281_, lean_object* v___f_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; 
lean_inc_ref(v_toProcessingContext_3278_);
v___x_3285_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3278_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3354_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3354_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3354_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_snd_3290_; lean_object* v_fst_3291_; lean_object* v_fst_3292_; lean_object* v_snd_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3353_; 
v_snd_3290_ = lean_ctor_get(v_a_3286_, 1);
lean_inc(v_snd_3290_);
v_fst_3291_ = lean_ctor_get(v_a_3286_, 0);
lean_inc(v_fst_3291_);
lean_dec(v_a_3286_);
v_fst_3292_ = lean_ctor_get(v_snd_3290_, 0);
v_snd_3293_ = lean_ctor_get(v_snd_3290_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_snd_3290_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3295_ = v_snd_3290_;
v_isShared_3296_ = v_isSharedCheck_3353_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_snd_3293_);
lean_inc(v_fst_3292_);
lean_dec(v_snd_3290_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3353_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
uint8_t v___x_3297_; 
v___x_3297_ = l_Lean_MessageLog_hasErrors(v_snd_3293_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___y_3300_; 
lean_inc(v_fst_3291_);
v___x_3298_ = l_Lean_Syntax_unsetTrailing(v_fst_3291_);
if (lean_obj_tag(v_old_x3f_3280_) == 1)
{
lean_object* v_val_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3336_; 
v_val_3321_ = lean_ctor_get(v_old_x3f_3280_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_old_x3f_3280_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3323_ = v_old_x3f_3280_;
v_isShared_3324_ = v_isSharedCheck_3336_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_val_3321_);
lean_dec(v_old_x3f_3280_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3336_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v_stx_3325_; lean_object* v_result_x3f_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_stx_3325_ = lean_ctor_get(v_val_3321_, 3);
v_result_x3f_3326_ = lean_ctor_get(v_val_3321_, 4);
lean_inc(v_stx_3325_);
v___x_3327_ = l_Lean_Syntax_unsetTrailing(v_stx_3325_);
lean_inc(v___x_3298_);
v___x_3328_ = l_Lean_Syntax_eqWithInfo(v___x_3298_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_inc(v_result_x3f_3326_);
lean_del_object(v___x_3323_);
lean_dec(v_val_3321_);
lean_dec_ref(v___f_3282_);
if (lean_obj_tag(v_result_x3f_3326_) == 0)
{
lean_dec_ref(v___x_3281_);
v___y_3300_ = v___y_3283_;
goto v___jp_3299_;
}
else
{
lean_object* v_val_3329_; lean_object* v_processedSnap_3330_; lean_object* v___x_3331_; 
v_val_3329_ = lean_ctor_get(v_result_x3f_3326_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v_result_x3f_3326_, 1);
v_processedSnap_3330_ = lean_ctor_get(v_val_3329_, 1);
lean_inc_ref(v_processedSnap_3330_);
lean_dec(v_val_3329_);
v___x_3331_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3281_, v_processedSnap_3330_);
v___y_3300_ = v___y_3283_;
goto v___jp_3299_;
}
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_dec(v___x_3298_);
lean_del_object(v___x_3295_);
lean_dec(v_snd_3293_);
lean_del_object(v___x_3288_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v_setupImports_3279_);
lean_dec_ref(v_toProcessingContext_3278_);
lean_inc_ref(v___y_3283_);
v___x_3332_ = lean_apply_5(v___f_3282_, v_val_3321_, v_fst_3291_, v_fst_3292_, v___y_3283_, lean_box(0));
if (v_isShared_3324_ == 0)
{
lean_ctor_set_tag(v___x_3323_, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3332_);
v___x_3334_ = v___x_3323_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
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
else
{
lean_dec_ref(v___f_3282_);
lean_dec_ref(v___x_3281_);
lean_dec(v_old_x3f_3280_);
v___y_3300_ = v___y_3283_;
goto v___jp_3299_;
}
v___jp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3301_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3293_);
lean_inc(v_fst_3292_);
lean_inc(v_fst_3291_);
v___x_3302_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3279_, v___x_3298_, v_fst_3291_, v_fst_3292_, v___y_3300_);
v___x_3303_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3304_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_unsigned_to_nat(32u);
v___x_3307_ = lean_mk_empty_array_with_capacity(v___x_3306_);
lean_dec_ref(v___x_3307_);
v___x_3308_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 1, v___x_3302_);
v___x_3310_ = v___x_3295_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_fst_3292_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v___x_3302_);
v___x_3310_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3312_, 0, v___x_3303_);
lean_ctor_set(v___x_3312_, 1, v___x_3304_);
lean_ctor_set(v___x_3312_, 2, v___x_3305_);
lean_ctor_set(v___x_3312_, 3, v___x_3308_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*4, v___x_3297_);
lean_inc(v_fst_3291_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_fst_3291_);
v___x_3314_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3314_, 0, v___x_3303_);
lean_ctor_set(v___x_3314_, 1, v___x_3301_);
lean_ctor_set(v___x_3314_, 2, v___x_3305_);
lean_ctor_set(v___x_3314_, 3, v___x_3308_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*4, v___x_3297_);
v___x_3315_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3313_, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3312_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
lean_ctor_set(v___x_3316_, 2, v_toProcessingContext_3278_);
lean_ctor_set(v___x_3316_, 3, v_fst_3291_);
lean_ctor_set(v___x_3316_, 4, v___x_3311_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3316_);
v___x_3318_ = v___x_3288_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
lean_del_object(v___x_3295_);
lean_dec(v_fst_3292_);
lean_dec_ref(v___f_3282_);
lean_dec_ref(v___x_3281_);
lean_dec(v_old_x3f_3280_);
lean_dec_ref(v_setupImports_3279_);
v___x_3337_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3293_);
v___x_3338_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3339_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_unsigned_to_nat(32u);
v___x_3342_ = lean_mk_empty_array_with_capacity(v___x_3341_);
lean_dec_ref(v___x_3342_);
v___x_3343_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3344_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3344_, 0, v___x_3338_);
lean_ctor_set(v___x_3344_, 1, v___x_3339_);
lean_ctor_set(v___x_3344_, 2, v___x_3340_);
lean_ctor_set(v___x_3344_, 3, v___x_3343_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*4, v___x_3297_);
lean_inc(v_fst_3291_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_fst_3291_);
v___x_3346_ = 0;
v___x_3347_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3347_, 0, v___x_3338_);
lean_ctor_set(v___x_3347_, 1, v___x_3337_);
lean_ctor_set(v___x_3347_, 2, v___x_3340_);
lean_ctor_set(v___x_3347_, 3, v___x_3343_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*4, v___x_3346_);
v___x_3348_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3345_, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3344_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
lean_ctor_set(v___x_3349_, 2, v_toProcessingContext_3278_);
lean_ctor_set(v___x_3349_, 3, v_fst_3291_);
lean_ctor_set(v___x_3349_, 4, v___x_3340_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3349_);
v___x_3351_ = v___x_3288_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref(v___f_3282_);
lean_dec_ref(v___x_3281_);
lean_dec(v_old_x3f_3280_);
lean_dec_ref(v_setupImports_3279_);
lean_dec_ref(v_toProcessingContext_3278_);
v_a_3355_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3285_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3285_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3363_, lean_object* v_setupImports_3364_, lean_object* v_old_x3f_3365_, lean_object* v___x_3366_, lean_object* v___f_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3363_, v_setupImports_3364_, v_old_x3f_3365_, v___x_3366_, v___f_3367_, v___y_3368_);
lean_dec_ref(v___y_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3371_, lean_object* v_toProcessingContext_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3374_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3371_);
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3377_, 0, v_x_3373_);
lean_ctor_set(v___x_3377_, 1, v___x_3374_);
lean_ctor_set(v___x_3377_, 2, v_toProcessingContext_3372_);
lean_ctor_set(v___x_3377_, 3, v___x_3375_);
lean_ctor_set(v___x_3377_, 4, v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3378_, lean_object* v_old_x3f_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_toProcessingContext_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___f_3386_; lean_object* v___f_3387_; 
v_toProcessingContext_3382_ = lean_ctor_get(v_a_3380_, 0);
v___x_3383_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3384_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3380_);
lean_inc_ref_n(v_toProcessingContext_3382_, 3);
v___f_3385_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3385_, 0, v_toProcessingContext_3382_);
lean_closure_set(v___f_3385_, 1, v_a_3380_);
lean_inc(v_old_x3f_3379_);
v___f_3386_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3386_, 0, v_toProcessingContext_3382_);
lean_closure_set(v___f_3386_, 1, v_setupImports_3378_);
lean_closure_set(v___f_3386_, 2, v_old_x3f_3379_);
lean_closure_set(v___f_3386_, 3, v___x_3384_);
lean_closure_set(v___f_3386_, 4, v___f_3385_);
v___f_3387_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3387_, 0, v___x_3383_);
lean_closure_set(v___f_3387_, 1, v_toProcessingContext_3382_);
if (lean_obj_tag(v_old_x3f_3379_) == 1)
{
lean_object* v_val_3388_; lean_object* v_result_x3f_3389_; 
v_val_3388_ = lean_ctor_get(v_old_x3f_3379_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v_old_x3f_3379_, 1);
v_result_x3f_3389_ = lean_ctor_get(v_val_3388_, 4);
if (lean_obj_tag(v_result_x3f_3389_) == 1)
{
lean_object* v_stx_3390_; lean_object* v_val_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v_stx_3390_ = lean_ctor_get(v_val_3388_, 3);
lean_inc(v_stx_3390_);
v_val_3391_ = lean_ctor_get(v_result_x3f_3389_, 0);
lean_inc(v_val_3388_);
v___x_3392_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3388_);
v___x_3393_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3392_);
if (lean_obj_tag(v___x_3393_) == 1)
{
lean_object* v_val_3394_; 
v_val_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_val_3394_);
lean_dec_ref_known(v___x_3393_, 1);
if (lean_obj_tag(v_val_3394_) == 1)
{
lean_object* v_val_3395_; lean_object* v_firstCmdSnap_3396_; lean_object* v___x_3397_; 
v_val_3395_ = lean_ctor_get(v_val_3394_, 0);
lean_inc(v_val_3395_);
lean_dec_ref_known(v_val_3394_, 1);
v_firstCmdSnap_3396_ = lean_ctor_get(v_val_3395_, 1);
lean_inc_ref(v_firstCmdSnap_3396_);
lean_dec(v_val_3395_);
v___x_3397_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3396_);
if (lean_obj_tag(v___x_3397_) == 1)
{
lean_object* v_val_3398_; lean_object* v_nextCmdSnap_x3f_3399_; 
v_val_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v_nextCmdSnap_x3f_3399_ = lean_ctor_get(v_val_3398_, 4);
lean_inc(v_nextCmdSnap_x3f_3399_);
lean_dec(v_val_3398_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3399_) == 0)
{
lean_object* v___x_3400_; 
lean_dec(v_stx_3390_);
lean_dec(v_val_3388_);
v___x_3400_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3400_;
}
else
{
lean_object* v_val_3401_; lean_object* v___x_3402_; 
v_val_3401_ = lean_ctor_get(v_nextCmdSnap_x3f_3399_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3399_, 1);
v___x_3402_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3401_);
if (lean_obj_tag(v___x_3402_) == 1)
{
lean_object* v_val_3403_; lean_object* v_parserState_3404_; lean_object* v_pos_3405_; uint8_t v___x_3406_; 
v_val_3403_ = lean_ctor_get(v___x_3402_, 0);
lean_inc(v_val_3403_);
lean_dec_ref_known(v___x_3402_, 1);
v_parserState_3404_ = lean_ctor_get(v_val_3403_, 2);
lean_inc_ref(v_parserState_3404_);
lean_dec(v_val_3403_);
v_pos_3405_ = lean_ctor_get(v_parserState_3404_, 0);
lean_inc(v_pos_3405_);
lean_dec_ref(v_parserState_3404_);
v___x_3406_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3405_, v_a_3380_);
lean_dec(v_pos_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
lean_dec(v_stx_3390_);
lean_dec(v_val_3388_);
v___x_3407_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3407_;
}
else
{
lean_object* v_parserState_3408_; lean_object* v___x_3409_; 
lean_dec_ref(v___f_3387_);
lean_dec_ref(v___f_3386_);
v_parserState_3408_ = lean_ctor_get(v_val_3391_, 0);
lean_inc_ref(v_parserState_3408_);
lean_inc_ref(v_toProcessingContext_3382_);
v___x_3409_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3382_, v_a_3380_, v_val_3388_, v_stx_3390_, v_parserState_3408_, v_a_3380_);
return v___x_3409_;
}
}
else
{
lean_object* v___x_3410_; 
lean_dec(v___x_3402_);
lean_dec(v_stx_3390_);
lean_dec(v_val_3388_);
v___x_3410_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3410_;
}
}
}
else
{
lean_object* v___x_3411_; 
lean_dec(v___x_3397_);
lean_dec(v_stx_3390_);
lean_dec(v_val_3388_);
v___x_3411_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3411_;
}
}
else
{
lean_object* v___x_3412_; 
lean_dec(v_val_3394_);
lean_dec(v_stx_3390_);
lean_dec(v_val_3388_);
v___x_3412_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3412_;
}
}
else
{
lean_object* v___x_3413_; 
lean_dec(v___x_3393_);
lean_dec(v_stx_3390_);
lean_dec(v_val_3388_);
v___x_3413_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3413_;
}
}
else
{
lean_object* v___x_3414_; 
lean_dec(v_val_3388_);
v___x_3414_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3414_;
}
}
else
{
lean_object* v___x_3415_; 
lean_dec(v_old_x3f_3379_);
v___x_3415_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3387_, v___f_3386_, v_a_3380_);
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3416_, lean_object* v_old_x3f_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3416_, v_old_x3f_3417_, v_a_3418_);
lean_dec_ref(v_a_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3421_, lean_object* v_old_x3f_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___x_3425_; 
lean_inc(v_old_x3f_3422_);
v___x_3425_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3425_, 0, v_setupImports_3421_);
lean_closure_set(v___x_3425_, 1, v_old_x3f_3422_);
if (lean_obj_tag(v_old_x3f_3422_) == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_box(0);
v___x_3427_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3425_, v___x_3426_, v_a_3423_);
return v___x_3427_;
}
else
{
lean_object* v_val_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3437_; 
v_val_3428_ = lean_ctor_get(v_old_x3f_3422_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_old_x3f_3422_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3430_ = v_old_x3f_3422_;
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_val_3428_);
lean_dec(v_old_x3f_3422_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_ictx_3432_; lean_object* v___x_3434_; 
v_ictx_3432_ = lean_ctor_get(v_val_3428_, 2);
lean_inc_ref(v_ictx_3432_);
lean_dec(v_val_3428_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v_ictx_3432_);
v___x_3434_ = v___x_3430_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_ictx_3432_);
v___x_3434_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3425_, v___x_3434_, v_a_3423_);
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3438_, lean_object* v_old_x3f_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Language_Lean_process(v_setupImports_3438_, v_old_x3f_3439_, v_a_3440_);
lean_dec_ref(v_a_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3443_, lean_object* v_parserState_3444_, lean_object* v_commandState_3445_, lean_object* v_old_x3f_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3456_; 
v___x_3448_ = lean_io_promise_new();
v___x_3449_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3446_) == 0)
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_box(0);
v___y_3456_ = v___x_3471_;
goto v___jp_3455_;
}
else
{
lean_object* v_val_3472_; lean_object* v_snd_3473_; lean_object* v___x_3474_; 
v_val_3472_ = lean_ctor_get(v_old_x3f_3446_, 0);
v_snd_3473_ = lean_ctor_get(v_val_3472_, 1);
lean_inc(v_snd_3473_);
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v_snd_3473_);
v___y_3456_ = v___x_3474_;
goto v___jp_3455_;
}
v___jp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3451_, v___y_3452_, v_inputCtx_3443_);
lean_dec(v___x_3453_);
v___x_3454_ = l_IO_Promise_result_x21___redArg(v___x_3448_);
lean_dec(v___x_3448_);
return v___x_3454_;
}
v___jp_3455_:
{
uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3457_ = 1;
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_box(v___x_3457_);
lean_inc(v___x_3448_);
v___x_3460_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3460_, 0, v___y_3456_);
lean_closure_set(v___x_3460_, 1, v_parserState_3444_);
lean_closure_set(v___x_3460_, 2, v_commandState_3445_);
lean_closure_set(v___x_3460_, 3, v___x_3448_);
lean_closure_set(v___x_3460_, 4, v___x_3459_);
lean_closure_set(v___x_3460_, 5, v___x_3449_);
lean_closure_set(v___x_3460_, 6, v___x_3458_);
if (lean_obj_tag(v_old_x3f_3446_) == 0)
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_box(0);
v___y_3451_ = v___x_3460_;
v___y_3452_ = v___x_3461_;
goto v___jp_3450_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3470_; 
v_val_3462_ = lean_ctor_get(v_old_x3f_3446_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_old_x3f_3446_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3464_ = v_old_x3f_3446_;
v_isShared_3465_ = v_isSharedCheck_3470_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v_old_x3f_3446_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3470_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_fst_3466_; lean_object* v___x_3468_; 
v_fst_3466_ = lean_ctor_get(v_val_3462_, 0);
lean_inc(v_fst_3466_);
lean_dec(v_val_3462_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_fst_3466_);
v___x_3468_ = v___x_3464_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_fst_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
v___y_3451_ = v___x_3460_;
v___y_3452_ = v___x_3468_;
goto v___jp_3450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3475_, lean_object* v_parserState_3476_, lean_object* v_commandState_3477_, lean_object* v_old_x3f_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3475_, v_parserState_3476_, v_commandState_3477_, v_old_x3f_3478_);
lean_dec_ref(v_inputCtx_3475_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3481_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3482_; 
v_nextCmdSnap_x3f_3482_ = lean_ctor_get(v_snap_3481_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3482_) == 1)
{
lean_object* v_val_3483_; lean_object* v___x_3484_; 
lean_inc_ref(v_nextCmdSnap_x3f_3482_);
lean_dec_ref(v_snap_3481_);
v_val_3483_ = lean_ctor_get(v_nextCmdSnap_x3f_3482_, 0);
lean_inc(v_val_3483_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3482_, 1);
v___x_3484_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3483_);
v_snap_3481_ = v___x_3484_;
goto _start;
}
else
{
lean_object* v_elabSnap_3486_; lean_object* v_resultSnap_3487_; lean_object* v___x_3488_; lean_object* v_cmdState_3489_; lean_object* v___x_3490_; 
v_elabSnap_3486_ = lean_ctor_get(v_snap_3481_, 3);
lean_inc_ref(v_elabSnap_3486_);
lean_dec_ref(v_snap_3481_);
v_resultSnap_3487_ = lean_ctor_get(v_elabSnap_3486_, 2);
lean_inc_ref(v_resultSnap_3487_);
lean_dec_ref(v_elabSnap_3486_);
v___x_3488_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3487_);
v_cmdState_3489_ = lean_ctor_get(v___x_3488_, 1);
lean_inc_ref(v_cmdState_3489_);
lean_dec(v___x_3488_);
v___x_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_cmdState_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3491_){
_start:
{
lean_object* v_result_x3f_3492_; 
v_result_x3f_3492_ = lean_ctor_get(v_snap_3491_, 4);
lean_inc(v_result_x3f_3492_);
lean_dec_ref(v_snap_3491_);
if (lean_obj_tag(v_result_x3f_3492_) == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_box(0);
return v___x_3493_;
}
else
{
lean_object* v_val_3494_; lean_object* v_processedSnap_3495_; lean_object* v___x_3496_; lean_object* v_result_x3f_3497_; 
v_val_3494_ = lean_ctor_get(v_result_x3f_3492_, 0);
lean_inc(v_val_3494_);
lean_dec_ref_known(v_result_x3f_3492_, 1);
v_processedSnap_3495_ = lean_ctor_get(v_val_3494_, 1);
lean_inc_ref(v_processedSnap_3495_);
lean_dec(v_val_3494_);
v___x_3496_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3495_);
v_result_x3f_3497_ = lean_ctor_get(v___x_3496_, 2);
lean_inc(v_result_x3f_3497_);
lean_dec(v___x_3496_);
if (lean_obj_tag(v_result_x3f_3497_) == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_box(0);
return v___x_3498_;
}
else
{
lean_object* v_val_3499_; lean_object* v_firstCmdSnap_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v_val_3499_ = lean_ctor_get(v_result_x3f_3497_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v_result_x3f_3497_, 1);
v_firstCmdSnap_3500_ = lean_ctor_get(v_val_3499_, 1);
lean_inc_ref(v_firstCmdSnap_3500_);
lean_dec(v_val_3499_);
v___x_3501_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3500_);
v___x_3502_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3501_);
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3503_, lean_object* v_snap_3504_, lean_object* v_acc_3505_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3506_; lean_object* v_acc_3507_; 
v_nextCmdSnap_x3f_3506_ = lean_ctor_get(v_snap_3504_, 4);
lean_inc(v_nextCmdSnap_x3f_3506_);
lean_inc(v_f_3503_);
v_acc_3507_ = lean_apply_2(v_f_3503_, v_acc_3505_, v_snap_3504_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3506_) == 1)
{
lean_object* v_val_3508_; lean_object* v___x_3509_; 
v_val_3508_ = lean_ctor_get(v_nextCmdSnap_x3f_3506_, 0);
lean_inc(v_val_3508_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3506_, 1);
v___x_3509_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3508_);
v_snap_3504_ = v___x_3509_;
v_acc_3505_ = v_acc_3507_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3506_);
lean_dec(v_f_3503_);
return v_acc_3507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3511_, lean_object* v_f_3512_, lean_object* v_snap_3513_, lean_object* v_acc_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3512_, v_snap_3513_, v_acc_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3516_, lean_object* v_init_3517_, lean_object* v_f_3518_){
_start:
{
lean_object* v_result_x3f_3519_; 
v_result_x3f_3519_ = lean_ctor_get(v_snap_3516_, 4);
lean_inc(v_result_x3f_3519_);
lean_dec_ref(v_snap_3516_);
if (lean_obj_tag(v_result_x3f_3519_) == 0)
{
lean_object* v___x_3520_; 
lean_dec(v_f_3518_);
lean_dec(v_init_3517_);
v___x_3520_ = lean_box(0);
return v___x_3520_;
}
else
{
lean_object* v_val_3521_; lean_object* v_processedSnap_3522_; lean_object* v___x_3523_; lean_object* v_result_x3f_3524_; 
v_val_3521_ = lean_ctor_get(v_result_x3f_3519_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v_result_x3f_3519_, 1);
v_processedSnap_3522_ = lean_ctor_get(v_val_3521_, 1);
lean_inc_ref(v_processedSnap_3522_);
lean_dec(v_val_3521_);
v___x_3523_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3522_);
v_result_x3f_3524_ = lean_ctor_get(v___x_3523_, 2);
lean_inc(v_result_x3f_3524_);
lean_dec(v___x_3523_);
if (lean_obj_tag(v_result_x3f_3524_) == 0)
{
lean_object* v___x_3525_; 
lean_dec(v_f_3518_);
lean_dec(v_init_3517_);
v___x_3525_ = lean_box(0);
return v___x_3525_;
}
else
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3536_; 
v_val_3526_ = lean_ctor_get(v_result_x3f_3524_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_result_x3f_3524_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3528_ = v_result_x3f_3524_;
v_isShared_3529_ = v_isSharedCheck_3536_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_result_x3f_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3536_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_firstCmdSnap_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v_firstCmdSnap_3530_ = lean_ctor_get(v_val_3526_, 1);
lean_inc_ref(v_firstCmdSnap_3530_);
lean_dec(v_val_3526_);
v___x_3531_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3530_);
v___x_3532_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3518_, v___x_3531_, v_init_3517_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3532_);
v___x_3534_ = v___x_3528_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3537_, lean_object* v_snap_3538_, lean_object* v_init_3539_, lean_object* v_f_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3538_, v_init_3539_, v_f_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = 1;
v___x_3548_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3549_ = l_Lean_Name_toString(v___x_3548_, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3550_ = 0;
v___x_3551_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3552_ = lean_box(0);
v___x_3553_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3554_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3555_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___x_3553_);
lean_ctor_set(v___x_3555_, 2, v___x_3552_);
lean_ctor_set(v___x_3555_, 3, v___x_3551_);
lean_ctor_set_uint8(v___x_3555_, sizeof(void*)*4, v___x_3550_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3557_ = lean_box(0);
v___x_3558_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3559_){
_start:
{
lean_object* v_result_x3f_3560_; 
v_result_x3f_3560_ = lean_ctor_get(v_snap_3559_, 4);
lean_inc(v_result_x3f_3560_);
if (lean_obj_tag(v_result_x3f_3560_) == 1)
{
lean_object* v_val_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3636_; 
v_val_3561_ = lean_ctor_get(v_result_x3f_3560_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_result_x3f_3560_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3563_ = v_result_x3f_3560_;
v_isShared_3564_ = v_isSharedCheck_3636_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_val_3561_);
lean_dec(v_result_x3f_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3636_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v_toSnapshot_3565_; lean_object* v_metaSnap_3566_; lean_object* v_ictx_3567_; lean_object* v_stx_3568_; lean_object* v_parserState_3569_; lean_object* v_processedSnap_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3635_; 
v_toSnapshot_3565_ = lean_ctor_get(v_snap_3559_, 0);
v_metaSnap_3566_ = lean_ctor_get(v_snap_3559_, 1);
v_ictx_3567_ = lean_ctor_get(v_snap_3559_, 2);
v_stx_3568_ = lean_ctor_get(v_snap_3559_, 3);
v_parserState_3569_ = lean_ctor_get(v_val_3561_, 0);
v_processedSnap_3570_ = lean_ctor_get(v_val_3561_, 1);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_val_3561_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3572_ = v_val_3561_;
v_isShared_3573_ = v_isSharedCheck_3635_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_processedSnap_3570_);
lean_inc(v_parserState_3569_);
lean_dec(v_val_3561_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3635_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v_processed_3574_; lean_object* v_result_x3f_3575_; 
v_processed_3574_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3570_);
v_result_x3f_3575_ = lean_ctor_get(v_processed_3574_, 2);
lean_inc(v_result_x3f_3575_);
if (lean_obj_tag(v_result_x3f_3575_) == 1)
{
lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3629_; 
lean_inc(v_stx_3568_);
lean_inc_ref(v_ictx_3567_);
lean_inc_ref(v_metaSnap_3566_);
lean_inc_ref(v_toSnapshot_3565_);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_snap_3559_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; lean_object* v_unused_3631_; lean_object* v_unused_3632_; lean_object* v_unused_3633_; lean_object* v_unused_3634_; 
v_unused_3630_ = lean_ctor_get(v_snap_3559_, 4);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_snap_3559_, 3);
lean_dec(v_unused_3631_);
v_unused_3632_ = lean_ctor_get(v_snap_3559_, 2);
lean_dec(v_unused_3632_);
v_unused_3633_ = lean_ctor_get(v_snap_3559_, 1);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v_snap_3559_, 0);
lean_dec(v_unused_3634_);
v___x_3577_ = v_snap_3559_;
v_isShared_3578_ = v_isSharedCheck_3629_;
goto v_resetjp_3576_;
}
else
{
lean_dec(v_snap_3559_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3629_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_val_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3628_; 
v_val_3579_ = lean_ctor_get(v_result_x3f_3575_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_result_x3f_3575_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3581_ = v_result_x3f_3575_;
v_isShared_3582_ = v_isSharedCheck_3628_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_val_3579_);
lean_dec(v_result_x3f_3575_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3628_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_toSnapshot_3583_; lean_object* v_metaSnap_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3626_; 
v_toSnapshot_3583_ = lean_ctor_get(v_processed_3574_, 0);
v_metaSnap_3584_ = lean_ctor_get(v_processed_3574_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_processed_3574_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v_processed_3574_, 2);
lean_dec(v_unused_3627_);
v___x_3586_ = v_processed_3574_;
v_isShared_3587_ = v_isSharedCheck_3626_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_metaSnap_3584_);
lean_inc(v_toSnapshot_3583_);
lean_dec(v_processed_3574_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3626_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v_cmdState_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3624_; 
v_cmdState_3588_ = lean_ctor_get(v_val_3579_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_val_3579_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v_val_3579_, 1);
lean_dec(v_unused_3625_);
v___x_3590_ = v_val_3579_;
v_isShared_3591_ = v_isSharedCheck_3624_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_cmdState_3588_);
lean_dec(v_val_3579_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3624_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v_resultSnap_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_elabSnap_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_termCmd_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3592_ = lean_box(0);
v___x_3593_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3594_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3588_);
v_resultSnap_3595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3595_, 0, v___x_3593_);
lean_ctor_set(v_resultSnap_3595_, 1, v_cmdState_3588_);
lean_ctor_set(v_resultSnap_3595_, 2, v___x_3594_);
v___x_3596_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3597_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3592_, v_resultSnap_3595_);
v___x_3598_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3599_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3600_, 0, v___x_3593_);
lean_ctor_set(v_elabSnap_3600_, 1, v___x_3596_);
lean_ctor_set(v_elabSnap_3600_, 2, v___x_3597_);
lean_ctor_set(v_elabSnap_3600_, 3, v___x_3598_);
lean_ctor_set(v_elabSnap_3600_, 4, v___x_3599_);
v___x_3601_ = lean_box(0);
v___x_3602_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3603_, 0, v___x_3593_);
lean_ctor_set(v_termCmd_3603_, 1, v___x_3601_);
lean_ctor_set(v_termCmd_3603_, 2, v___x_3602_);
lean_ctor_set(v_termCmd_3603_, 3, v_elabSnap_3600_);
lean_ctor_set(v_termCmd_3603_, 4, v___x_3592_);
v___x_3604_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3592_, v_termCmd_3603_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v___x_3604_);
v___x_3606_ = v___x_3590_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_cmdState_3588_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3606_);
v___x_3608_ = v___x_3581_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v_newProcessed_3610_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 2, v___x_3608_);
v_newProcessed_3610_ = v___x_3586_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_toSnapshot_3583_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_metaSnap_3584_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v___x_3608_);
v_newProcessed_3610_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3592_, v_newProcessed_3610_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 1, v___x_3611_);
v___x_3613_ = v___x_3572_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_parserState_3569_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3613_);
v___x_3615_ = v___x_3563_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 4, v___x_3615_);
v___x_3617_ = v___x_3577_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_toSnapshot_3565_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_metaSnap_3566_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_ictx_3567_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_stx_3568_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
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
lean_dec(v_result_x3f_3575_);
lean_dec(v_processed_3574_);
lean_del_object(v___x_3572_);
lean_dec_ref(v_parserState_3569_);
lean_del_object(v___x_3563_);
return v_snap_3559_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3560_);
return v_snap_3559_;
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

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
extern lean_object* l_Lean_Options_empty;
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
lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; uint8_t v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; uint8_t v___y_774_; lean_object* v___y_775_; uint8_t v___y_776_; uint8_t v___y_777_; lean_object* v___y_778_; uint8_t v___y_782_; uint8_t v___y_783_; uint8_t v___y_784_; uint8_t v___x_799_; uint8_t v___y_801_; uint8_t v___y_802_; uint8_t v___y_803_; uint8_t v___y_805_; uint8_t v___x_817_; 
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
lean_ctor_set(v___x_699_, 1, v___y_684_);
lean_inc_ref(v___y_686_);
lean_inc_ref(v___y_681_);
v___x_700_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_700_, 0, v___y_681_);
lean_ctor_set(v___x_700_, 1, v___y_685_);
lean_ctor_set(v___x_700_, 2, v___y_683_);
lean_ctor_set(v___x_700_, 3, v___y_686_);
lean_ctor_set(v___x_700_, 4, v___x_699_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5, v___y_682_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 1, v___y_687_);
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
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
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
lean_dec_ref(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
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
v___x_763_ = l_Lean_FileMap_toPosition(v_fileMap_752_, v___y_747_);
lean_dec(v___y_747_);
v___x_764_ = l_Lean_FileMap_toPosition(v_fileMap_752_, v___y_750_);
lean_dec(v___y_750_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_753_ == 0)
{
lean_del_object(v___x_761_);
lean_dec_ref(v___f_756_);
v___y_681_ = v_fileName_751_;
v___y_682_ = v___y_748_;
v___y_683_ = v___x_765_;
v___y_684_ = v_a_759_;
v___y_685_ = v___x_763_;
v___y_686_ = v___x_766_;
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
v___y_681_ = v_fileName_751_;
v___y_682_ = v___y_748_;
v___y_683_ = v___x_765_;
v___y_684_ = v_a_759_;
v___y_685_ = v___x_763_;
v___y_686_ = v___x_766_;
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
v___x_779_ = l_Lean_Syntax_getTailPos_x3f(v___y_775_, v___y_776_);
lean_dec(v___y_775_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_inc(v___y_778_);
v___y_746_ = v___y_774_;
v___y_747_ = v___y_778_;
v___y_748_ = v___y_776_;
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
v___y_747_ = v___y_778_;
v___y_748_ = v___y_776_;
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
v___y_775_ = v_ref_787_;
v___y_776_ = v___y_783_;
v___y_777_ = v___y_784_;
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
v___y_775_ = v_ref_787_;
v___y_776_ = v___y_783_;
v___y_777_ = v___y_784_;
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
lean_object* v___x_1106_; lean_object* v_toProcessingContext_1107_; lean_object* v_fileName_1108_; lean_object* v_fileMap_1109_; lean_object* v_opts_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; uint8_t v___y_1118_; lean_object* v_env_1119_; lean_object* v_scopes_1120_; lean_object* v_usedQuotCtxts_1121_; lean_object* v_nextMacroScope_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_ngen_1124_; lean_object* v_auxDeclNGen_1125_; lean_object* v_infoState_1126_; lean_object* v_traceState_1127_; lean_object* v_snapshotTasks_1128_; lean_object* v_prevLinterStates_1129_; lean_object* v_codeQualityEntryTasks_1130_; lean_object* v_messages_1131_; lean_object* v___y_1140_; 
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
lean_ctor_set(v___x_1133_, 0, v_env_1119_);
lean_ctor_set(v___x_1133_, 1, v_messages_1131_);
lean_ctor_set(v___x_1133_, 2, v_scopes_1120_);
lean_ctor_set(v___x_1133_, 3, v_usedQuotCtxts_1121_);
lean_ctor_set(v___x_1133_, 4, v_nextMacroScope_1122_);
lean_ctor_set(v___x_1133_, 5, v_maxRecDepth_1123_);
lean_ctor_set(v___x_1133_, 6, v_ngen_1124_);
lean_ctor_set(v___x_1133_, 7, v_auxDeclNGen_1125_);
lean_ctor_set(v___x_1133_, 8, v_infoState_1126_);
lean_ctor_set(v___x_1133_, 9, v_traceState_1127_);
lean_ctor_set(v___x_1133_, 10, v_snapshotTasks_1128_);
lean_ctor_set(v___x_1133_, 11, v_prevLinterStates_1129_);
lean_ctor_set(v___x_1133_, 12, v_codeQualityEntryTasks_1130_);
v___x_1134_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1135_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1136_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1112_);
lean_ctor_set(v___x_1136_, 3, v___x_1102_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*4, v___y_1118_);
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
v___y_1118_ = v___x_1142_;
v_env_1119_ = v_env_1150_;
v_scopes_1120_ = v_scopes_1152_;
v_usedQuotCtxts_1121_ = v_usedQuotCtxts_1153_;
v_nextMacroScope_1122_ = v_nextMacroScope_1154_;
v_maxRecDepth_1123_ = v_maxRecDepth_1155_;
v_ngen_1124_ = v_ngen_1156_;
v_auxDeclNGen_1125_ = v_auxDeclNGen_1157_;
v_infoState_1126_ = v_infoState_1158_;
v_traceState_1127_ = v_traceState_1159_;
v_snapshotTasks_1128_ = v_snapshotTasks_1160_;
v_prevLinterStates_1129_ = v_prevLinterStates_1161_;
v_codeQualityEntryTasks_1130_ = v_codeQualityEntryTasks_1162_;
v_messages_1131_ = v___x_1171_;
goto v___jp_1117_;
}
else
{
lean_dec(v_fst_1148_);
lean_dec(v_beginPos_1079_);
v___y_1118_ = v___x_1142_;
v_env_1119_ = v_env_1150_;
v_scopes_1120_ = v_scopes_1152_;
v_usedQuotCtxts_1121_ = v_usedQuotCtxts_1153_;
v_nextMacroScope_1122_ = v_nextMacroScope_1154_;
v_maxRecDepth_1123_ = v_maxRecDepth_1155_;
v_ngen_1124_ = v_ngen_1156_;
v_auxDeclNGen_1125_ = v_auxDeclNGen_1157_;
v_infoState_1126_ = v_infoState_1158_;
v_traceState_1127_ = v_traceState_1159_;
v_snapshotTasks_1128_ = v_snapshotTasks_1160_;
v_prevLinterStates_1129_ = v_prevLinterStates_1161_;
v_codeQualityEntryTasks_1130_ = v_codeQualityEntryTasks_1162_;
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
uint8_t v_val_36222__boxed_1331_; uint8_t v___x_36227__boxed_1332_; lean_object* v_res_1333_; 
v_val_36222__boxed_1331_ = lean_unbox(v_val_1320_);
v___x_36227__boxed_1332_ = lean_unbox(v___x_1325_);
v_res_1333_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1318_, v___x_1319_, v_val_36222__boxed_1331_, v_val_1321_, v_val_1322_, v___x_1323_, v___x_1324_, v___x_36227__boxed_1332_, v_a_1326_, v_pos_1327_, v___x_1328_, v_infoSt_1329_);
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
uint8_t v_val_36335__boxed_1373_; size_t v_sz_boxed_1374_; size_t v_i_boxed_1375_; lean_object* v_res_1376_; 
v_val_36335__boxed_1373_ = lean_unbox(v_val_1367_);
v_sz_boxed_1374_ = lean_unbox_usize(v_sz_1369_);
lean_dec(v_sz_1369_);
v_i_boxed_1375_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1364_, v___x_1365_, v___x_1366_, v_val_36335__boxed_1373_, v_as_1368_, v_sz_boxed_1374_, v_i_boxed_1375_, v_b_1371_);
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
uint8_t v_val_36387__boxed_1416_; size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_val_36387__boxed_1416_ = lean_unbox(v_val_1410_);
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1412_);
lean_dec(v_sz_1412_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1407_, v___x_1408_, v___x_1409_, v_val_36387__boxed_1416_, v_as_1411_, v_sz_boxed_1417_, v_i_boxed_1418_, v_b_1414_);
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
lean_inc(v_fst_1434_);
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
lean_inc(v_fst_1444_);
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
uint8_t v_val_36438__boxed_1489_; size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_val_36438__boxed_1489_ = lean_unbox(v_val_1483_);
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1485_);
lean_dec(v_sz_1485_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1486_);
lean_dec(v_i_1486_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1479_, v___x_1480_, v___x_1481_, v___x_1482_, v_val_36438__boxed_1489_, v_as_1484_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_1487_);
lean_dec_ref(v_as_1484_);
lean_dec(v___x_1481_);
lean_dec_ref(v_init_1479_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1493_, lean_object* v___x_1494_, lean_object* v___x_1495_, lean_object* v___x_1496_, lean_object* v_val_1497_, lean_object* v_n_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_val_36454__boxed_1501_; lean_object* v_res_1502_; 
v_val_36454__boxed_1501_ = lean_unbox(v_val_1497_);
v_res_1502_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1493_, v___x_1494_, v___x_1495_, v___x_1496_, v_val_36454__boxed_1501_, v_n_1498_, v_b_1499_);
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
uint8_t v_val_36536__boxed_1542_; size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_val_36536__boxed_1542_ = lean_unbox(v_val_1536_);
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1538_);
lean_dec(v_sz_1538_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1539_);
lean_dec(v_i_1539_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1533_, v___x_1534_, v___x_1535_, v_val_36536__boxed_1542_, v_as_1537_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1540_);
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
uint8_t v_val_36588__boxed_1585_; size_t v_sz_boxed_1586_; size_t v_i_boxed_1587_; lean_object* v_res_1588_; 
v_val_36588__boxed_1585_ = lean_unbox(v_val_1579_);
v_sz_boxed_1586_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1587_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1576_, v___x_1577_, v___x_1578_, v_val_36588__boxed_1585_, v_as_1580_, v_sz_boxed_1586_, v_i_boxed_1587_, v_b_1583_);
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
lean_inc(v_fst_1606_);
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
uint8_t v_val_36639__boxed_1616_; lean_object* v_res_1617_; 
v_val_36639__boxed_1616_ = lean_unbox(v_val_1612_);
v_res_1617_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1609_, v___x_1610_, v___x_1611_, v_val_36639__boxed_1616_, v_t_1613_, v_init_1614_);
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
lean_object* v_toProcessingContext_1651_; lean_object* v_fileName_1652_; lean_object* v_fileMap_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint16_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_fileName_1675_; lean_object* v_fileMap_1676_; lean_object* v_currNamespace_1677_; lean_object* v_openDecls_1678_; lean_object* v_initHeartbeats_1679_; lean_object* v_maxHeartbeats_1680_; lean_object* v_quotContext_1681_; lean_object* v_currMacroScope_1682_; lean_object* v_cancelTk_x3f_1683_; lean_object* v_inheritedTraceOptions_1684_; lean_object* v_currRecDepth_1685_; lean_object* v_ref_1686_; uint8_t v_suppressElabErrors_1687_; uint8_t v_isRecordingDeps_1688_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___y_1708_; uint8_t v___y_1730_; uint8_t v___y_1731_; lean_object* v_env_1732_; uint8_t v___x_1733_; uint8_t v___y_1735_; uint16_t v___x_1736_; uint16_t v___x_1737_; uint16_t v___x_1738_; uint8_t v___x_1739_; 
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
v___x_1666_ = lean_mk_empty_array_with_capacity(v___x_1635_);
lean_inc_ref(v___x_1666_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_inc_n(v___x_1634_, 2);
v___x_1668_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1666_);
lean_ctor_set(v___x_1668_, 2, v___x_1634_);
lean_ctor_set(v___x_1668_, 3, v___x_1634_);
lean_ctor_set_usize(v___x_1668_, 4, v___x_1636_);
v___x_1669_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1668_, 2);
v___x_1670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1668_);
lean_ctor_set(v___x_1670_, 2, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1671_, 0, v___x_1663_);
lean_ctor_set(v___x_1671_, 1, v___x_1663_);
lean_ctor_set(v___x_1671_, 2, v___x_1668_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*3, v___x_1637_);
lean_inc_ref_n(v___x_1665_, 2);
lean_inc_ref(v___x_1639_);
v___x_1672_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1672_, 0, v_env_1638_);
lean_ctor_set(v___x_1672_, 1, v___x_1660_);
lean_ctor_set(v___x_1672_, 2, v___x_1661_);
lean_ctor_set(v___x_1672_, 3, v___x_1662_);
lean_ctor_set(v___x_1672_, 4, v___x_1639_);
lean_ctor_set(v___x_1672_, 5, v___x_1664_);
lean_ctor_set(v___x_1672_, 6, v___x_1665_);
lean_ctor_set(v___x_1672_, 7, v___x_1670_);
lean_ctor_set(v___x_1672_, 8, v___x_1671_);
lean_ctor_set(v___x_1672_, 9, v___x_1665_);
v___x_1673_ = lean_st_mk_ref(v___x_1672_);
v___x_1705_ = lean_st_ref_get(v___x_1646_);
v___x_1706_ = lean_st_ref_get(v___x_1673_);
v_env_1732_ = lean_ctor_get(v___x_1706_, 0);
lean_inc_ref(v_env_1732_);
lean_dec(v___x_1706_);
v___x_1733_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1732_);
lean_dec_ref(v_env_1732_);
v___x_1736_ = 512;
v___x_1737_ = lean_uint16_land(v___x_1658_, v___x_1736_);
v___x_1738_ = 0;
v___x_1739_ = lean_uint16_dec_eq(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
if (v___x_1648_ == 0)
{
v___y_1735_ = v___x_1648_;
goto v___jp_1734_;
}
else
{
v___y_1730_ = v___x_1648_;
v___y_1731_ = v___x_1733_;
goto v___jp_1729_;
}
}
else
{
v___y_1735_ = v_val_1642_;
goto v___jp_1734_;
}
v___jp_1674_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1689_ = l_Lean_maxRecDepth;
v___x_1690_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1632_, v___x_1689_);
lean_inc(v_currMacroScope_1682_);
lean_inc(v_openDecls_1678_);
v___x_1691_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1691_, 0, v_fileName_1675_);
lean_ctor_set(v___x_1691_, 1, v_fileMap_1676_);
lean_ctor_set(v___x_1691_, 2, v_opts_1632_);
lean_ctor_set(v___x_1691_, 3, v___x_1690_);
lean_ctor_set(v___x_1691_, 4, v_currNamespace_1677_);
lean_ctor_set(v___x_1691_, 5, v_openDecls_1678_);
lean_ctor_set(v___x_1691_, 6, v_initHeartbeats_1679_);
lean_ctor_set(v___x_1691_, 7, v_maxHeartbeats_1680_);
lean_ctor_set(v___x_1691_, 8, v_quotContext_1681_);
lean_ctor_set(v___x_1691_, 9, v_currMacroScope_1682_);
lean_ctor_set(v___x_1691_, 10, v_cancelTk_x3f_1683_);
lean_ctor_set(v___x_1691_, 11, v_inheritedTraceOptions_1684_);
lean_inc(v_ref_1686_);
v___x_1692_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v_currRecDepth_1685_);
lean_ctor_set(v___x_1692_, 2, v_ref_1686_);
lean_ctor_set_uint16(v___x_1692_, sizeof(void*)*3, v___x_1658_);
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*3 + 2, v_suppressElabErrors_1687_);
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*3 + 3, v_isRecordingDeps_1688_);
v___x_1693_ = l_Lean_Language_SnapshotTree_trace(v___x_1640_, v___x_1692_, v___x_1673_);
lean_dec_ref_known(v___x_1692_, 3);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; lean_object* v_traceState_1695_; lean_object* v_traces_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref_known(v___x_1693_, 1);
lean_dec_ref(v___x_1645_);
v___x_1694_ = lean_st_ref_get(v___x_1673_);
lean_dec(v___x_1673_);
v_traceState_1695_ = lean_ctor_get(v___x_1694_, 4);
lean_inc_ref(v_traceState_1695_);
lean_dec(v___x_1694_);
v_traces_1696_ = lean_ctor_get(v_traceState_1695_, 0);
lean_inc_ref(v_traces_1696_);
lean_dec_ref(v_traceState_1695_);
v___x_1697_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1652_);
lean_inc_ref(v_fileMap_1653_);
v___x_1698_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1653_, v_pos_1641_, v_fileName_1652_, v_val_1642_, v_traces_1696_, v___x_1697_);
lean_dec_ref(v_traces_1696_);
v___x_1699_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1700_, 0, v___x_1643_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
lean_ctor_set(v___x_1700_, 2, v___x_1644_);
lean_ctor_set(v___x_1700_, 3, v___x_1639_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*4, v_val_1642_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v___x_1665_);
v___x_1702_ = lean_task_pure(v___x_1701_);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref_known(v___x_1693_, 1);
lean_dec(v___x_1673_);
lean_dec(v___x_1644_);
lean_dec_ref(v___x_1643_);
lean_dec_ref(v___x_1639_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1645_);
lean_ctor_set(v___x_1703_, 1, v___x_1665_);
v___x_1704_ = lean_task_pure(v___x_1703_);
return v___x_1704_;
}
}
v___jp_1707_:
{
lean_object* v___x_1709_; lean_object* v_env_1710_; lean_object* v_nextMacroScope_1711_; lean_object* v_ngen_1712_; lean_object* v_auxDeclNGen_1713_; lean_object* v_traceState_1714_; lean_object* v_recordedDeps_1715_; lean_object* v_messages_1716_; lean_object* v_infoState_1717_; lean_object* v_snapshotTasks_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v___x_1709_ = lean_st_ref_take(v___x_1673_);
v_env_1710_ = lean_ctor_get(v___x_1709_, 0);
v_nextMacroScope_1711_ = lean_ctor_get(v___x_1709_, 1);
v_ngen_1712_ = lean_ctor_get(v___x_1709_, 2);
v_auxDeclNGen_1713_ = lean_ctor_get(v___x_1709_, 3);
v_traceState_1714_ = lean_ctor_get(v___x_1709_, 4);
v_recordedDeps_1715_ = lean_ctor_get(v___x_1709_, 6);
v_messages_1716_ = lean_ctor_get(v___x_1709_, 7);
v_infoState_1717_ = lean_ctor_get(v___x_1709_, 8);
v_snapshotTasks_1718_ = lean_ctor_get(v___x_1709_, 9);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1709_, 5);
lean_dec(v_unused_1728_);
v___x_1720_ = v___x_1709_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snapshotTasks_1718_);
lean_inc(v_infoState_1717_);
lean_inc(v_messages_1716_);
lean_inc(v_recordedDeps_1715_);
lean_inc(v_traceState_1714_);
lean_inc(v_auxDeclNGen_1713_);
lean_inc(v_ngen_1712_);
lean_inc(v_nextMacroScope_1711_);
lean_inc(v_env_1710_);
lean_dec(v___x_1709_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_Kernel_enableDiag(v_env_1710_, v___y_1708_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 5, v___x_1664_);
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_nextMacroScope_1711_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_ngen_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_auxDeclNGen_1713_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_traceState_1714_);
lean_ctor_set(v_reuseFailAlloc_1726_, 5, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1726_, 6, v_recordedDeps_1715_);
lean_ctor_set(v_reuseFailAlloc_1726_, 7, v_messages_1716_);
lean_ctor_set(v_reuseFailAlloc_1726_, 8, v_infoState_1717_);
lean_ctor_set(v_reuseFailAlloc_1726_, 9, v_snapshotTasks_1718_);
v___x_1724_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_st_ref_put(v___x_1673_, v___x_1724_);
lean_inc(v___x_1634_);
lean_inc(v___x_1633_);
lean_inc_ref(v_fileMap_1653_);
lean_inc_ref(v_fileName_1652_);
v_fileName_1675_ = v_fileName_1652_;
v_fileMap_1676_ = v_fileMap_1653_;
v_currNamespace_1677_ = v___x_1633_;
v_openDecls_1678_ = v___x_1654_;
v_initHeartbeats_1679_ = v___x_1634_;
v_maxHeartbeats_1680_ = v___x_1655_;
v_quotContext_1681_ = v___x_1633_;
v_currMacroScope_1682_ = v___x_1656_;
v_cancelTk_x3f_1683_ = v___x_1647_;
v_inheritedTraceOptions_1684_ = v___x_1705_;
v_currRecDepth_1685_ = v___x_1634_;
v_ref_1686_ = v___x_1657_;
v_suppressElabErrors_1687_ = v_val_1642_;
v_isRecordingDeps_1688_ = v_val_1642_;
goto v___jp_1674_;
}
}
}
v___jp_1729_:
{
if (v___y_1731_ == 0)
{
v___y_1708_ = v___y_1730_;
goto v___jp_1707_;
}
else
{
lean_inc(v___x_1634_);
lean_inc(v___x_1633_);
lean_inc_ref(v_fileMap_1653_);
lean_inc_ref(v_fileName_1652_);
v_fileName_1675_ = v_fileName_1652_;
v_fileMap_1676_ = v_fileMap_1653_;
v_currNamespace_1677_ = v___x_1633_;
v_openDecls_1678_ = v___x_1654_;
v_initHeartbeats_1679_ = v___x_1634_;
v_maxHeartbeats_1680_ = v___x_1655_;
v_quotContext_1681_ = v___x_1633_;
v_currMacroScope_1682_ = v___x_1656_;
v_cancelTk_x3f_1683_ = v___x_1647_;
v_inheritedTraceOptions_1684_ = v___x_1705_;
v_currRecDepth_1685_ = v___x_1634_;
v_ref_1686_ = v___x_1657_;
v_suppressElabErrors_1687_ = v_val_1642_;
v_isRecordingDeps_1688_ = v_val_1642_;
goto v___jp_1674_;
}
}
v___jp_1734_:
{
if (v___x_1733_ == 0)
{
v___y_1730_ = v___y_1735_;
v___y_1731_ = v___x_1648_;
goto v___jp_1729_;
}
else
{
v___y_1708_ = v___y_1735_;
goto v___jp_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1740_ = _args[0];
lean_object* v_opts_1741_ = _args[1];
lean_object* v___x_1742_ = _args[2];
lean_object* v___x_1743_ = _args[3];
lean_object* v___x_1744_ = _args[4];
lean_object* v___x_1745_ = _args[5];
lean_object* v___x_1746_ = _args[6];
lean_object* v_env_1747_ = _args[7];
lean_object* v___x_1748_ = _args[8];
lean_object* v___x_1749_ = _args[9];
lean_object* v_pos_1750_ = _args[10];
lean_object* v_val_1751_ = _args[11];
lean_object* v___x_1752_ = _args[12];
lean_object* v___x_1753_ = _args[13];
lean_object* v___x_1754_ = _args[14];
lean_object* v___x_1755_ = _args[15];
lean_object* v___x_1756_ = _args[16];
lean_object* v___x_1757_ = _args[17];
lean_object* v_x_1758_ = _args[18];
lean_object* v___y_1759_ = _args[19];
_start:
{
size_t v___x_36699__boxed_1760_; uint8_t v___x_36700__boxed_1761_; uint8_t v_val_36703__boxed_1762_; uint8_t v___x_36709__boxed_1763_; lean_object* v_res_1764_; 
v___x_36699__boxed_1760_ = lean_unbox_usize(v___x_1745_);
lean_dec(v___x_1745_);
v___x_36700__boxed_1761_ = lean_unbox(v___x_1746_);
v_val_36703__boxed_1762_ = lean_unbox(v_val_1751_);
v___x_36709__boxed_1763_ = lean_unbox(v___x_1757_);
v_res_1764_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1740_, v_opts_1741_, v___x_1742_, v___x_1743_, v___x_1744_, v___x_36699__boxed_1760_, v___x_36700__boxed_1761_, v_env_1747_, v___x_1748_, v___x_1749_, v_pos_1750_, v_val_36703__boxed_1762_, v___x_1752_, v___x_1753_, v___x_1754_, v___x_1755_, v___x_1756_, v___x_36709__boxed_1763_, v_x_1758_);
lean_dec(v___x_1755_);
lean_dec(v_pos_1750_);
lean_dec(v___x_1744_);
lean_dec_ref(v_a_1740_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1765_, lean_object* v___x_1766_, lean_object* v_parserState_1767_, lean_object* v_x_1768_){
_start:
{
lean_object* v_toProcessingContext_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_toProcessingContext_1769_ = lean_ctor_get(v_a_1765_, 0);
v___x_1770_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1769_);
v___x_1771_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1769_, v___x_1766_, v_parserState_1767_, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1772_, lean_object* v___x_1773_, lean_object* v_parserState_1774_, lean_object* v_x_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1772_, v___x_1773_, v_parserState_1774_, v_x_1775_);
lean_dec_ref(v_a_1772_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1778_, size_t v_i_1779_, size_t v_stop_1780_, lean_object* v_b_1781_){
_start:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_usize_dec_eq(v_i_1779_, v_stop_1780_);
if (v___x_1783_ == 0)
{
lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; size_t v___x_1787_; size_t v___x_1788_; 
v___f_1784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1785_ = lean_array_uget_borrowed(v_as_1778_, v_i_1779_);
lean_inc(v___x_1785_);
v___x_1786_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1784_, v___x_1785_);
v___x_1787_ = ((size_t)1ULL);
v___x_1788_ = lean_usize_add(v_i_1779_, v___x_1787_);
v_i_1779_ = v___x_1788_;
v_b_1781_ = v___x_1786_;
goto _start;
}
else
{
return v_b_1781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1790_, lean_object* v_i_1791_, lean_object* v_stop_1792_, lean_object* v_b_1793_, lean_object* v___y_1794_){
_start:
{
size_t v_i_boxed_1795_; size_t v_stop_boxed_1796_; lean_object* v_res_1797_; 
v_i_boxed_1795_ = lean_unbox_usize(v_i_1791_);
lean_dec(v_i_1791_);
v_stop_boxed_1796_ = lean_unbox_usize(v_stop_1792_);
lean_dec(v_stop_1792_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1790_, v_i_boxed_1795_, v_stop_boxed_1796_, v_b_1793_);
lean_dec_ref(v_as_1790_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1798_, lean_object* v_stx_1799_, lean_object* v_revCmds_1800_, lean_object* v_newParserState_1801_, lean_object* v_val_1802_, lean_object* v_sync_1803_, lean_object* v_val_1804_, lean_object* v_a_1805_, lean_object* v_oldNext_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v_sync_boxed_1808_; lean_object* v_res_1809_; 
v_sync_boxed_1808_ = lean_unbox(v_sync_1803_);
v_res_1809_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1798_, v_stx_1799_, v_revCmds_1800_, v_newParserState_1801_, v_val_1802_, v_sync_boxed_1808_, v_val_1804_, v_a_1805_, v_oldNext_1806_);
lean_dec_ref(v_a_1805_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1810_, lean_object* v_stx_1811_, lean_object* v_revCmds_1812_, lean_object* v_newParserState_1813_, lean_object* v_val_1814_, uint8_t v_sync_1815_, lean_object* v_val_1816_, lean_object* v_a_1817_, lean_object* v_oldResult_1818_){
_start:
{
lean_object* v_task_1820_; lean_object* v___x_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; 
v_task_1820_ = lean_ctor_get(v_val_1810_, 3);
lean_inc_ref(v_task_1820_);
lean_dec_ref(v_val_1810_);
v___x_1821_ = lean_box(v_sync_1815_);
lean_inc_ref(v_a_1817_);
v___f_1822_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1822_, 0, v_oldResult_1818_);
lean_closure_set(v___f_1822_, 1, v_stx_1811_);
lean_closure_set(v___f_1822_, 2, v_revCmds_1812_);
lean_closure_set(v___f_1822_, 3, v_newParserState_1813_);
lean_closure_set(v___f_1822_, 4, v_val_1814_);
lean_closure_set(v___f_1822_, 5, v___x_1821_);
lean_closure_set(v___f_1822_, 6, v_val_1816_);
lean_closure_set(v___f_1822_, 7, v_a_1817_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = 1;
v___x_1825_ = l_BaseIO_chainTask___redArg(v_task_1820_, v___f_1822_, v___x_1823_, v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1826_, lean_object* v_stx_1827_, lean_object* v_revCmds_1828_, lean_object* v_newParserState_1829_, lean_object* v_val_1830_, lean_object* v_sync_1831_, lean_object* v_val_1832_, lean_object* v_a_1833_, lean_object* v_oldResult_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v_sync_boxed_1836_; lean_object* v_res_1837_; 
v_sync_boxed_1836_ = lean_unbox(v_sync_1831_);
v_res_1837_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1826_, v_stx_1827_, v_revCmds_1828_, v_newParserState_1829_, v_val_1830_, v_sync_boxed_1836_, v_val_1832_, v_a_1833_, v_oldResult_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1837_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1846_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1847_ = l_Lean_Name_append(v___x_1846_, v___x_1845_);
return v___x_1847_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1851_, lean_object* v_val_1852_, lean_object* v_fst_1853_, lean_object* v_revCmds_1854_, lean_object* v_fst_1855_, uint8_t v_val_1856_, lean_object* v_a_1857_, lean_object* v_snd_1858_, lean_object* v___x_1859_, uint8_t v___x_1860_, lean_object* v_fst_1861_, lean_object* v_val_1862_, lean_object* v_val_1863_, lean_object* v___x_1864_, lean_object* v___f_1865_, lean_object* v___f_1866_, lean_object* v___f_1867_, lean_object* v_pos_1868_, lean_object* v_cmdState_1869_, lean_object* v_val_1870_, lean_object* v___x_1871_, lean_object* v_opts_1872_, lean_object* v___x_1873_, lean_object* v_snd_1874_, lean_object* v_prom_1875_, lean_object* v_old_x3f_1876_, lean_object* v_parseCancelTk_1877_, lean_object* v_next_x3f_1878_){
_start:
{
lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_snapshotTasks_1886_; lean_object* v_traceTask_1887_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; size_t v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v_env_1931_; lean_object* v_messages_1932_; lean_object* v_scopes_1933_; lean_object* v_infoState_1934_; lean_object* v_traceState_1935_; lean_object* v_snapshotTasks_1936_; lean_object* v_codeQualityEntryTasks_1937_; lean_object* v_reportedCmdState_1938_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; size_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v_reportedCmdState_1995_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; size_t v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2053_; 
if (lean_obj_tag(v_next_x3f_1878_) == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v_parseCancelTk_1877_);
v___x_2106_ = lean_box(0);
v___y_2053_ = v___x_2106_;
goto v___jp_2052_;
}
else
{
lean_object* v_toProcessingContext_2107_; lean_object* v_val_2108_; lean_object* v_pos_2109_; lean_object* v_endPos_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_toProcessingContext_2107_ = lean_ctor_get(v_a_1857_, 0);
v_val_2108_ = lean_ctor_get(v_next_x3f_1878_, 0);
v_pos_2109_ = lean_ctor_get(v_fst_1855_, 0);
v_endPos_2110_ = lean_ctor_get(v_toProcessingContext_2107_, 3);
v___x_2111_ = lean_box(0);
lean_inc(v_endPos_2110_);
lean_inc(v_pos_2109_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_pos_2109_);
lean_ctor_set(v___x_2112_, 1, v_endPos_2110_);
v___x_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_parseCancelTk_1877_);
v___x_2115_ = l_IO_Promise_result_x21___redArg(v_val_2108_);
v___x_2116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2111_);
lean_ctor_set(v___x_2116_, 1, v___x_2113_);
lean_ctor_set(v___x_2116_, 2, v___x_2114_);
lean_ctor_set(v___x_2116_, 3, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___y_2053_ = v___x_2117_;
goto v___jp_2052_;
}
v___jp_1880_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1888_, 0, v___y_1883_);
lean_ctor_set(v___x_1888_, 1, v___x_1851_);
lean_ctor_set(v___x_1888_, 2, v___y_1881_);
lean_ctor_set(v___x_1888_, 3, v_traceTask_1887_);
v___x_1889_ = lean_array_push(v_snapshotTasks_1886_, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___y_1882_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_io_promise_resolve(v___x_1890_, v_val_1852_);
if (lean_obj_tag(v_next_x3f_1878_) == 1)
{
lean_object* v_val_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_val_1892_ = lean_ctor_get(v_next_x3f_1878_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v_next_x3f_1878_, 1);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_fst_1853_);
lean_ctor_set(v___x_1894_, 1, v_revCmds_1854_);
v___x_1895_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1893_, v_fst_1855_, v___y_1885_, v_val_1892_, v_val_1856_, v___y_1884_, v___x_1894_, v_a_1857_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; 
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v_next_x3f_1878_);
lean_dec_ref(v_fst_1855_);
lean_dec(v_revCmds_1854_);
lean_dec(v_fst_1853_);
v___x_1896_ = lean_box(0);
return v___x_1896_;
}
}
v___jp_1897_:
{
lean_object* v_snapshotTasks_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_snapshotTasks_1904_ = lean_ctor_get(v___y_1903_, 10);
lean_inc_ref(v_snapshotTasks_1904_);
v___x_1905_ = lean_mk_empty_array_with_capacity(v___y_1902_);
lean_dec(v___y_1902_);
lean_inc_ref(v___y_1900_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___y_1900_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_task_pure(v___x_1906_);
v___y_1881_ = v___y_1898_;
v___y_1882_ = v___y_1900_;
v___y_1883_ = v___y_1899_;
v___y_1884_ = v___y_1901_;
v___y_1885_ = v___y_1903_;
v_snapshotTasks_1886_ = v_snapshotTasks_1904_;
v_traceTask_1887_ = v___x_1907_;
goto v___jp_1880_;
}
v___jp_1908_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_opts_1948_; uint8_t v_hasTrace_1949_; 
v___x_1939_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1932_);
v___x_1940_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1940_, 0, v___y_1918_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
lean_ctor_set(v___x_1940_, 2, v___y_1919_);
lean_ctor_set(v___x_1940_, 3, v_traceState_1935_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*4, v_val_1856_);
v___x_1941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v_reportedCmdState_1938_);
lean_ctor_set(v___x_1941_, 2, v_codeQualityEntryTasks_1937_);
v___x_1942_ = lean_io_promise_resolve(v___x_1941_, v_val_1863_);
v___x_1943_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1934_);
lean_inc(v___y_1922_);
v___x_1944_ = l_BaseIO_chainTask___redArg(v___x_1943_, v___y_1921_, v___y_1922_, v___x_1860_);
v___x_1945_ = l_Lean_inheritedTraceOptions;
v___x_1946_ = lean_st_ref_get(v___x_1945_);
v___x_1947_ = l_List_head_x21___redArg(v___x_1864_, v_scopes_1933_);
lean_dec(v_scopes_1933_);
lean_dec_ref(v___x_1864_);
v_opts_1948_ = lean_ctor_get(v___x_1947_, 1);
lean_inc_ref(v_opts_1948_);
lean_dec(v___x_1947_);
v_hasTrace_1949_ = lean_ctor_get_uint8(v_opts_1948_, sizeof(void*)*1);
if (v_hasTrace_1949_ == 0)
{
lean_dec_ref(v_opts_1948_);
lean_dec(v___x_1946_);
lean_dec_ref(v_snapshotTasks_1936_);
lean_dec_ref(v_env_1931_);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec(v_pos_1868_);
lean_dec_ref(v___f_1867_);
lean_dec_ref(v___f_1866_);
lean_dec_ref(v___f_1865_);
lean_dec(v___x_1859_);
v___y_1898_ = v___y_1925_;
v___y_1899_ = v___y_1926_;
v___y_1900_ = v___y_1917_;
v___y_1901_ = v___y_1920_;
v___y_1902_ = v___y_1922_;
v___y_1903_ = v___y_1930_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1946_, v_opts_1948_, v___x_1950_);
lean_dec(v___x_1946_);
if (v___x_1951_ == 0)
{
lean_dec_ref(v_opts_1948_);
lean_dec_ref(v_snapshotTasks_1936_);
lean_dec_ref(v_env_1931_);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec(v_pos_1868_);
lean_dec_ref(v___f_1867_);
lean_dec_ref(v___f_1866_);
lean_dec_ref(v___f_1865_);
lean_dec(v___x_1859_);
v___y_1898_ = v___y_1925_;
v___y_1899_ = v___y_1926_;
v___y_1900_ = v___y_1917_;
v___y_1901_ = v___y_1920_;
v___y_1902_ = v___y_1922_;
v___y_1903_ = v___y_1930_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___f_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_inc_n(v___y_1922_, 3);
v___x_1952_ = lean_task_map(v___f_1865_, v___y_1929_, v___y_1922_, v___x_1860_);
lean_inc_n(v___y_1925_, 3);
lean_inc_n(v___y_1923_, 2);
lean_inc_n(v___y_1924_, 2);
v___x_1953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1953_, 0, v___y_1924_);
lean_ctor_set(v___x_1953_, 1, v___y_1923_);
lean_ctor_set(v___x_1953_, 2, v___y_1925_);
lean_ctor_set(v___x_1953_, 3, v___x_1952_);
v___x_1954_ = lean_task_map(v___f_1866_, v___y_1928_, v___y_1922_, v___x_1860_);
v___x_1955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1955_, 0, v___y_1924_);
lean_ctor_set(v___x_1955_, 1, v___y_1923_);
lean_ctor_set(v___x_1955_, 2, v___y_1925_);
lean_ctor_set(v___x_1955_, 3, v___x_1954_);
v___x_1956_ = lean_task_map(v___f_1867_, v___y_1927_, v___y_1922_, v___x_1860_);
v___x_1957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1957_, 0, v___y_1924_);
lean_ctor_set(v___x_1957_, 1, v___y_1923_);
lean_ctor_set(v___x_1957_, 2, v___y_1925_);
lean_ctor_set(v___x_1957_, 3, v___x_1956_);
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = lean_mk_empty_array_with_capacity(v___x_1958_);
v___x_1960_ = lean_array_push(v___x_1959_, v___x_1953_);
v___x_1961_ = lean_array_push(v___x_1960_, v___x_1955_);
v___x_1962_ = lean_array_push(v___x_1961_, v___x_1957_);
v___x_1963_ = l_Array_append___redArg(v___x_1962_, v_snapshotTasks_1936_);
lean_inc_ref(v___y_1917_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___y_1917_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_box_usize(v___y_1912_);
v___x_1966_ = lean_box(v___x_1860_);
v___x_1967_ = lean_box(v_val_1856_);
v___x_1968_ = lean_box(v___x_1951_);
lean_inc_ref(v___x_1964_);
lean_inc_ref(v___y_1913_);
lean_inc_ref(v_a_1857_);
v___f_1969_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1969_, 0, v_a_1857_);
lean_closure_set(v___f_1969_, 1, v_opts_1948_);
lean_closure_set(v___f_1969_, 2, v___x_1859_);
lean_closure_set(v___f_1969_, 3, v___y_1910_);
lean_closure_set(v___f_1969_, 4, v___y_1915_);
lean_closure_set(v___f_1969_, 5, v___x_1965_);
lean_closure_set(v___f_1969_, 6, v___x_1966_);
lean_closure_set(v___f_1969_, 7, v_env_1931_);
lean_closure_set(v___f_1969_, 8, v___y_1913_);
lean_closure_set(v___f_1969_, 9, v___x_1964_);
lean_closure_set(v___f_1969_, 10, v_pos_1868_);
lean_closure_set(v___f_1969_, 11, v___x_1967_);
lean_closure_set(v___f_1969_, 12, v___y_1916_);
lean_closure_set(v___f_1969_, 13, v___y_1909_);
lean_closure_set(v___f_1969_, 14, v___y_1914_);
lean_closure_set(v___f_1969_, 15, v___x_1945_);
lean_closure_set(v___f_1969_, 16, v___y_1911_);
lean_closure_set(v___f_1969_, 17, v___x_1968_);
v___x_1970_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1964_);
v___x_1971_ = lean_io_bind_task(v___x_1970_, v___f_1969_, v___y_1922_, v_val_1856_);
v___y_1881_ = v___y_1925_;
v___y_1882_ = v___y_1917_;
v___y_1883_ = v___y_1926_;
v___y_1884_ = v___y_1920_;
v___y_1885_ = v___y_1930_;
v_snapshotTasks_1886_ = v_snapshotTasks_1936_;
v_traceTask_1887_ = v___x_1971_;
goto v___jp_1880_;
}
}
}
v___jp_1972_:
{
lean_object* v_env_1996_; lean_object* v_messages_1997_; lean_object* v_scopes_1998_; lean_object* v_infoState_1999_; lean_object* v_traceState_2000_; lean_object* v_snapshotTasks_2001_; lean_object* v_codeQualityEntryTasks_2002_; 
v_env_1996_ = lean_ctor_get(v___y_1994_, 0);
lean_inc_ref(v_env_1996_);
v_messages_1997_ = lean_ctor_get(v___y_1994_, 1);
lean_inc_ref(v_messages_1997_);
v_scopes_1998_ = lean_ctor_get(v___y_1994_, 2);
lean_inc(v_scopes_1998_);
v_infoState_1999_ = lean_ctor_get(v___y_1994_, 8);
lean_inc_ref(v_infoState_1999_);
v_traceState_2000_ = lean_ctor_get(v___y_1994_, 9);
lean_inc_ref(v_traceState_2000_);
v_snapshotTasks_2001_ = lean_ctor_get(v___y_1994_, 10);
lean_inc_ref(v_snapshotTasks_2001_);
v_codeQualityEntryTasks_2002_ = lean_ctor_get(v___y_1994_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2002_);
v___y_1909_ = v___y_1973_;
v___y_1910_ = v___y_1974_;
v___y_1911_ = v___y_1975_;
v___y_1912_ = v___y_1976_;
v___y_1913_ = v___y_1977_;
v___y_1914_ = v___y_1979_;
v___y_1915_ = v___y_1978_;
v___y_1916_ = v___y_1980_;
v___y_1917_ = v___y_1981_;
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
v___y_1928_ = v___y_1992_;
v___y_1929_ = v___y_1993_;
v___y_1930_ = v___y_1994_;
v_env_1931_ = v_env_1996_;
v_messages_1932_ = v_messages_1997_;
v_scopes_1933_ = v_scopes_1998_;
v_infoState_1934_ = v_infoState_1999_;
v_traceState_1935_ = v_traceState_2000_;
v_snapshotTasks_1936_ = v_snapshotTasks_2001_;
v_codeQualityEntryTasks_1937_ = v_codeQualityEntryTasks_2002_;
v_reportedCmdState_1938_ = v_reportedCmdState_1995_;
goto v___jp_1908_;
}
v___jp_2003_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___f_2024_; uint8_t v___x_2025_; 
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2019_);
lean_ctor_set(v___x_2020_, 1, v_val_1862_);
lean_inc_ref(v___y_2014_);
lean_inc_n(v_pos_1868_, 2);
lean_inc(v_revCmds_1854_);
lean_inc(v_fst_1853_);
v___x_2021_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1853_, v_revCmds_1854_, v_cmdState_1869_, v_pos_1868_, v___x_2020_, v___y_2014_, v_a_1857_);
v___x_2022_ = lean_box(v_val_1856_);
v___x_2023_ = lean_box(v___x_1860_);
lean_inc_ref(v_a_1857_);
lean_inc(v___y_2005_);
lean_inc_ref(v___x_1864_);
lean_inc_ref(v___x_2021_);
lean_inc_ref(v___y_2009_);
lean_inc_ref(v___y_2015_);
v___f_2024_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2024_, 0, v___y_2015_);
lean_closure_set(v___f_2024_, 1, v___y_2009_);
lean_closure_set(v___f_2024_, 2, v___x_2022_);
lean_closure_set(v___f_2024_, 3, v_val_1870_);
lean_closure_set(v___f_2024_, 4, v___x_2021_);
lean_closure_set(v___f_2024_, 5, v___x_1864_);
lean_closure_set(v___f_2024_, 6, v___y_2005_);
lean_closure_set(v___f_2024_, 7, v___x_2023_);
lean_closure_set(v___f_2024_, 8, v_a_1857_);
lean_closure_set(v___f_2024_, 9, v_pos_1868_);
lean_closure_set(v___f_2024_, 10, v___x_1871_);
v___x_2025_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1872_, v___x_1873_);
if (v___x_2025_ == 0)
{
lean_inc_ref(v___x_2021_);
lean_inc_ref(v___y_2015_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc(v___y_2004_);
v___y_1973_ = v___y_2004_;
v___y_1974_ = v___y_2005_;
v___y_1975_ = v___y_2006_;
v___y_1976_ = v___y_2007_;
v___y_1977_ = v___y_2009_;
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2011_;
v___y_1980_ = v___y_2015_;
v___y_1981_ = v___y_2011_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2004_;
v___y_1984_ = v___y_2014_;
v___y_1985_ = v___f_2024_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2008_;
v___y_1988_ = v___y_2012_;
v___y_1989_ = v___y_2006_;
v___y_1990_ = v___y_2016_;
v___y_1991_ = v___y_2017_;
v___y_1992_ = v___y_2018_;
v___y_1993_ = v___y_2013_;
v___y_1994_ = v___x_2021_;
v_reportedCmdState_1995_ = v___x_2021_;
goto v___jp_1972_;
}
else
{
uint8_t v___x_2026_; 
lean_inc(v_fst_1853_);
v___x_2026_ = l_Lean_Parser_isTerminalCommand(v_fst_1853_);
if (v___x_2026_ == 0)
{
if (v___x_2025_ == 0)
{
lean_inc_ref(v___x_2021_);
lean_inc_ref(v___y_2015_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc(v___y_2004_);
v___y_1973_ = v___y_2004_;
v___y_1974_ = v___y_2005_;
v___y_1975_ = v___y_2006_;
v___y_1976_ = v___y_2007_;
v___y_1977_ = v___y_2009_;
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2011_;
v___y_1980_ = v___y_2015_;
v___y_1981_ = v___y_2011_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2004_;
v___y_1984_ = v___y_2014_;
v___y_1985_ = v___f_2024_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2008_;
v___y_1988_ = v___y_2012_;
v___y_1989_ = v___y_2006_;
v___y_1990_ = v___y_2016_;
v___y_1991_ = v___y_2017_;
v___y_1992_ = v___y_2018_;
v___y_1993_ = v___y_2013_;
v___y_1994_ = v___x_2021_;
v_reportedCmdState_1995_ = v___x_2021_;
goto v___jp_1972_;
}
else
{
lean_object* v_env_2027_; lean_object* v_messages_2028_; lean_object* v_scopes_2029_; lean_object* v_infoState_2030_; lean_object* v_traceState_2031_; lean_object* v_snapshotTasks_2032_; lean_object* v_codeQualityEntryTasks_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_env_2027_ = lean_ctor_get(v___x_2021_, 0);
lean_inc_ref_n(v_env_2027_, 2);
v_messages_2028_ = lean_ctor_get(v___x_2021_, 1);
lean_inc_ref(v_messages_2028_);
v_scopes_2029_ = lean_ctor_get(v___x_2021_, 2);
lean_inc(v_scopes_2029_);
v_infoState_2030_ = lean_ctor_get(v___x_2021_, 8);
lean_inc_ref(v_infoState_2030_);
v_traceState_2031_ = lean_ctor_get(v___x_2021_, 9);
lean_inc_ref(v_traceState_2031_);
v_snapshotTasks_2032_ = lean_ctor_get(v___x_2021_, 10);
lean_inc_ref(v_snapshotTasks_2032_);
v_codeQualityEntryTasks_2033_ = lean_ctor_get(v___x_2021_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2033_);
v___x_2034_ = lean_mk_empty_array_with_capacity(v___y_2010_);
lean_inc_ref(v___x_2034_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_inc_n(v___y_2005_, 4);
v___x_2036_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2034_);
lean_ctor_set(v___x_2036_, 2, v___y_2005_);
lean_ctor_set(v___x_2036_, 3, v___y_2005_);
lean_ctor_set_usize(v___x_2036_, 4, v___y_2007_);
v___x_2037_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2036_, 2);
v___x_2038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
lean_ctor_set(v___x_2038_, 2, v___x_2037_);
v___x_2039_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2040_ = l_Lean_Options_empty;
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_mk_empty_array_with_capacity(v___y_2005_);
lean_inc_ref_n(v___x_2042_, 3);
lean_inc_n(v___x_1859_, 2);
v___x_2043_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2043_, 0, v___x_2039_);
lean_ctor_set(v___x_2043_, 1, v___x_2040_);
lean_ctor_set(v___x_2043_, 2, v___x_1859_);
lean_ctor_set(v___x_2043_, 3, v___x_2041_);
lean_ctor_set(v___x_2043_, 4, v___x_2041_);
lean_ctor_set(v___x_2043_, 5, v___x_2042_);
lean_ctor_set(v___x_2043_, 6, v___x_2042_);
lean_ctor_set(v___x_2043_, 7, v___x_2041_);
lean_ctor_set(v___x_2043_, 8, v___x_2041_);
lean_ctor_set(v___x_2043_, 9, v___x_2041_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*10, v_val_1856_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*10 + 1, v_val_1856_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*10 + 2, v_val_1856_);
v___x_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2041_);
v___x_2045_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2046_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2047_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1859_);
v___x_2048_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2049_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
lean_ctor_set(v___x_2049_, 2, v___x_2036_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*3, v___x_1860_);
v___x_2050_ = lean_box(0);
lean_inc_ref(v___y_2009_);
v___x_2051_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2051_, 0, v_env_2027_);
lean_ctor_set(v___x_2051_, 1, v___x_2038_);
lean_ctor_set(v___x_2051_, 2, v___x_2044_);
lean_ctor_set(v___x_2051_, 3, v___x_2037_);
lean_ctor_set(v___x_2051_, 4, v___x_2045_);
lean_ctor_set(v___x_2051_, 5, v___y_2005_);
lean_ctor_set(v___x_2051_, 6, v___x_2046_);
lean_ctor_set(v___x_2051_, 7, v___x_2047_);
lean_ctor_set(v___x_2051_, 8, v___x_2049_);
lean_ctor_set(v___x_2051_, 9, v___y_2009_);
lean_ctor_set(v___x_2051_, 10, v___x_2042_);
lean_ctor_set(v___x_2051_, 11, v___x_2050_);
lean_ctor_set(v___x_2051_, 12, v___x_2042_);
lean_inc_ref(v___y_2015_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2006_);
lean_inc(v___y_2004_);
v___y_1909_ = v___y_2004_;
v___y_1910_ = v___y_2005_;
v___y_1911_ = v___y_2006_;
v___y_1912_ = v___y_2007_;
v___y_1913_ = v___y_2009_;
v___y_1914_ = v___y_2011_;
v___y_1915_ = v___y_2010_;
v___y_1916_ = v___y_2015_;
v___y_1917_ = v___y_2011_;
v___y_1918_ = v___y_2015_;
v___y_1919_ = v___y_2004_;
v___y_1920_ = v___y_2014_;
v___y_1921_ = v___f_2024_;
v___y_1922_ = v___y_2005_;
v___y_1923_ = v___y_2008_;
v___y_1924_ = v___y_2012_;
v___y_1925_ = v___y_2006_;
v___y_1926_ = v___y_2016_;
v___y_1927_ = v___y_2017_;
v___y_1928_ = v___y_2018_;
v___y_1929_ = v___y_2013_;
v___y_1930_ = v___x_2021_;
v_env_1931_ = v_env_2027_;
v_messages_1932_ = v_messages_2028_;
v_scopes_1933_ = v_scopes_2029_;
v_infoState_1934_ = v_infoState_2030_;
v_traceState_1935_ = v_traceState_2031_;
v_snapshotTasks_1936_ = v_snapshotTasks_2032_;
v_codeQualityEntryTasks_1937_ = v_codeQualityEntryTasks_2033_;
v_reportedCmdState_1938_ = v___x_2051_;
goto v___jp_1908_;
}
}
else
{
lean_inc_ref(v___x_2021_);
lean_inc_ref(v___y_2015_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc(v___y_2004_);
v___y_1973_ = v___y_2004_;
v___y_1974_ = v___y_2005_;
v___y_1975_ = v___y_2006_;
v___y_1976_ = v___y_2007_;
v___y_1977_ = v___y_2009_;
v___y_1978_ = v___y_2010_;
v___y_1979_ = v___y_2011_;
v___y_1980_ = v___y_2015_;
v___y_1981_ = v___y_2011_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2004_;
v___y_1984_ = v___y_2014_;
v___y_1985_ = v___f_2024_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2008_;
v___y_1988_ = v___y_2012_;
v___y_1989_ = v___y_2006_;
v___y_1990_ = v___y_2016_;
v___y_1991_ = v___y_2017_;
v___y_1992_ = v___y_2018_;
v___y_1993_ = v___y_2013_;
v___y_1994_ = v___x_2021_;
v_reportedCmdState_1995_ = v___x_2021_;
goto v___jp_1972_;
}
}
}
v___jp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2054_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1858_);
v___x_2055_ = l_IO_CancelToken_new();
v___x_2056_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1859_);
v___x_2057_ = l_Lean_Name_str___override(v___x_1859_, v___x_2056_);
v___x_2058_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2059_ = l_Lean_Name_str___override(v___x_2057_, v___x_2058_);
v___x_2060_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2061_ = l_Lean_Name_str___override(v___x_2059_, v___x_2060_);
v___x_2062_ = l_Lean_Name_str___override(v___x_2061_, v___x_2058_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = l_Lean_Name_num___override(v___x_2062_, v___x_2063_);
v___x_2065_ = l_Lean_Name_str___override(v___x_2064_, v___x_2058_);
v___x_2066_ = l_Lean_Name_str___override(v___x_2065_, v___x_2060_);
v___x_2067_ = l_Lean_Name_str___override(v___x_2066_, v___x_2058_);
v___x_2068_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2069_ = l_Lean_Name_str___override(v___x_2067_, v___x_2068_);
v___x_2070_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2071_ = l_Lean_Name_str___override(v___x_2069_, v___x_2070_);
v___x_2072_ = l_Lean_Name_toString(v___x_2071_, v___x_1860_);
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_unsigned_to_nat(32u);
v___x_2075_ = ((size_t)5ULL);
v___x_2076_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2072_, 2);
v___x_2077_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2077_, 0, v___x_2072_);
lean_ctor_set(v___x_2077_, 1, v___x_2054_);
lean_ctor_set(v___x_2077_, 2, v___x_2073_);
lean_ctor_set(v___x_2077_, 3, v___x_2076_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*4, v_val_1856_);
v___x_2078_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2079_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2079_, 0, v___x_2072_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
lean_ctor_set(v___x_2079_, 2, v___x_2073_);
lean_ctor_set(v___x_2079_, 3, v___x_2076_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*4, v_val_1856_);
lean_inc(v_fst_1861_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v_fst_1861_);
v___x_2081_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2080_);
lean_inc_ref(v___x_2055_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2055_);
v___x_2083_ = l_IO_Promise_result_x21___redArg(v_val_1862_);
lean_inc_ref(v___x_2083_);
lean_inc(v___x_2081_);
lean_inc_ref_n(v___x_2080_, 3);
v___x_2084_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2080_);
lean_ctor_set(v___x_2084_, 1, v___x_2081_);
lean_ctor_set(v___x_2084_, 2, v___x_2082_);
lean_ctor_set(v___x_2084_, 3, v___x_2083_);
v___x_2085_ = l_IO_Promise_result_x21___redArg(v_val_1863_);
lean_inc_ref(v___x_2085_);
lean_inc_n(v___x_1851_, 3);
v___x_2086_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2080_);
lean_ctor_set(v___x_2086_, 1, v___x_1851_);
lean_ctor_set(v___x_2086_, 2, v___x_2073_);
lean_ctor_set(v___x_2086_, 3, v___x_2085_);
v___x_2087_ = l_IO_Promise_result_x21___redArg(v_val_1870_);
lean_inc_ref(v___x_2087_);
v___x_2088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2080_);
lean_ctor_set(v___x_2088_, 1, v___x_1851_);
lean_ctor_set(v___x_2088_, 2, v___x_2073_);
lean_ctor_set(v___x_2088_, 3, v___x_2087_);
v___x_2089_ = l_IO_Promise_result_x21___redArg(v_val_1852_);
v___x_2090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2073_);
lean_ctor_set(v___x_2090_, 1, v___x_1851_);
lean_ctor_set(v___x_2090_, 2, v___x_2073_);
lean_ctor_set(v___x_2090_, 3, v___x_2089_);
lean_inc_ref(v___x_2079_);
v___x_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2079_);
lean_ctor_set(v___x_2091_, 1, v___x_2084_);
lean_ctor_set(v___x_2091_, 2, v___x_2086_);
lean_ctor_set(v___x_2091_, 3, v___x_2088_);
lean_ctor_set(v___x_2091_, 4, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2077_);
lean_ctor_set(v___x_2092_, 1, v_fst_1861_);
lean_ctor_set(v___x_2092_, 2, v_snd_1874_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
lean_ctor_set(v___x_2092_, 4, v___y_2053_);
v___x_2093_ = lean_io_promise_resolve(v___x_2092_, v_prom_1875_);
if (lean_obj_tag(v_old_x3f_1876_) == 0)
{
v___y_2004_ = v___x_2073_;
v___y_2005_ = v___x_2063_;
v___y_2006_ = v___x_2073_;
v___y_2007_ = v___x_2075_;
v___y_2008_ = v___x_2081_;
v___y_2009_ = v___x_2076_;
v___y_2010_ = v___x_2074_;
v___y_2011_ = v___x_2079_;
v___y_2012_ = v___x_2080_;
v___y_2013_ = v___x_2083_;
v___y_2014_ = v___x_2055_;
v___y_2015_ = v___x_2072_;
v___y_2016_ = v___x_2073_;
v___y_2017_ = v___x_2087_;
v___y_2018_ = v___x_2085_;
v___y_2019_ = v___x_2073_;
goto v___jp_2003_;
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2105_; 
v_val_2094_ = lean_ctor_get(v_old_x3f_1876_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_old_x3f_1876_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2096_ = v_old_x3f_1876_;
v_isShared_2097_ = v_isSharedCheck_2105_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v_old_x3f_1876_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2105_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_elabSnap_2098_; lean_object* v_stx_2099_; lean_object* v_elabSnap_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_elabSnap_2098_ = lean_ctor_get(v_val_2094_, 3);
lean_inc_ref(v_elabSnap_2098_);
v_stx_2099_ = lean_ctor_get(v_val_2094_, 1);
lean_inc(v_stx_2099_);
lean_dec(v_val_2094_);
v_elabSnap_2100_ = lean_ctor_get(v_elabSnap_2098_, 1);
lean_inc_ref(v_elabSnap_2100_);
lean_dec_ref(v_elabSnap_2098_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_stx_2099_);
lean_ctor_set(v___x_2101_, 1, v_elabSnap_2100_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2101_);
v___x_2103_ = v___x_2096_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
v___y_2004_ = v___x_2073_;
v___y_2005_ = v___x_2063_;
v___y_2006_ = v___x_2073_;
v___y_2007_ = v___x_2075_;
v___y_2008_ = v___x_2081_;
v___y_2009_ = v___x_2076_;
v___y_2010_ = v___x_2074_;
v___y_2011_ = v___x_2079_;
v___y_2012_ = v___x_2080_;
v___y_2013_ = v___x_2083_;
v___y_2014_ = v___x_2055_;
v___y_2015_ = v___x_2072_;
v___y_2016_ = v___x_2073_;
v___y_2017_ = v___x_2087_;
v___y_2018_ = v___x_2085_;
v___y_2019_ = v___x_2103_;
goto v___jp_2003_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2119_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2123_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_fst_2124_, lean_object* v_revCmds_2125_, lean_object* v_fst_2126_, uint8_t v_val_2127_, lean_object* v_a_2128_, lean_object* v_snd_2129_, lean_object* v___x_2130_, uint8_t v___x_2131_, lean_object* v___x_2132_, lean_object* v___f_2133_, lean_object* v___f_2134_, lean_object* v___f_2135_, lean_object* v_pos_2136_, lean_object* v_cmdState_2137_, lean_object* v___x_2138_, lean_object* v_opts_2139_, lean_object* v_prom_2140_, lean_object* v_old_x3f_2141_, lean_object* v_parseCancelTk_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v_snapshotTasks_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v_traceTask_2157_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; size_t v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v_env_2192_; lean_object* v_messages_2193_; lean_object* v_scopes_2194_; lean_object* v_infoState_2195_; lean_object* v_traceState_2196_; lean_object* v_snapshotTasks_2197_; lean_object* v_codeQualityEntryTasks_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v_reportedCmdState_2212_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; size_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v_reportedCmdState_2271_; lean_object* v___x_2279_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; size_t v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v_fst_2410_; lean_object* v_snd_2411_; uint8_t v___x_2423_; 
v___x_2144_ = lean_io_promise_new();
v___x_2145_ = lean_io_promise_new();
v___x_2146_ = lean_io_promise_new();
v___x_2147_ = lean_io_promise_new();
v___x_2279_ = l_Lean_internal_cmdlineSnapshots;
v___x_2423_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2139_, v___x_2279_);
if (v___x_2423_ == 0)
{
lean_inc_ref(v_fst_2126_);
lean_inc(v_fst_2124_);
v_fst_2410_ = v_fst_2124_;
v_snd_2411_ = v_fst_2126_;
goto v___jp_2409_;
}
else
{
uint8_t v___x_2424_; 
lean_inc(v_fst_2124_);
v___x_2424_ = l_Lean_Parser_isTerminalCommand(v_fst_2124_);
if (v___x_2424_ == 0)
{
if (v___x_2423_ == 0)
{
lean_inc_ref(v_fst_2126_);
lean_inc(v_fst_2124_);
v_fst_2410_ = v_fst_2124_;
v_snd_2411_ = v_fst_2126_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2410_ = v___x_2425_;
v_snd_2411_ = v___x_2426_;
goto v___jp_2409_;
}
}
else
{
lean_inc_ref(v_fst_2126_);
lean_inc(v_fst_2124_);
v_fst_2410_ = v_fst_2124_;
v_snd_2411_ = v_fst_2126_;
goto v___jp_2409_;
}
}
v___jp_2148_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2158_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2158_, 0, v___y_2153_);
lean_ctor_set(v___x_2158_, 1, v___y_2150_);
lean_ctor_set(v___x_2158_, 2, v___y_2154_);
lean_ctor_set(v___x_2158_, 3, v_traceTask_2157_);
v___x_2159_ = lean_array_push(v_snapshotTasks_2152_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___y_2155_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_io_promise_resolve(v___x_2160_, v___x_2147_);
lean_dec(v___x_2147_);
if (lean_obj_tag(v___y_2156_) == 1)
{
lean_object* v_val_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_val_2162_ = lean_ctor_get(v___y_2156_, 0);
lean_inc(v_val_2162_);
lean_dec_ref_known(v___y_2156_, 1);
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v_fst_2124_);
lean_ctor_set(v___x_2164_, 1, v_revCmds_2125_);
v___x_2165_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2163_, v_fst_2126_, v___y_2151_, v_val_2162_, v_val_2127_, v___y_2149_, v___x_2164_, v_a_2128_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2151_);
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_fst_2126_);
lean_dec(v_revCmds_2125_);
lean_dec(v_fst_2124_);
v___x_2166_ = lean_box(0);
return v___x_2166_;
}
}
v___jp_2167_:
{
lean_object* v_snapshotTasks_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_snapshotTasks_2176_ = lean_ctor_get(v___y_2171_, 10);
lean_inc_ref(v_snapshotTasks_2176_);
v___x_2177_ = lean_mk_empty_array_with_capacity(v___y_2169_);
lean_dec(v___y_2169_);
lean_inc_ref(v___y_2174_);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___y_2174_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_task_pure(v___x_2178_);
v___y_2149_ = v___y_2168_;
v___y_2150_ = v___y_2170_;
v___y_2151_ = v___y_2171_;
v_snapshotTasks_2152_ = v_snapshotTasks_2176_;
v___y_2153_ = v___y_2172_;
v___y_2154_ = v___y_2173_;
v___y_2155_ = v___y_2174_;
v___y_2156_ = v___y_2175_;
v_traceTask_2157_ = v___x_2179_;
goto v___jp_2148_;
}
v___jp_2180_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_opts_2222_; uint8_t v_hasTrace_2223_; 
v___x_2213_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2193_);
v___x_2214_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2214_, 0, v___y_2199_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
lean_ctor_set(v___x_2214_, 2, v___y_2210_);
lean_ctor_set(v___x_2214_, 3, v_traceState_2196_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*4, v_val_2127_);
v___x_2215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v_reportedCmdState_2212_);
lean_ctor_set(v___x_2215_, 2, v_codeQualityEntryTasks_2198_);
v___x_2216_ = lean_io_promise_resolve(v___x_2215_, v___x_2145_);
lean_dec(v___x_2145_);
v___x_2217_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2195_);
lean_inc(v___y_2189_);
v___x_2218_ = l_BaseIO_chainTask___redArg(v___x_2217_, v___y_2205_, v___y_2189_, v___x_2131_);
v___x_2219_ = l_Lean_inheritedTraceOptions;
v___x_2220_ = lean_st_ref_get(v___x_2219_);
v___x_2221_ = l_List_head_x21___redArg(v___x_2132_, v_scopes_2194_);
lean_dec(v_scopes_2194_);
lean_dec_ref(v___x_2132_);
v_opts_2222_ = lean_ctor_get(v___x_2221_, 1);
lean_inc_ref(v_opts_2222_);
lean_dec(v___x_2221_);
v_hasTrace_2223_ = lean_ctor_get_uint8(v_opts_2222_, sizeof(void*)*1);
if (v_hasTrace_2223_ == 0)
{
lean_dec_ref(v_opts_2222_);
lean_dec(v___x_2220_);
lean_dec(v___y_2209_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_snapshotTasks_2197_);
lean_dec_ref(v_env_2192_);
lean_dec(v___y_2188_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v_pos_2136_);
lean_dec_ref(v___f_2135_);
lean_dec_ref(v___f_2134_);
lean_dec_ref(v___f_2133_);
lean_dec(v___x_2130_);
v___y_2168_ = v___y_2190_;
v___y_2169_ = v___y_2189_;
v___y_2170_ = v___y_2206_;
v___y_2171_ = v___y_2191_;
v___y_2172_ = v___y_2208_;
v___y_2173_ = v___y_2202_;
v___y_2174_ = v___y_2211_;
v___y_2175_ = v___y_2204_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2220_, v_opts_2222_, v___x_2224_);
lean_dec(v___x_2220_);
if (v___x_2225_ == 0)
{
lean_dec_ref(v_opts_2222_);
lean_dec(v___y_2209_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_snapshotTasks_2197_);
lean_dec_ref(v_env_2192_);
lean_dec(v___y_2188_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v_pos_2136_);
lean_dec_ref(v___f_2135_);
lean_dec_ref(v___f_2134_);
lean_dec_ref(v___f_2133_);
lean_dec(v___x_2130_);
v___y_2168_ = v___y_2190_;
v___y_2169_ = v___y_2189_;
v___y_2170_ = v___y_2206_;
v___y_2171_ = v___y_2191_;
v___y_2172_ = v___y_2208_;
v___y_2173_ = v___y_2202_;
v___y_2174_ = v___y_2211_;
v___y_2175_ = v___y_2204_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_inc_n(v___y_2189_, 3);
v___x_2226_ = lean_task_map(v___f_2133_, v___y_2200_, v___y_2189_, v___x_2131_);
lean_inc_n(v___y_2202_, 3);
lean_inc_n(v___y_2207_, 2);
lean_inc_n(v___y_2209_, 2);
v___x_2227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2227_, 0, v___y_2209_);
lean_ctor_set(v___x_2227_, 1, v___y_2207_);
lean_ctor_set(v___x_2227_, 2, v___y_2202_);
lean_ctor_set(v___x_2227_, 3, v___x_2226_);
v___x_2228_ = lean_task_map(v___f_2134_, v___y_2201_, v___y_2189_, v___x_2131_);
v___x_2229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2229_, 0, v___y_2209_);
lean_ctor_set(v___x_2229_, 1, v___y_2207_);
lean_ctor_set(v___x_2229_, 2, v___y_2202_);
lean_ctor_set(v___x_2229_, 3, v___x_2228_);
v___x_2230_ = lean_task_map(v___f_2135_, v___y_2203_, v___y_2189_, v___x_2131_);
v___x_2231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2231_, 0, v___y_2209_);
lean_ctor_set(v___x_2231_, 1, v___y_2207_);
lean_ctor_set(v___x_2231_, 2, v___y_2202_);
lean_ctor_set(v___x_2231_, 3, v___x_2230_);
v___x_2232_ = lean_unsigned_to_nat(3u);
v___x_2233_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2234_ = lean_array_push(v___x_2233_, v___x_2227_);
v___x_2235_ = lean_array_push(v___x_2234_, v___x_2229_);
v___x_2236_ = lean_array_push(v___x_2235_, v___x_2231_);
v___x_2237_ = l_Array_append___redArg(v___x_2236_, v_snapshotTasks_2197_);
lean_inc_ref(v___y_2211_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2211_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_box_usize(v___y_2187_);
v___x_2240_ = lean_box(v___x_2131_);
v___x_2241_ = lean_box(v_val_2127_);
v___x_2242_ = lean_box(v___x_2225_);
lean_inc_ref(v___x_2238_);
lean_inc_ref(v___y_2183_);
lean_inc_ref(v_a_2128_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2243_, 0, v_a_2128_);
lean_closure_set(v___f_2243_, 1, v_opts_2222_);
lean_closure_set(v___f_2243_, 2, v___x_2130_);
lean_closure_set(v___f_2243_, 3, v___y_2186_);
lean_closure_set(v___f_2243_, 4, v___y_2184_);
lean_closure_set(v___f_2243_, 5, v___x_2239_);
lean_closure_set(v___f_2243_, 6, v___x_2240_);
lean_closure_set(v___f_2243_, 7, v_env_2192_);
lean_closure_set(v___f_2243_, 8, v___y_2183_);
lean_closure_set(v___f_2243_, 9, v___x_2238_);
lean_closure_set(v___f_2243_, 10, v_pos_2136_);
lean_closure_set(v___f_2243_, 11, v___x_2241_);
lean_closure_set(v___f_2243_, 12, v___y_2181_);
lean_closure_set(v___f_2243_, 13, v___y_2188_);
lean_closure_set(v___f_2243_, 14, v___y_2185_);
lean_closure_set(v___f_2243_, 15, v___x_2219_);
lean_closure_set(v___f_2243_, 16, v___y_2182_);
lean_closure_set(v___f_2243_, 17, v___x_2242_);
v___x_2244_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2238_);
v___x_2245_ = lean_io_bind_task(v___x_2244_, v___f_2243_, v___y_2189_, v_val_2127_);
v___y_2149_ = v___y_2190_;
v___y_2150_ = v___y_2206_;
v___y_2151_ = v___y_2191_;
v_snapshotTasks_2152_ = v_snapshotTasks_2197_;
v___y_2153_ = v___y_2208_;
v___y_2154_ = v___y_2202_;
v___y_2155_ = v___y_2211_;
v___y_2156_ = v___y_2204_;
v_traceTask_2157_ = v___x_2245_;
goto v___jp_2148_;
}
}
}
v___jp_2246_:
{
lean_object* v_env_2272_; lean_object* v_messages_2273_; lean_object* v_scopes_2274_; lean_object* v_infoState_2275_; lean_object* v_traceState_2276_; lean_object* v_snapshotTasks_2277_; lean_object* v_codeQualityEntryTasks_2278_; 
v_env_2272_ = lean_ctor_get(v___y_2257_, 0);
lean_inc_ref(v_env_2272_);
v_messages_2273_ = lean_ctor_get(v___y_2257_, 1);
lean_inc_ref(v_messages_2273_);
v_scopes_2274_ = lean_ctor_get(v___y_2257_, 2);
lean_inc(v_scopes_2274_);
v_infoState_2275_ = lean_ctor_get(v___y_2257_, 8);
lean_inc_ref(v_infoState_2275_);
v_traceState_2276_ = lean_ctor_get(v___y_2257_, 9);
lean_inc_ref(v_traceState_2276_);
v_snapshotTasks_2277_ = lean_ctor_get(v___y_2257_, 10);
lean_inc_ref(v_snapshotTasks_2277_);
v_codeQualityEntryTasks_2278_ = lean_ctor_get(v___y_2257_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2278_);
v___y_2181_ = v___y_2247_;
v___y_2182_ = v___y_2250_;
v___y_2183_ = v___y_2249_;
v___y_2184_ = v___y_2248_;
v___y_2185_ = v___y_2251_;
v___y_2186_ = v___y_2252_;
v___y_2187_ = v___y_2253_;
v___y_2188_ = v___y_2254_;
v___y_2189_ = v___y_2255_;
v___y_2190_ = v___y_2256_;
v___y_2191_ = v___y_2257_;
v_env_2192_ = v_env_2272_;
v_messages_2193_ = v_messages_2273_;
v_scopes_2194_ = v_scopes_2274_;
v_infoState_2195_ = v_infoState_2275_;
v_traceState_2196_ = v_traceState_2276_;
v_snapshotTasks_2197_ = v_snapshotTasks_2277_;
v_codeQualityEntryTasks_2198_ = v_codeQualityEntryTasks_2278_;
v___y_2199_ = v___y_2258_;
v___y_2200_ = v___y_2259_;
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
v_reportedCmdState_2212_ = v_reportedCmdState_2271_;
goto v___jp_2180_;
}
v___jp_2280_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___f_2303_; uint8_t v___x_2304_; 
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2144_);
lean_inc_ref(v___y_2291_);
lean_inc_n(v_pos_2136_, 2);
lean_inc(v_revCmds_2125_);
lean_inc(v_fst_2124_);
v___x_2300_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2124_, v_revCmds_2125_, v_cmdState_2137_, v_pos_2136_, v___x_2299_, v___y_2291_, v_a_2128_);
v___x_2301_ = lean_box(v_val_2127_);
v___x_2302_ = lean_box(v___x_2131_);
lean_inc_ref(v_a_2128_);
lean_inc(v___y_2288_);
lean_inc_ref(v___x_2132_);
lean_inc_ref(v___x_2300_);
lean_inc_ref(v___y_2286_);
lean_inc_ref(v___y_2282_);
v___f_2303_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2303_, 0, v___y_2282_);
lean_closure_set(v___f_2303_, 1, v___y_2286_);
lean_closure_set(v___f_2303_, 2, v___x_2301_);
lean_closure_set(v___f_2303_, 3, v___x_2146_);
lean_closure_set(v___f_2303_, 4, v___x_2300_);
lean_closure_set(v___f_2303_, 5, v___x_2132_);
lean_closure_set(v___f_2303_, 6, v___y_2288_);
lean_closure_set(v___f_2303_, 7, v___x_2302_);
lean_closure_set(v___f_2303_, 8, v_a_2128_);
lean_closure_set(v___f_2303_, 9, v_pos_2136_);
lean_closure_set(v___f_2303_, 10, v___x_2138_);
v___x_2304_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2139_, v___x_2279_);
if (v___x_2304_ == 0)
{
lean_inc_ref(v___x_2300_);
lean_inc(v___y_2292_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2282_);
v___y_2247_ = v___y_2282_;
v___y_2248_ = v___y_2283_;
v___y_2249_ = v___y_2286_;
v___y_2250_ = v___y_2285_;
v___y_2251_ = v___y_2287_;
v___y_2252_ = v___y_2288_;
v___y_2253_ = v___y_2289_;
v___y_2254_ = v___y_2292_;
v___y_2255_ = v___y_2288_;
v___y_2256_ = v___y_2291_;
v___y_2257_ = v___x_2300_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2290_;
v___y_2260_ = v___y_2293_;
v___y_2261_ = v___y_2285_;
v___y_2262_ = v___y_2294_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v___f_2303_;
v___y_2265_ = v___y_2296_;
v___y_2266_ = v___y_2284_;
v___y_2267_ = v___y_2297_;
v___y_2268_ = v___y_2281_;
v___y_2269_ = v___y_2292_;
v___y_2270_ = v___y_2287_;
v_reportedCmdState_2271_ = v___x_2300_;
goto v___jp_2246_;
}
else
{
uint8_t v___x_2305_; 
lean_inc(v_fst_2124_);
v___x_2305_ = l_Lean_Parser_isTerminalCommand(v_fst_2124_);
if (v___x_2305_ == 0)
{
if (v___x_2304_ == 0)
{
lean_inc_ref(v___x_2300_);
lean_inc(v___y_2292_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2282_);
v___y_2247_ = v___y_2282_;
v___y_2248_ = v___y_2283_;
v___y_2249_ = v___y_2286_;
v___y_2250_ = v___y_2285_;
v___y_2251_ = v___y_2287_;
v___y_2252_ = v___y_2288_;
v___y_2253_ = v___y_2289_;
v___y_2254_ = v___y_2292_;
v___y_2255_ = v___y_2288_;
v___y_2256_ = v___y_2291_;
v___y_2257_ = v___x_2300_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2290_;
v___y_2260_ = v___y_2293_;
v___y_2261_ = v___y_2285_;
v___y_2262_ = v___y_2294_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v___f_2303_;
v___y_2265_ = v___y_2296_;
v___y_2266_ = v___y_2284_;
v___y_2267_ = v___y_2297_;
v___y_2268_ = v___y_2281_;
v___y_2269_ = v___y_2292_;
v___y_2270_ = v___y_2287_;
v_reportedCmdState_2271_ = v___x_2300_;
goto v___jp_2246_;
}
else
{
lean_object* v_env_2306_; lean_object* v_messages_2307_; lean_object* v_scopes_2308_; lean_object* v_infoState_2309_; lean_object* v_traceState_2310_; lean_object* v_snapshotTasks_2311_; lean_object* v_codeQualityEntryTasks_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_env_2306_ = lean_ctor_get(v___x_2300_, 0);
lean_inc_ref_n(v_env_2306_, 2);
v_messages_2307_ = lean_ctor_get(v___x_2300_, 1);
lean_inc_ref(v_messages_2307_);
v_scopes_2308_ = lean_ctor_get(v___x_2300_, 2);
lean_inc(v_scopes_2308_);
v_infoState_2309_ = lean_ctor_get(v___x_2300_, 8);
lean_inc_ref(v_infoState_2309_);
v_traceState_2310_ = lean_ctor_get(v___x_2300_, 9);
lean_inc_ref(v_traceState_2310_);
v_snapshotTasks_2311_ = lean_ctor_get(v___x_2300_, 10);
lean_inc_ref(v_snapshotTasks_2311_);
v_codeQualityEntryTasks_2312_ = lean_ctor_get(v___x_2300_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2312_);
v___x_2313_ = lean_mk_empty_array_with_capacity(v___y_2283_);
lean_inc_ref(v___x_2313_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_inc_n(v___y_2288_, 4);
v___x_2315_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v___x_2313_);
lean_ctor_set(v___x_2315_, 2, v___y_2288_);
lean_ctor_set(v___x_2315_, 3, v___y_2288_);
lean_ctor_set_usize(v___x_2315_, 4, v___y_2289_);
v___x_2316_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2315_, 2);
v___x_2317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2315_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
v___x_2318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2319_ = l_Lean_Options_empty;
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_mk_empty_array_with_capacity(v___y_2288_);
lean_inc_ref_n(v___x_2321_, 3);
lean_inc_n(v___x_2130_, 2);
v___x_2322_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2322_, 0, v___x_2318_);
lean_ctor_set(v___x_2322_, 1, v___x_2319_);
lean_ctor_set(v___x_2322_, 2, v___x_2130_);
lean_ctor_set(v___x_2322_, 3, v___x_2320_);
lean_ctor_set(v___x_2322_, 4, v___x_2320_);
lean_ctor_set(v___x_2322_, 5, v___x_2321_);
lean_ctor_set(v___x_2322_, 6, v___x_2321_);
lean_ctor_set(v___x_2322_, 7, v___x_2320_);
lean_ctor_set(v___x_2322_, 8, v___x_2320_);
lean_ctor_set(v___x_2322_, 9, v___x_2320_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*10, v_val_2127_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*10 + 1, v_val_2127_);
lean_ctor_set_uint8(v___x_2322_, sizeof(void*)*10 + 2, v_val_2127_);
v___x_2323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___x_2320_);
v___x_2324_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2325_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2326_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2130_);
v___x_2327_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2328_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
lean_ctor_set(v___x_2328_, 2, v___x_2315_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*3, v___x_2131_);
v___x_2329_ = lean_box(0);
lean_inc_ref(v___y_2286_);
v___x_2330_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2330_, 0, v_env_2306_);
lean_ctor_set(v___x_2330_, 1, v___x_2317_);
lean_ctor_set(v___x_2330_, 2, v___x_2323_);
lean_ctor_set(v___x_2330_, 3, v___x_2316_);
lean_ctor_set(v___x_2330_, 4, v___x_2324_);
lean_ctor_set(v___x_2330_, 5, v___y_2288_);
lean_ctor_set(v___x_2330_, 6, v___x_2325_);
lean_ctor_set(v___x_2330_, 7, v___x_2326_);
lean_ctor_set(v___x_2330_, 8, v___x_2328_);
lean_ctor_set(v___x_2330_, 9, v___y_2286_);
lean_ctor_set(v___x_2330_, 10, v___x_2321_);
lean_ctor_set(v___x_2330_, 11, v___x_2329_);
lean_ctor_set(v___x_2330_, 12, v___x_2321_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2287_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2282_);
v___y_2181_ = v___y_2282_;
v___y_2182_ = v___y_2285_;
v___y_2183_ = v___y_2286_;
v___y_2184_ = v___y_2283_;
v___y_2185_ = v___y_2287_;
v___y_2186_ = v___y_2288_;
v___y_2187_ = v___y_2289_;
v___y_2188_ = v___y_2292_;
v___y_2189_ = v___y_2288_;
v___y_2190_ = v___y_2291_;
v___y_2191_ = v___x_2300_;
v_env_2192_ = v_env_2306_;
v_messages_2193_ = v_messages_2307_;
v_scopes_2194_ = v_scopes_2308_;
v_infoState_2195_ = v_infoState_2309_;
v_traceState_2196_ = v_traceState_2310_;
v_snapshotTasks_2197_ = v_snapshotTasks_2311_;
v_codeQualityEntryTasks_2198_ = v_codeQualityEntryTasks_2312_;
v___y_2199_ = v___y_2282_;
v___y_2200_ = v___y_2290_;
v___y_2201_ = v___y_2293_;
v___y_2202_ = v___y_2285_;
v___y_2203_ = v___y_2294_;
v___y_2204_ = v___y_2295_;
v___y_2205_ = v___f_2303_;
v___y_2206_ = v___y_2296_;
v___y_2207_ = v___y_2284_;
v___y_2208_ = v___y_2297_;
v___y_2209_ = v___y_2281_;
v___y_2210_ = v___y_2292_;
v___y_2211_ = v___y_2287_;
v_reportedCmdState_2212_ = v___x_2330_;
goto v___jp_2180_;
}
}
else
{
lean_inc_ref(v___x_2300_);
lean_inc(v___y_2292_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2282_);
v___y_2247_ = v___y_2282_;
v___y_2248_ = v___y_2283_;
v___y_2249_ = v___y_2286_;
v___y_2250_ = v___y_2285_;
v___y_2251_ = v___y_2287_;
v___y_2252_ = v___y_2288_;
v___y_2253_ = v___y_2289_;
v___y_2254_ = v___y_2292_;
v___y_2255_ = v___y_2288_;
v___y_2256_ = v___y_2291_;
v___y_2257_ = v___x_2300_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2290_;
v___y_2260_ = v___y_2293_;
v___y_2261_ = v___y_2285_;
v___y_2262_ = v___y_2294_;
v___y_2263_ = v___y_2295_;
v___y_2264_ = v___f_2303_;
v___y_2265_ = v___y_2296_;
v___y_2266_ = v___y_2284_;
v___y_2267_ = v___y_2297_;
v___y_2268_ = v___y_2281_;
v___y_2269_ = v___y_2292_;
v___y_2270_ = v___y_2287_;
v_reportedCmdState_2271_ = v___x_2300_;
goto v___jp_2246_;
}
}
}
v___jp_2331_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; size_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2337_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2129_);
v___x_2338_ = l_IO_CancelToken_new();
v___x_2339_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2130_);
v___x_2340_ = l_Lean_Name_str___override(v___x_2130_, v___x_2339_);
v___x_2341_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2342_ = l_Lean_Name_str___override(v___x_2340_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2344_ = l_Lean_Name_str___override(v___x_2342_, v___x_2343_);
v___x_2345_ = l_Lean_Name_str___override(v___x_2344_, v___x_2341_);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = l_Lean_Name_num___override(v___x_2345_, v___x_2346_);
v___x_2348_ = l_Lean_Name_str___override(v___x_2347_, v___x_2341_);
v___x_2349_ = l_Lean_Name_str___override(v___x_2348_, v___x_2343_);
v___x_2350_ = l_Lean_Name_str___override(v___x_2349_, v___x_2341_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2352_ = l_Lean_Name_str___override(v___x_2350_, v___x_2351_);
v___x_2353_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2354_ = l_Lean_Name_str___override(v___x_2352_, v___x_2353_);
v___x_2355_ = l_Lean_Name_toString(v___x_2354_, v___x_2131_);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_unsigned_to_nat(32u);
v___x_2358_ = lean_mk_empty_array_with_capacity(v___x_2357_);
lean_dec_ref(v___x_2358_);
v___x_2359_ = ((size_t)5ULL);
v___x_2360_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2355_, 2);
v___x_2361_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2361_, 0, v___x_2355_);
lean_ctor_set(v___x_2361_, 1, v___x_2337_);
lean_ctor_set(v___x_2361_, 2, v___x_2356_);
lean_ctor_set(v___x_2361_, 3, v___x_2360_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*4, v_val_2127_);
v___x_2362_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2363_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2355_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
lean_ctor_set(v___x_2363_, 2, v___x_2356_);
lean_ctor_set(v___x_2363_, 3, v___x_2360_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*4, v_val_2127_);
lean_inc(v___y_2335_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___y_2335_);
v___x_2365_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2364_);
lean_inc_ref(v___x_2338_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2338_);
v___x_2367_ = l_IO_Promise_result_x21___redArg(v___x_2144_);
lean_inc_ref(v___x_2367_);
lean_inc(v___x_2365_);
lean_inc_ref_n(v___x_2364_, 3);
v___x_2368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2364_);
lean_ctor_set(v___x_2368_, 1, v___x_2365_);
lean_ctor_set(v___x_2368_, 2, v___x_2366_);
lean_ctor_set(v___x_2368_, 3, v___x_2367_);
v___x_2369_ = l_IO_Promise_result_x21___redArg(v___x_2145_);
lean_inc_ref(v___x_2369_);
lean_inc_n(v___y_2333_, 3);
v___x_2370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2364_);
lean_ctor_set(v___x_2370_, 1, v___y_2333_);
lean_ctor_set(v___x_2370_, 2, v___x_2356_);
lean_ctor_set(v___x_2370_, 3, v___x_2369_);
v___x_2371_ = l_IO_Promise_result_x21___redArg(v___x_2146_);
lean_inc_ref(v___x_2371_);
v___x_2372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2364_);
lean_ctor_set(v___x_2372_, 1, v___y_2333_);
lean_ctor_set(v___x_2372_, 2, v___x_2356_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
v___x_2373_ = l_IO_Promise_result_x21___redArg(v___x_2147_);
v___x_2374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2356_);
lean_ctor_set(v___x_2374_, 1, v___y_2333_);
lean_ctor_set(v___x_2374_, 2, v___x_2356_);
lean_ctor_set(v___x_2374_, 3, v___x_2373_);
lean_inc_ref(v___x_2363_);
v___x_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2363_);
lean_ctor_set(v___x_2375_, 1, v___x_2368_);
lean_ctor_set(v___x_2375_, 2, v___x_2370_);
lean_ctor_set(v___x_2375_, 3, v___x_2372_);
lean_ctor_set(v___x_2375_, 4, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2361_);
lean_ctor_set(v___x_2376_, 1, v___y_2335_);
lean_ctor_set(v___x_2376_, 2, v___y_2332_);
lean_ctor_set(v___x_2376_, 3, v___x_2375_);
lean_ctor_set(v___x_2376_, 4, v___y_2336_);
v___x_2377_ = lean_io_promise_resolve(v___x_2376_, v_prom_2140_);
if (lean_obj_tag(v_old_x3f_2141_) == 0)
{
v___y_2281_ = v___x_2364_;
v___y_2282_ = v___x_2355_;
v___y_2283_ = v___x_2357_;
v___y_2284_ = v___x_2365_;
v___y_2285_ = v___x_2356_;
v___y_2286_ = v___x_2360_;
v___y_2287_ = v___x_2363_;
v___y_2288_ = v___x_2346_;
v___y_2289_ = v___x_2359_;
v___y_2290_ = v___x_2367_;
v___y_2291_ = v___x_2338_;
v___y_2292_ = v___x_2356_;
v___y_2293_ = v___x_2369_;
v___y_2294_ = v___x_2371_;
v___y_2295_ = v___y_2334_;
v___y_2296_ = v___y_2333_;
v___y_2297_ = v___x_2356_;
v___y_2298_ = v___x_2356_;
goto v___jp_2280_;
}
else
{
lean_object* v_val_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2389_; 
v_val_2378_ = lean_ctor_get(v_old_x3f_2141_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_old_x3f_2141_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2380_ = v_old_x3f_2141_;
v_isShared_2381_ = v_isSharedCheck_2389_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_val_2378_);
lean_dec(v_old_x3f_2141_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2389_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_elabSnap_2382_; lean_object* v_stx_2383_; lean_object* v_elabSnap_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v_elabSnap_2382_ = lean_ctor_get(v_val_2378_, 3);
lean_inc_ref(v_elabSnap_2382_);
v_stx_2383_ = lean_ctor_get(v_val_2378_, 1);
lean_inc(v_stx_2383_);
lean_dec(v_val_2378_);
v_elabSnap_2384_ = lean_ctor_get(v_elabSnap_2382_, 1);
lean_inc_ref(v_elabSnap_2384_);
lean_dec_ref(v_elabSnap_2382_);
v___x_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_stx_2383_);
lean_ctor_set(v___x_2385_, 1, v_elabSnap_2384_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2385_);
v___x_2387_ = v___x_2380_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
v___y_2281_ = v___x_2364_;
v___y_2282_ = v___x_2355_;
v___y_2283_ = v___x_2357_;
v___y_2284_ = v___x_2365_;
v___y_2285_ = v___x_2356_;
v___y_2286_ = v___x_2360_;
v___y_2287_ = v___x_2363_;
v___y_2288_ = v___x_2346_;
v___y_2289_ = v___x_2359_;
v___y_2290_ = v___x_2367_;
v___y_2291_ = v___x_2338_;
v___y_2292_ = v___x_2356_;
v___y_2293_ = v___x_2369_;
v___y_2294_ = v___x_2371_;
v___y_2295_ = v___y_2334_;
v___y_2296_ = v___y_2333_;
v___y_2297_ = v___x_2356_;
v___y_2298_ = v___x_2387_;
goto v___jp_2280_;
}
}
}
}
v___jp_2390_:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2393_);
lean_inc(v_fst_2124_);
v___x_2395_ = l_Lean_Parser_isTerminalCommand(v_fst_2124_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v_toProcessingContext_2397_; lean_object* v_pos_2398_; lean_object* v_endPos_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2396_ = lean_io_promise_new();
v_toProcessingContext_2397_ = lean_ctor_get(v_a_2128_, 0);
v_pos_2398_ = lean_ctor_get(v_fst_2126_, 0);
v_endPos_2399_ = lean_ctor_get(v_toProcessingContext_2397_, 3);
lean_inc(v___x_2396_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2396_);
v___x_2401_ = lean_box(0);
lean_inc(v_endPos_2399_);
lean_inc(v_pos_2398_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_pos_2398_);
lean_ctor_set(v___x_2402_, 1, v_endPos_2399_);
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_parseCancelTk_2142_);
v___x_2405_ = l_IO_Promise_result_x21___redArg(v___x_2396_);
lean_dec(v___x_2396_);
v___x_2406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2401_);
lean_ctor_set(v___x_2406_, 1, v___x_2403_);
lean_ctor_set(v___x_2406_, 2, v___x_2404_);
lean_ctor_set(v___x_2406_, 3, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
v___y_2332_ = v___y_2391_;
v___y_2333_ = v___x_2394_;
v___y_2334_ = v___x_2400_;
v___y_2335_ = v___y_2392_;
v___y_2336_ = v___x_2407_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2408_; 
lean_dec_ref(v_parseCancelTk_2142_);
v___x_2408_ = lean_box(0);
v___y_2332_ = v___y_2391_;
v___y_2333_ = v___x_2394_;
v___y_2334_ = v___x_2408_;
v___y_2335_ = v___y_2392_;
v___y_2336_ = v___x_2408_;
goto v___jp_2331_;
}
}
v___jp_2409_:
{
lean_object* v___x_2412_; 
lean_inc(v_fst_2124_);
v___x_2412_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2124_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_box(0);
v___y_2391_ = v_snd_2411_;
v___y_2392_ = v_fst_2410_;
v___y_2393_ = v___x_2413_;
goto v___jp_2390_;
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2422_; 
v_val_2414_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2422_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
lean_inc(v_val_2414_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_val_2414_);
lean_ctor_set(v___x_2418_, 1, v_val_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2418_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
v___y_2391_ = v_snd_2411_;
v___y_2392_ = v_fst_2410_;
v___y_2393_ = v___x_2420_;
goto v___jp_2390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_fst_2427_ = _args[0];
lean_object* v_revCmds_2428_ = _args[1];
lean_object* v_fst_2429_ = _args[2];
lean_object* v_val_2430_ = _args[3];
lean_object* v_a_2431_ = _args[4];
lean_object* v_snd_2432_ = _args[5];
lean_object* v___x_2433_ = _args[6];
lean_object* v___x_2434_ = _args[7];
lean_object* v___x_2435_ = _args[8];
lean_object* v___f_2436_ = _args[9];
lean_object* v___f_2437_ = _args[10];
lean_object* v___f_2438_ = _args[11];
lean_object* v_pos_2439_ = _args[12];
lean_object* v_cmdState_2440_ = _args[13];
lean_object* v___x_2441_ = _args[14];
lean_object* v_opts_2442_ = _args[15];
lean_object* v_prom_2443_ = _args[16];
lean_object* v_old_x3f_2444_ = _args[17];
lean_object* v_parseCancelTk_2445_ = _args[18];
lean_object* v___y_2446_ = _args[19];
_start:
{
uint8_t v_val_37353__boxed_2447_; uint8_t v___x_37356__boxed_2448_; lean_object* v_res_2449_; 
v_val_37353__boxed_2447_ = lean_unbox(v_val_2430_);
v___x_37356__boxed_2448_ = lean_unbox(v___x_2434_);
v_res_2449_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_fst_2427_, v_revCmds_2428_, v_fst_2429_, v_val_37353__boxed_2447_, v_a_2431_, v_snd_2432_, v___x_2433_, v___x_37356__boxed_2448_, v___x_2435_, v___f_2436_, v___f_2437_, v___f_2438_, v_pos_2439_, v_cmdState_2440_, v___x_2441_, v_opts_2442_, v_prom_2443_, v_old_x3f_2444_, v_parseCancelTk_2445_);
lean_dec(v_prom_2443_);
lean_dec_ref(v_opts_2442_);
lean_dec_ref(v_a_2431_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2452_, lean_object* v_parserState_2453_, lean_object* v_cmdState_2454_, lean_object* v_prom_2455_, uint8_t v_sync_2456_, lean_object* v_parseCancelTk_2457_, lean_object* v_revCmds_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___y_2464_; lean_object* v_toSnapshot_2466_; lean_object* v_stx_2467_; lean_object* v_parserState_2468_; lean_object* v_elabSnap_2469_; lean_object* v_val_2470_; lean_object* v_newParserState_2471_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; uint8_t v___y_2520_; lean_object* v___y_2521_; uint8_t v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___y_2543_; uint8_t v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v_fst_2547_; lean_object* v_snd_2548_; lean_object* v___y_2561_; uint8_t v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2598_; uint8_t v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___x_2643_; 
v___f_2502_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2503_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2504_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2505_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2506_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2643_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
if (lean_obj_tag(v_old_x3f_2452_) == 1)
{
lean_object* v_val_2676_; lean_object* v_nextCmdSnap_x3f_2677_; 
v_val_2676_ = lean_ctor_get(v_old_x3f_2452_, 0);
v_nextCmdSnap_x3f_2677_ = lean_ctor_get(v_val_2676_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2677_) == 0)
{
goto v___jp_2644_;
}
else
{
lean_object* v_toSnapshot_2678_; lean_object* v_stx_2679_; lean_object* v_parserState_2680_; lean_object* v_elabSnap_2681_; lean_object* v_val_2682_; lean_object* v___x_2683_; 
v_toSnapshot_2678_ = lean_ctor_get(v_val_2676_, 0);
v_stx_2679_ = lean_ctor_get(v_val_2676_, 1);
v_parserState_2680_ = lean_ctor_get(v_val_2676_, 2);
v_elabSnap_2681_ = lean_ctor_get(v_val_2676_, 3);
v_val_2682_ = lean_ctor_get(v_nextCmdSnap_x3f_2677_, 0);
lean_inc(v_val_2682_);
v___x_2683_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2682_);
if (lean_obj_tag(v___x_2683_) == 1)
{
lean_object* v_val_2684_; lean_object* v_nextCmdSnap_x3f_2685_; 
v_val_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_val_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v_nextCmdSnap_x3f_2685_ = lean_ctor_get(v_val_2684_, 4);
lean_inc(v_nextCmdSnap_x3f_2685_);
lean_dec(v_val_2684_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2685_) == 0)
{
goto v___jp_2644_;
}
else
{
lean_object* v_val_2686_; lean_object* v___x_2687_; 
v_val_2686_ = lean_ctor_get(v_nextCmdSnap_x3f_2685_, 0);
lean_inc(v_val_2686_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2685_, 1);
v___x_2687_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2686_);
if (lean_obj_tag(v___x_2687_) == 1)
{
lean_object* v_val_2688_; lean_object* v_parserState_2689_; lean_object* v_pos_2690_; uint8_t v___x_2691_; 
v_val_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_val_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v_parserState_2689_ = lean_ctor_get(v_val_2688_, 2);
lean_inc_ref(v_parserState_2689_);
lean_dec(v_val_2688_);
v_pos_2690_ = lean_ctor_get(v_parserState_2689_, 0);
lean_inc(v_pos_2690_);
lean_dec_ref(v_parserState_2689_);
v___x_2691_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2690_, v_a_2459_);
lean_dec(v_pos_2690_);
if (v___x_2691_ == 0)
{
goto v___jp_2644_;
}
else
{
lean_inc(v_val_2682_);
lean_inc_ref(v_elabSnap_2681_);
lean_inc_ref_n(v_parserState_2680_, 2);
lean_inc(v_stx_2679_);
lean_inc_ref(v_toSnapshot_2678_);
lean_dec_ref_known(v_old_x3f_2452_, 1);
lean_dec_ref(v_parseCancelTk_2457_);
lean_dec_ref(v_cmdState_2454_);
lean_dec_ref(v_parserState_2453_);
v_toSnapshot_2466_ = v_toSnapshot_2678_;
v_stx_2467_ = v_stx_2679_;
v_parserState_2468_ = v_parserState_2680_;
v_elabSnap_2469_ = v_elabSnap_2681_;
v_val_2470_ = v_val_2682_;
v_newParserState_2471_ = v_parserState_2680_;
goto v___jp_2465_;
}
}
else
{
lean_dec(v___x_2687_);
goto v___jp_2644_;
}
}
}
else
{
lean_dec(v___x_2683_);
goto v___jp_2644_;
}
}
}
else
{
goto v___jp_2644_;
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
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_resultSnap_2474_; lean_object* v_task_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2498_; 
v___x_2472_ = lean_io_promise_new();
v___x_2473_ = l_IO_CancelToken_new();
v_resultSnap_2474_ = lean_ctor_get(v_elabSnap_2469_, 2);
lean_inc_ref(v_resultSnap_2474_);
v_task_2475_ = lean_ctor_get(v_resultSnap_2474_, 3);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_resultSnap_2474_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; 
v_unused_2499_ = lean_ctor_get(v_resultSnap_2474_, 2);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_resultSnap_2474_, 1);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_resultSnap_2474_, 0);
lean_dec(v_unused_2501_);
v___x_2477_ = v_resultSnap_2474_;
v_isShared_2478_ = v_isSharedCheck_2498_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_task_2475_);
lean_dec(v_resultSnap_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2498_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___f_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; lean_object* v_toProcessingContext_2484_; lean_object* v_pos_2485_; lean_object* v_endPos_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2479_ = lean_box(v_sync_2456_);
lean_inc_ref(v_a_2459_);
lean_inc_ref(v___x_2473_);
lean_inc(v___x_2472_);
lean_inc_ref(v_newParserState_2471_);
lean_inc(v_stx_2467_);
v___f_2480_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2480_, 0, v_val_2470_);
lean_closure_set(v___f_2480_, 1, v_stx_2467_);
lean_closure_set(v___f_2480_, 2, v_revCmds_2458_);
lean_closure_set(v___f_2480_, 3, v_newParserState_2471_);
lean_closure_set(v___f_2480_, 4, v___x_2472_);
lean_closure_set(v___f_2480_, 5, v___x_2479_);
lean_closure_set(v___f_2480_, 6, v___x_2473_);
lean_closure_set(v___f_2480_, 7, v_a_2459_);
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = 1;
v___x_2483_ = l_BaseIO_chainTask___redArg(v_task_2475_, v___f_2480_, v___x_2481_, v___x_2482_);
v_toProcessingContext_2484_ = lean_ctor_get(v_a_2459_, 0);
v_pos_2485_ = lean_ctor_get(v_newParserState_2471_, 0);
lean_inc(v_pos_2485_);
lean_dec_ref(v_newParserState_2471_);
v_endPos_2486_ = lean_ctor_get(v_toProcessingContext_2484_, 3);
v___x_2487_ = lean_box(0);
lean_inc(v_endPos_2486_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_pos_2485_);
lean_ctor_set(v___x_2488_, 1, v_endPos_2486_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2473_);
v___x_2491_ = l_IO_Promise_result_x21___redArg(v___x_2472_);
lean_dec(v___x_2472_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 3, v___x_2491_);
lean_ctor_set(v___x_2477_, 2, v___x_2490_);
lean_ctor_set(v___x_2477_, 1, v___x_2489_);
lean_ctor_set(v___x_2477_, 0, v___x_2487_);
v___x_2493_ = v___x_2477_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2495_, 0, v_toSnapshot_2466_);
lean_ctor_set(v___x_2495_, 1, v_stx_2467_);
lean_ctor_set(v___x_2495_, 2, v_parserState_2468_);
lean_ctor_set(v___x_2495_, 3, v_elabSnap_2469_);
lean_ctor_set(v___x_2495_, 4, v___x_2494_);
v___x_2496_ = lean_io_promise_resolve(v___x_2495_, v_prom_2455_);
lean_dec(v_prom_2455_);
return v___x_2496_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2524_);
v___x_2526_ = l_Lean_Parser_isTerminalCommand(v___y_2519_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = lean_io_promise_new();
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
v___x_2529_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2525_, v___y_2513_, v___y_2515_, v_revCmds_2458_, v___y_2508_, v___y_2520_, v_a_2459_, v___y_2511_, v___y_2514_, v___y_2522_, v___y_2512_, v___y_2518_, v___y_2510_, v___x_2505_, v___f_2504_, v___f_2503_, v___f_2502_, v___y_2516_, v_cmdState_2454_, v___y_2523_, v___x_2506_, v___y_2517_, v___y_2509_, v___y_2521_, v_prom_2455_, v_old_x3f_2452_, v_parseCancelTk_2457_, v___x_2528_);
lean_dec(v_prom_2455_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2510_);
lean_dec(v___y_2513_);
v___y_2464_ = v___x_2529_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_box(0);
v___x_2531_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2525_, v___y_2513_, v___y_2515_, v_revCmds_2458_, v___y_2508_, v___y_2520_, v_a_2459_, v___y_2511_, v___y_2514_, v___y_2522_, v___y_2512_, v___y_2518_, v___y_2510_, v___x_2505_, v___f_2504_, v___f_2503_, v___f_2502_, v___y_2516_, v_cmdState_2454_, v___y_2523_, v___x_2506_, v___y_2517_, v___y_2509_, v___y_2521_, v_prom_2455_, v_old_x3f_2452_, v_parseCancelTk_2457_, v___x_2530_);
lean_dec(v_prom_2455_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2510_);
lean_dec(v___y_2513_);
v___y_2464_ = v___x_2531_;
goto v___jp_2463_;
}
}
v___jp_2532_:
{
lean_object* v___x_2549_; 
lean_inc(v___y_2546_);
v___x_2549_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2546_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_box(0);
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2535_;
v___y_2511_ = v___y_2536_;
v___y_2512_ = v_fst_2547_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v___y_2541_;
v___y_2518_ = v___y_2542_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v_snd_2548_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___x_2550_;
goto v___jp_2507_;
}
else
{
lean_object* v_val_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2559_; 
v_val_2551_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2553_ = v___x_2549_;
v_isShared_2554_ = v_isSharedCheck_2559_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_val_2551_);
lean_dec(v___x_2549_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2559_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
lean_inc(v_val_2551_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v_val_2551_);
lean_ctor_set(v___x_2555_, 1, v_val_2551_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2535_;
v___y_2511_ = v___y_2536_;
v___y_2512_ = v_fst_2547_;
v___y_2513_ = v___y_2537_;
v___y_2514_ = v___y_2538_;
v___y_2515_ = v___y_2539_;
v___y_2516_ = v___y_2540_;
v___y_2517_ = v___y_2541_;
v___y_2518_ = v___y_2542_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v___y_2543_;
v___y_2521_ = v_snd_2548_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___x_2557_;
goto v___jp_2507_;
}
}
}
}
v___jp_2560_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2564_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2565_ = l_Lean_Name_str___override(v___y_2563_, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2567_ = l_Lean_Name_str___override(v___x_2565_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2569_ = l_Lean_Name_str___override(v___x_2567_, v___x_2568_);
v___x_2570_ = l_Lean_Name_str___override(v___x_2569_, v___x_2566_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = l_Lean_Name_num___override(v___x_2570_, v___x_2571_);
v___x_2573_ = l_Lean_Name_str___override(v___x_2572_, v___x_2566_);
v___x_2574_ = l_Lean_Name_str___override(v___x_2573_, v___x_2568_);
v___x_2575_ = l_Lean_Name_str___override(v___x_2574_, v___x_2566_);
v___x_2576_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2577_ = l_Lean_Name_str___override(v___x_2575_, v___x_2576_);
v___x_2578_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2579_ = l_Lean_Name_str___override(v___x_2577_, v___x_2578_);
v___x_2580_ = l_Lean_Name_toString(v___x_2579_, v___y_2562_);
v___x_2581_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2584_ = 0;
v___x_2585_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2585_, 0, v___x_2580_);
lean_ctor_set(v___x_2585_, 1, v___x_2581_);
lean_ctor_set(v___x_2585_, 2, v___x_2582_);
lean_ctor_set(v___x_2585_, 3, v___x_2583_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*4, v___x_2584_);
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_2588_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref_n(v___x_2585_, 3);
v___x_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2585_);
lean_ctor_set(v___x_2589_, 1, v_cmdState_2454_);
lean_ctor_set(v___x_2589_, 2, v___x_2588_);
v___x_2590_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2582_, v___x_2589_);
v___x_2591_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2582_, v___x_2585_);
v___x_2592_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v___x_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2585_);
lean_ctor_set(v___x_2593_, 1, v___x_2587_);
lean_ctor_set(v___x_2593_, 2, v___x_2590_);
lean_ctor_set(v___x_2593_, 3, v___x_2591_);
lean_ctor_set(v___x_2593_, 4, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2585_);
lean_ctor_set(v___x_2594_, 1, v___x_2586_);
lean_ctor_set(v___x_2594_, 2, v___y_2561_);
lean_ctor_set(v___x_2594_, 3, v___x_2593_);
lean_ctor_set(v___x_2594_, 4, v___x_2582_);
v___x_2595_ = lean_io_promise_resolve(v___x_2594_, v_prom_2455_);
lean_dec(v_prom_2455_);
v___x_2596_ = lean_box(0);
return v___x_2596_;
}
v___jp_2597_:
{
v___y_2561_ = v___y_2598_;
v___y_2562_ = v___y_2599_;
v___y_2563_ = v___y_2600_;
goto v___jp_2560_;
}
v___jp_2602_:
{
uint8_t v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = l_IO_CancelToken_isSet(v_parseCancelTk_2457_);
v___x_2614_ = 1;
if (v___x_2613_ == 0)
{
lean_dec(v___y_2610_);
if (v_sync_2456_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2615_ = lean_io_promise_new();
v___x_2616_ = lean_io_promise_new();
v___x_2617_ = lean_io_promise_new();
v___x_2618_ = lean_io_promise_new();
v___x_2619_ = l_Lean_internal_cmdlineSnapshots;
v___x_2620_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2611_, v___x_2619_);
lean_dec_ref(v___y_2611_);
if (v___x_2620_ == 0)
{
lean_inc(v___y_2612_);
v___y_2533_ = v___y_2603_;
v___y_2534_ = v___x_2619_;
v___y_2535_ = v___x_2616_;
v___y_2536_ = v___y_2604_;
v___y_2537_ = v___x_2618_;
v___y_2538_ = v___y_2605_;
v___y_2539_ = v___y_2608_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2606_;
v___y_2542_ = v___x_2615_;
v___y_2543_ = v___x_2613_;
v___y_2544_ = v___x_2614_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___y_2612_;
v_fst_2547_ = v___y_2612_;
v_snd_2548_ = v___y_2609_;
goto v___jp_2532_;
}
else
{
uint8_t v___x_2621_; 
lean_inc(v___y_2612_);
v___x_2621_ = l_Lean_Parser_isTerminalCommand(v___y_2612_);
if (v___x_2621_ == 0)
{
if (v___x_2620_ == 0)
{
lean_inc(v___y_2612_);
v___y_2533_ = v___y_2603_;
v___y_2534_ = v___x_2619_;
v___y_2535_ = v___x_2616_;
v___y_2536_ = v___y_2604_;
v___y_2537_ = v___x_2618_;
v___y_2538_ = v___y_2605_;
v___y_2539_ = v___y_2608_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2606_;
v___y_2542_ = v___x_2615_;
v___y_2543_ = v___x_2613_;
v___y_2544_ = v___x_2614_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___y_2612_;
v_fst_2547_ = v___y_2612_;
v_snd_2548_ = v___y_2609_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec_ref(v___y_2609_);
v___x_2622_ = lean_box(0);
v___x_2623_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2533_ = v___y_2603_;
v___y_2534_ = v___x_2619_;
v___y_2535_ = v___x_2616_;
v___y_2536_ = v___y_2604_;
v___y_2537_ = v___x_2618_;
v___y_2538_ = v___y_2605_;
v___y_2539_ = v___y_2608_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2606_;
v___y_2542_ = v___x_2615_;
v___y_2543_ = v___x_2613_;
v___y_2544_ = v___x_2614_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___y_2612_;
v_fst_2547_ = v___x_2622_;
v_snd_2548_ = v___x_2623_;
goto v___jp_2532_;
}
}
else
{
lean_inc(v___y_2612_);
v___y_2533_ = v___y_2603_;
v___y_2534_ = v___x_2619_;
v___y_2535_ = v___x_2616_;
v___y_2536_ = v___y_2604_;
v___y_2537_ = v___x_2618_;
v___y_2538_ = v___y_2605_;
v___y_2539_ = v___y_2608_;
v___y_2540_ = v___y_2607_;
v___y_2541_ = v___y_2606_;
v___y_2542_ = v___x_2615_;
v___y_2543_ = v___x_2613_;
v___y_2544_ = v___x_2614_;
v___y_2545_ = v___x_2617_;
v___y_2546_ = v___y_2612_;
v_fst_2547_ = v___y_2612_;
v_snd_2548_ = v___y_2609_;
goto v___jp_2532_;
}
}
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v___y_2609_);
v___x_2624_ = lean_box(v___x_2613_);
v___x_2625_ = lean_box(v___x_2614_);
lean_inc_ref(v_a_2459_);
v___f_2626_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2626_, 0, v___y_2608_);
lean_closure_set(v___f_2626_, 1, v_revCmds_2458_);
lean_closure_set(v___f_2626_, 2, v___y_2603_);
lean_closure_set(v___f_2626_, 3, v___x_2624_);
lean_closure_set(v___f_2626_, 4, v_a_2459_);
lean_closure_set(v___f_2626_, 5, v___y_2604_);
lean_closure_set(v___f_2626_, 6, v___y_2605_);
lean_closure_set(v___f_2626_, 7, v___x_2625_);
lean_closure_set(v___f_2626_, 8, v___x_2505_);
lean_closure_set(v___f_2626_, 9, v___f_2504_);
lean_closure_set(v___f_2626_, 10, v___f_2503_);
lean_closure_set(v___f_2626_, 11, v___f_2502_);
lean_closure_set(v___f_2626_, 12, v___y_2607_);
lean_closure_set(v___f_2626_, 13, v_cmdState_2454_);
lean_closure_set(v___f_2626_, 14, v___x_2506_);
lean_closure_set(v___f_2626_, 15, v___y_2606_);
lean_closure_set(v___f_2626_, 16, v_prom_2455_);
lean_closure_set(v___f_2626_, 17, v_old_x3f_2452_);
lean_closure_set(v___f_2626_, 18, v_parseCancelTk_2457_);
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_io_as_task(v___f_2626_, v___x_2627_);
lean_dec_ref(v___x_2628_);
goto v___jp_2461_;
}
}
else
{
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v_revCmds_2458_);
lean_dec_ref(v_parseCancelTk_2457_);
if (lean_obj_tag(v_old_x3f_2452_) == 1)
{
lean_object* v_val_2629_; lean_object* v___x_2630_; lean_object* v_children_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v_val_2629_ = lean_ctor_get(v_old_x3f_2452_, 0);
lean_inc(v_val_2629_);
lean_dec_ref_known(v_old_x3f_2452_, 1);
v___x_2630_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2629_);
v_children_2631_ = lean_ctor_get(v___x_2630_, 1);
lean_inc_ref(v_children_2631_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2633_ = lean_array_get_size(v_children_2631_);
v___x_2634_ = lean_nat_dec_lt(v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_dec_ref(v_children_2631_);
v___y_2561_ = v___y_2609_;
v___y_2562_ = v___x_2614_;
v___y_2563_ = v___y_2610_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_nat_dec_le(v___x_2633_, v___x_2633_);
if (v___x_2636_ == 0)
{
if (v___x_2634_ == 0)
{
lean_dec_ref(v_children_2631_);
v___y_2561_ = v___y_2609_;
v___y_2562_ = v___x_2614_;
v___y_2563_ = v___y_2610_;
goto v___jp_2560_;
}
else
{
size_t v___x_2637_; size_t v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((size_t)0ULL);
v___x_2638_ = lean_usize_of_nat(v___x_2633_);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2631_, v___x_2637_, v___x_2638_, v___x_2635_);
lean_dec_ref(v_children_2631_);
v___y_2598_ = v___y_2609_;
v___y_2599_ = v___x_2614_;
v___y_2600_ = v___y_2610_;
v___y_2601_ = v___x_2639_;
goto v___jp_2597_;
}
}
else
{
size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2633_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2631_, v___x_2640_, v___x_2641_, v___x_2635_);
lean_dec_ref(v_children_2631_);
v___y_2598_ = v___y_2609_;
v___y_2599_ = v___x_2614_;
v___y_2600_ = v___y_2610_;
v___y_2601_ = v___x_2642_;
goto v___jp_2597_;
}
}
}
else
{
lean_dec(v_old_x3f_2452_);
v___y_2561_ = v___y_2609_;
v___y_2562_ = v___x_2614_;
v___y_2563_ = v___y_2610_;
goto v___jp_2560_;
}
}
}
v___jp_2644_:
{
lean_object* v_env_2645_; lean_object* v_scopes_2646_; lean_object* v___x_2647_; lean_object* v_opts_2648_; lean_object* v_currNamespace_2649_; lean_object* v_openDecls_2650_; lean_object* v___x_2651_; lean_object* v___f_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_snd_2656_; 
v_env_2645_ = lean_ctor_get(v_cmdState_2454_, 0);
v_scopes_2646_ = lean_ctor_get(v_cmdState_2454_, 2);
v___x_2647_ = l_List_head_x21___redArg(v___x_2505_, v_scopes_2646_);
v_opts_2648_ = lean_ctor_get(v___x_2647_, 1);
lean_inc_ref_n(v_opts_2648_, 2);
v_currNamespace_2649_ = lean_ctor_get(v___x_2647_, 2);
lean_inc(v_currNamespace_2649_);
v_openDecls_2650_ = lean_ctor_get(v___x_2647_, 3);
lean_inc(v_openDecls_2650_);
lean_dec(v___x_2647_);
lean_inc_ref(v_env_2645_);
v___x_2651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2651_, 0, v_env_2645_);
lean_ctor_set(v___x_2651_, 1, v_opts_2648_);
lean_ctor_set(v___x_2651_, 2, v_currNamespace_2649_);
lean_ctor_set(v___x_2651_, 3, v_openDecls_2650_);
lean_inc_ref(v_parserState_2453_);
lean_inc_ref(v_a_2459_);
v___f_2652_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2652_, 0, v_a_2459_);
lean_closure_set(v___f_2652_, 1, v___x_2651_);
lean_closure_set(v___f_2652_, 2, v_parserState_2453_);
v___x_2653_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__7));
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_profileit(v___x_2653_, v_opts_2648_, v___f_2652_, v___x_2654_);
v_snd_2656_ = lean_ctor_get(v___x_2655_, 1);
lean_inc(v_snd_2656_);
if (lean_obj_tag(v_old_x3f_2452_) == 1)
{
lean_object* v_val_2657_; lean_object* v_fst_2658_; lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v_pos_2661_; lean_object* v_toSnapshot_2662_; lean_object* v_stx_2663_; lean_object* v_parserState_2664_; lean_object* v_elabSnap_2665_; lean_object* v_nextCmdSnap_x3f_2666_; uint8_t v___x_2667_; 
v_val_2657_ = lean_ctor_get(v_old_x3f_2452_, 0);
v_fst_2658_ = lean_ctor_get(v___x_2655_, 0);
lean_inc_n(v_fst_2658_, 2);
lean_dec(v___x_2655_);
v_fst_2659_ = lean_ctor_get(v_snd_2656_, 0);
lean_inc(v_fst_2659_);
v_snd_2660_ = lean_ctor_get(v_snd_2656_, 1);
lean_inc(v_snd_2660_);
lean_dec(v_snd_2656_);
v_pos_2661_ = lean_ctor_get(v_parserState_2453_, 0);
lean_inc(v_pos_2661_);
lean_dec_ref(v_parserState_2453_);
v_toSnapshot_2662_ = lean_ctor_get(v_val_2657_, 0);
v_stx_2663_ = lean_ctor_get(v_val_2657_, 1);
v_parserState_2664_ = lean_ctor_get(v_val_2657_, 2);
v_elabSnap_2665_ = lean_ctor_get(v_val_2657_, 3);
v_nextCmdSnap_x3f_2666_ = lean_ctor_get(v_val_2657_, 4);
lean_inc(v_stx_2663_);
v___x_2667_ = l_Lean_Syntax_eqWithInfo(v_fst_2658_, v_stx_2663_);
if (v___x_2667_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2666_) == 0)
{
lean_inc(v_fst_2658_);
lean_inc_ref(v_opts_2648_);
lean_inc(v_fst_2659_);
v___y_2603_ = v_fst_2659_;
v___y_2604_ = v_snd_2660_;
v___y_2605_ = v___x_2654_;
v___y_2606_ = v_opts_2648_;
v___y_2607_ = v_pos_2661_;
v___y_2608_ = v_fst_2658_;
v___y_2609_ = v_fst_2659_;
v___y_2610_ = v___x_2654_;
v___y_2611_ = v_opts_2648_;
v___y_2612_ = v_fst_2658_;
goto v___jp_2602_;
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2669_; 
v_val_2668_ = lean_ctor_get(v_nextCmdSnap_x3f_2666_, 0);
lean_inc(v_val_2668_);
v___x_2669_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2643_, v_val_2668_);
lean_inc(v_fst_2658_);
lean_inc_ref(v_opts_2648_);
lean_inc(v_fst_2659_);
v___y_2603_ = v_fst_2659_;
v___y_2604_ = v_snd_2660_;
v___y_2605_ = v___x_2654_;
v___y_2606_ = v_opts_2648_;
v___y_2607_ = v_pos_2661_;
v___y_2608_ = v_fst_2658_;
v___y_2609_ = v_fst_2659_;
v___y_2610_ = v___x_2654_;
v___y_2611_ = v_opts_2648_;
v___y_2612_ = v_fst_2658_;
goto v___jp_2602_;
}
}
else
{
lean_inc(v_val_2657_);
lean_dec(v_pos_2661_);
lean_dec(v_snd_2660_);
lean_dec(v_fst_2658_);
lean_dec_ref_known(v_old_x3f_2452_, 1);
lean_dec_ref(v_opts_2648_);
lean_dec_ref(v_parseCancelTk_2457_);
lean_dec_ref(v_cmdState_2454_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2666_) == 1)
{
lean_object* v_val_2670_; 
lean_inc_ref(v_nextCmdSnap_x3f_2666_);
lean_inc_ref(v_elabSnap_2665_);
lean_inc_ref(v_parserState_2664_);
lean_inc(v_stx_2663_);
lean_inc_ref(v_toSnapshot_2662_);
lean_dec(v_val_2657_);
v_val_2670_ = lean_ctor_get(v_nextCmdSnap_x3f_2666_, 0);
lean_inc(v_val_2670_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2666_, 1);
v_toSnapshot_2466_ = v_toSnapshot_2662_;
v_stx_2467_ = v_stx_2663_;
v_parserState_2468_ = v_parserState_2664_;
v_elabSnap_2469_ = v_elabSnap_2665_;
v_val_2470_ = v_val_2670_;
v_newParserState_2471_ = v_fst_2659_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2671_; 
lean_dec(v_fst_2659_);
lean_dec(v_revCmds_2458_);
v___x_2671_ = lean_io_promise_resolve(v_val_2657_, v_prom_2455_);
lean_dec(v_prom_2455_);
return v___x_2671_;
}
}
}
else
{
lean_object* v_fst_2672_; lean_object* v_fst_2673_; lean_object* v_snd_2674_; lean_object* v_pos_2675_; 
v_fst_2672_ = lean_ctor_get(v___x_2655_, 0);
lean_inc_n(v_fst_2672_, 2);
lean_dec(v___x_2655_);
v_fst_2673_ = lean_ctor_get(v_snd_2656_, 0);
lean_inc_n(v_fst_2673_, 2);
v_snd_2674_ = lean_ctor_get(v_snd_2656_, 1);
lean_inc(v_snd_2674_);
lean_dec(v_snd_2656_);
v_pos_2675_ = lean_ctor_get(v_parserState_2453_, 0);
lean_inc(v_pos_2675_);
lean_dec_ref(v_parserState_2453_);
lean_inc_ref(v_opts_2648_);
v___y_2603_ = v_fst_2673_;
v___y_2604_ = v_snd_2674_;
v___y_2605_ = v___x_2654_;
v___y_2606_ = v_opts_2648_;
v___y_2607_ = v_pos_2675_;
v___y_2608_ = v_fst_2672_;
v___y_2609_ = v_fst_2673_;
v___y_2610_ = v___x_2654_;
v___y_2611_ = v_opts_2648_;
v___y_2612_ = v_fst_2672_;
goto v___jp_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2692_, lean_object* v_stx_2693_, lean_object* v_revCmds_2694_, lean_object* v_newParserState_2695_, lean_object* v_val_2696_, uint8_t v_sync_2697_, lean_object* v_val_2698_, lean_object* v_a_2699_, lean_object* v_oldNext_2700_){
_start:
{
lean_object* v_cmdState_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_cmdState_2702_ = lean_ctor_get(v_oldResult_2692_, 1);
lean_inc_ref(v_cmdState_2702_);
lean_dec_ref(v_oldResult_2692_);
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_oldNext_2700_);
v___x_2704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_stx_2693_);
lean_ctor_set(v___x_2704_, 1, v_revCmds_2694_);
v___x_2705_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2703_, v_newParserState_2695_, v_cmdState_2702_, v_val_2696_, v_sync_2697_, v_val_2698_, v___x_2704_, v_a_2699_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2706_ = _args[0];
lean_object* v_val_2707_ = _args[1];
lean_object* v_fst_2708_ = _args[2];
lean_object* v_revCmds_2709_ = _args[3];
lean_object* v_fst_2710_ = _args[4];
lean_object* v_val_2711_ = _args[5];
lean_object* v_a_2712_ = _args[6];
lean_object* v_snd_2713_ = _args[7];
lean_object* v___x_2714_ = _args[8];
lean_object* v___x_2715_ = _args[9];
lean_object* v_fst_2716_ = _args[10];
lean_object* v_val_2717_ = _args[11];
lean_object* v_val_2718_ = _args[12];
lean_object* v___x_2719_ = _args[13];
lean_object* v___f_2720_ = _args[14];
lean_object* v___f_2721_ = _args[15];
lean_object* v___f_2722_ = _args[16];
lean_object* v_pos_2723_ = _args[17];
lean_object* v_cmdState_2724_ = _args[18];
lean_object* v_val_2725_ = _args[19];
lean_object* v___x_2726_ = _args[20];
lean_object* v_opts_2727_ = _args[21];
lean_object* v___x_2728_ = _args[22];
lean_object* v_snd_2729_ = _args[23];
lean_object* v_prom_2730_ = _args[24];
lean_object* v_old_x3f_2731_ = _args[25];
lean_object* v_parseCancelTk_2732_ = _args[26];
lean_object* v_next_x3f_2733_ = _args[27];
lean_object* v___y_2734_ = _args[28];
_start:
{
uint8_t v_val_37143__boxed_2735_; uint8_t v___x_37146__boxed_2736_; lean_object* v_res_2737_; 
v_val_37143__boxed_2735_ = lean_unbox(v_val_2711_);
v___x_37146__boxed_2736_ = lean_unbox(v___x_2715_);
v_res_2737_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2706_, v_val_2707_, v_fst_2708_, v_revCmds_2709_, v_fst_2710_, v_val_37143__boxed_2735_, v_a_2712_, v_snd_2713_, v___x_2714_, v___x_37146__boxed_2736_, v_fst_2716_, v_val_2717_, v_val_2718_, v___x_2719_, v___f_2720_, v___f_2721_, v___f_2722_, v_pos_2723_, v_cmdState_2724_, v_val_2725_, v___x_2726_, v_opts_2727_, v___x_2728_, v_snd_2729_, v_prom_2730_, v_old_x3f_2731_, v_parseCancelTk_2732_, v_next_x3f_2733_);
lean_dec(v_prom_2730_);
lean_dec_ref(v___x_2728_);
lean_dec_ref(v_opts_2727_);
lean_dec(v_val_2718_);
lean_dec_ref(v_a_2712_);
lean_dec(v_val_2707_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2738_, lean_object* v_parserState_2739_, lean_object* v_cmdState_2740_, lean_object* v_prom_2741_, lean_object* v_sync_2742_, lean_object* v_parseCancelTk_2743_, lean_object* v_revCmds_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
uint8_t v_sync_boxed_2747_; lean_object* v_res_2748_; 
v_sync_boxed_2747_ = lean_unbox(v_sync_2742_);
v_res_2748_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2738_, v_parserState_2739_, v_cmdState_2740_, v_prom_2741_, v_sync_boxed_2747_, v_parseCancelTk_2743_, v_revCmds_2744_, v_a_2745_);
lean_dec_ref(v_a_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2749_, size_t v_i_2750_, size_t v_stop_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2749_, v_i_2750_, v_stop_2751_, v_b_2752_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2756_, lean_object* v_i_2757_, lean_object* v_stop_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
size_t v_i_boxed_2762_; size_t v_stop_boxed_2763_; lean_object* v_res_2764_; 
v_i_boxed_2762_ = lean_unbox_usize(v_i_2757_);
lean_dec(v_i_2757_);
v_stop_boxed_2763_ = lean_unbox_usize(v_stop_2758_);
lean_dec(v_stop_2758_);
v_res_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2756_, v_i_boxed_2762_, v_stop_boxed_2763_, v_b_2759_, v___y_2760_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_as_2756_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2765_, lean_object* v_opt_2766_){
_start:
{
lean_object* v_name_2767_; lean_object* v_map_2768_; lean_object* v___x_2769_; 
v_name_2767_ = lean_ctor_get(v_opt_2766_, 0);
v_map_2768_ = lean_ctor_get(v_opts_2765_, 0);
v___x_2769_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2768_, v_name_2767_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_box(0);
return v___x_2770_;
}
else
{
lean_object* v_val_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2780_; 
v_val_2771_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2773_ = v___x_2769_;
v_isShared_2774_ = v_isSharedCheck_2780_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_val_2771_);
lean_dec(v___x_2769_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2780_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
if (lean_obj_tag(v_val_2771_) == 0)
{
lean_object* v_v_2775_; lean_object* v___x_2777_; 
v_v_2775_ = lean_ctor_get(v_val_2771_, 0);
lean_inc_ref(v_v_2775_);
lean_dec_ref_known(v_val_2771_, 1);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v_v_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_v_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
lean_object* v___x_2779_; 
lean_del_object(v___x_2773_);
lean_dec(v_val_2771_);
v___x_2779_ = lean_box(0);
return v___x_2779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2781_, lean_object* v_opt_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2781_, v_opt_2782_);
lean_dec_ref(v_opt_2782_);
lean_dec_ref(v_opts_2781_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2786_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2784_);
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2788_, 0, v_x_2785_);
lean_ctor_set(v___x_2788_, 1, v___x_2786_);
lean_ctor_set(v___x_2788_, 2, v___x_2787_);
return v___x_2788_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2795_ = l_Lean_Array_toPArray_x27___redArg(v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
if (lean_obj_tag(v_a_2796_) == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = l_List_reverse___redArg(v_a_2797_);
return v___x_2798_;
}
else
{
lean_object* v_head_2799_; lean_object* v_tail_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2813_; 
v_head_2799_ = lean_ctor_get(v_a_2796_, 0);
v_tail_2800_ = lean_ctor_get(v_a_2796_, 1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2802_ = v_a_2796_;
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_tail_2800_);
lean_inc(v_head_2799_);
lean_dec(v_a_2796_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2804_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v_head_2799_);
v___x_2806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
v___x_2807_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v_a_2797_);
lean_ctor_set(v___x_2802_, 0, v___x_2808_);
v___x_2810_ = v___x_2802_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_a_2797_);
v___x_2810_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
v_a_2796_ = v_tail_2800_;
v_a_2797_ = v___x_2810_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2814_; double v___x_2815_; 
v___x_2814_ = lean_unsigned_to_nat(1000000000u);
v___x_2815_ = lean_float_of_nat(v___x_2814_);
return v___x_2815_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2833_ = l_Lean_MessageData_ofFormat(v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2834_, lean_object* v_stx_2835_, lean_object* v_origStx_2836_, lean_object* v_toProcessingContext_2837_, lean_object* v___x_2838_, lean_object* v_fileMap_2839_, lean_object* v_parserState_2840_, lean_object* v_a_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v___x_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_toProcessingContext_2847_; lean_object* v___x_2848_; 
v_toProcessingContext_2847_ = lean_ctor_get(v___y_2845_, 0);
lean_inc_ref(v_toProcessingContext_2847_);
lean_inc(v_stx_2835_);
v___x_2848_ = lean_apply_3(v_setupImports_2834_, v_stx_2835_, v_toProcessingContext_2847_, lean_box(0));
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_3061_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_3061_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_3061_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
if (lean_obj_tag(v_a_2849_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; 
lean_dec_ref(v___x_2844_);
lean_dec(v___x_2842_);
lean_dec_ref(v_parserState_2840_);
lean_dec_ref(v_fileMap_2839_);
lean_dec(v___x_2838_);
lean_dec_ref(v_toProcessingContext_2837_);
lean_dec(v_origStx_2836_);
lean_dec(v_stx_2835_);
v_a_2853_ = lean_ctor_get(v_a_2849_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v_a_2849_, 1);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v_a_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_3060_; 
v_a_2857_ = lean_ctor_get(v_a_2849_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_a_2849_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_2859_ = v_a_2849_;
v_isShared_2860_ = v_isSharedCheck_3060_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v_a_2849_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_3060_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v_mainModuleName_2862_; lean_object* v_package_x3f_2863_; uint8_t v_isModule_2864_; lean_object* v_imports_2865_; lean_object* v_opts_2866_; uint32_t v_trustLevel_2867_; lean_object* v_importArts_2868_; lean_object* v_plugins_2869_; double v___x_2870_; double v___x_2871_; double v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2877_; 
v___x_2861_ = lean_io_mono_nanos_now();
v_mainModuleName_2862_ = lean_ctor_get(v_a_2857_, 0);
lean_inc(v_mainModuleName_2862_);
v_package_x3f_2863_ = lean_ctor_get(v_a_2857_, 1);
lean_inc(v_package_x3f_2863_);
v_isModule_2864_ = lean_ctor_get_uint8(v_a_2857_, sizeof(void*)*6 + 4);
v_imports_2865_ = lean_ctor_get(v_a_2857_, 2);
lean_inc_ref(v_imports_2865_);
v_opts_2866_ = lean_ctor_get(v_a_2857_, 3);
lean_inc_ref(v_opts_2866_);
v_trustLevel_2867_ = lean_ctor_get_uint32(v_a_2857_, sizeof(void*)*6);
v_importArts_2868_ = lean_ctor_get(v_a_2857_, 4);
lean_inc(v_importArts_2868_);
v_plugins_2869_ = lean_ctor_get(v_a_2857_, 5);
lean_inc_ref(v_plugins_2869_);
lean_dec(v_a_2857_);
v___x_2870_ = lean_float_of_nat(v___x_2861_);
v___x_2871_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2872_ = lean_float_div(v___x_2870_, v___x_2871_);
v___x_2873_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2835_);
v___x_2874_ = l_Lean_MessageLog_empty;
v___x_2875_ = 1;
lean_inc(v_stx_2835_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_stx_2835_);
v___x_2877_ = v___x_2859_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_stx_2835_);
v___x_2877_ = v_reuseFailAlloc_3059_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_origStx_2836_);
lean_inc_ref(v___x_2877_);
lean_inc_ref(v_opts_2866_);
v___x_2879_ = l_Lean_Elab_processHeaderCore(v___x_2873_, v_imports_2865_, v_isModule_2864_, v_opts_2866_, v___x_2874_, v_toProcessingContext_2837_, v_trustLevel_2867_, v_plugins_2869_, v___x_2875_, v_mainModuleName_2862_, v_package_x3f_2863_, v_importArts_2868_, v___x_2877_, v___x_2878_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_3050_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_3050_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_3050_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_3049_; 
v_fst_2884_ = lean_ctor_get(v_a_2880_, 0);
v_snd_2885_ = lean_ctor_get(v_a_2880_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_a_2880_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_2887_ = v_a_2880_;
v_isShared_2888_ = v_isSharedCheck_3049_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_snd_2885_);
lean_inc(v_fst_2884_);
lean_dec(v_a_2880_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_3049_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; double v___x_2890_; double v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v_traceState_2909_; 
v___x_2889_ = lean_io_mono_nanos_now();
v___x_2890_ = lean_float_of_nat(v___x_2889_);
v___x_2891_ = lean_float_div(v___x_2890_, v___x_2871_);
lean_inc(v_snd_2885_);
v___x_2892_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2885_);
v___x_2893_ = l_Lean_MessageLog_hasErrors(v_snd_2885_);
if (v___x_2893_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_del_object(v___x_2851_);
lean_dec_ref(v___x_2844_);
v___x_3018_ = l_Lean_trace_profiler_output;
v___x_3019_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2866_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = l_Lean_trace_profiler_serve;
v___x_3021_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2866_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2909_ = v___x_3022_;
goto v___jp_2908_;
}
else
{
goto v___jp_3002_;
}
}
else
{
lean_dec_ref_known(v___x_3019_, 1);
goto v___jp_3002_;
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint64_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; size_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_del_object(v___x_2887_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_del_object(v___x_2882_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_opts_2866_);
lean_dec(v___x_2842_);
lean_dec_ref(v_parserState_2840_);
lean_dec_ref(v_fileMap_2839_);
lean_dec(v_stx_2835_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3024_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2838_, 2);
v___x_3026_ = l_Lean_Name_num___override(v___x_3025_, v___x_2838_);
v___x_3027_ = l_Lean_Name_str___override(v___x_3026_, v___x_3023_);
v___x_3028_ = l_Lean_Name_str___override(v___x_3027_, v___x_3024_);
v___x_3029_ = l_Lean_Name_str___override(v___x_3028_, v___x_3023_);
v___x_3030_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3031_ = l_Lean_Name_str___override(v___x_3029_, v___x_3030_);
v___x_3032_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_3033_ = l_Lean_Name_str___override(v___x_3031_, v___x_3032_);
v___x_3034_ = l_Lean_Name_toString(v___x_3033_, v___x_2875_);
v___x_3035_ = lean_box(0);
v___x_3036_ = 0ULL;
v___x_3037_ = lean_unsigned_to_nat(32u);
v___x_3038_ = lean_mk_empty_array_with_capacity(v___x_3037_);
v___x_3039_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3040_ = ((size_t)5ULL);
v___x_3041_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_3038_);
lean_ctor_set(v___x_3041_, 2, v___x_2838_);
lean_ctor_set(v___x_3041_, 3, v___x_2838_);
lean_ctor_set_usize(v___x_3041_, 4, v___x_3040_);
v___x_3042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set_uint64(v___x_3042_, sizeof(void*)*1, v___x_3036_);
v___x_3043_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3034_);
lean_ctor_set(v___x_3043_, 1, v___x_2892_);
lean_ctor_set(v___x_3043_, 2, v___x_3035_);
lean_ctor_set(v___x_3043_, 3, v___x_3042_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*4, v___x_2893_);
v___x_3044_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2844_);
v___x_3045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
lean_ctor_set(v___x_3045_, 2, v___x_3035_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_3045_);
v___x_3047_ = v___x_2851_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
v___jp_2894_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___y_2900_);
v___x_2902_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2902_, 0, v___y_2895_);
lean_ctor_set(v___x_2902_, 1, v___x_2892_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
lean_ctor_set(v___x_2902_, 3, v___y_2897_);
lean_ctor_set_uint8(v___x_2902_, sizeof(void*)*4, v___x_2893_);
v___x_2903_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2896_, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2904_, 0, v___y_2898_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
lean_ctor_set(v___x_2904_, 2, v___y_2899_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2904_);
v___x_2906_ = v___x_2882_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
v___jp_2908_:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_Language_Lean_reparseOptions(v_opts_2866_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v_env_2913_; lean_object* v_messages_2914_; lean_object* v_scopes_2915_; lean_object* v_usedQuotCtxts_2916_; lean_object* v_nextMacroScope_2917_; lean_object* v_maxRecDepth_2918_; lean_object* v_ngen_2919_; lean_object* v_auxDeclNGen_2920_; lean_object* v_snapshotTasks_2921_; lean_object* v_prevLinterStates_2922_; lean_object* v_codeQualityEntryTasks_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2991_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
lean_inc(v_fst_2884_);
v___x_2912_ = l_Lean_Elab_Command_mkState(v_fst_2884_, v_snd_2885_, v_a_2911_);
v_env_2913_ = lean_ctor_get(v___x_2912_, 0);
v_messages_2914_ = lean_ctor_get(v___x_2912_, 1);
v_scopes_2915_ = lean_ctor_get(v___x_2912_, 2);
v_usedQuotCtxts_2916_ = lean_ctor_get(v___x_2912_, 3);
v_nextMacroScope_2917_ = lean_ctor_get(v___x_2912_, 4);
v_maxRecDepth_2918_ = lean_ctor_get(v___x_2912_, 5);
v_ngen_2919_ = lean_ctor_get(v___x_2912_, 6);
v_auxDeclNGen_2920_ = lean_ctor_get(v___x_2912_, 7);
v_snapshotTasks_2921_ = lean_ctor_get(v___x_2912_, 10);
v_prevLinterStates_2922_ = lean_ctor_get(v___x_2912_, 11);
v_codeQualityEntryTasks_2923_ = lean_ctor_get(v___x_2912_, 12);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; lean_object* v_unused_2993_; 
v_unused_2992_ = lean_ctor_get(v___x_2912_, 9);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v___x_2912_, 8);
lean_dec(v_unused_2993_);
v___x_2925_ = v___x_2912_;
v_isShared_2926_ = v_isSharedCheck_2991_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2923_);
lean_inc(v_prevLinterStates_2922_);
lean_inc(v_snapshotTasks_2921_);
lean_inc(v_auxDeclNGen_2920_);
lean_inc(v_ngen_2919_);
lean_inc(v_maxRecDepth_2918_);
lean_inc(v_nextMacroScope_2917_);
lean_inc(v_usedQuotCtxts_2916_);
lean_inc(v_scopes_2915_);
lean_inc(v_messages_2914_);
lean_inc(v_env_2913_);
lean_dec(v___x_2912_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2991_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2927_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2928_ = lean_box(0);
lean_inc_n(v___x_2838_, 4);
v___x_2929_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2838_);
lean_ctor_set(v___x_2929_, 1, v___x_2838_);
lean_ctor_set(v___x_2929_, 2, v___x_2838_);
lean_ctor_set(v___x_2929_, 3, v___x_2838_);
lean_ctor_set(v___x_2929_, 4, v___x_2927_);
lean_ctor_set(v___x_2929_, 5, v___x_2927_);
lean_ctor_set(v___x_2929_, 6, v___x_2927_);
lean_ctor_set(v___x_2929_, 7, v___x_2927_);
lean_ctor_set(v___x_2929_, 8, v___x_2927_);
lean_ctor_set(v___x_2929_, 9, v___x_2927_);
lean_ctor_set(v___x_2929_, 10, v___x_2927_);
v___x_2930_ = l_Lean_Options_empty;
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_unsigned_to_nat(1u);
v___x_2934_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2935_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2935_, 0, v_fst_2884_);
lean_ctor_set(v___x_2935_, 1, v___x_2928_);
lean_ctor_set(v___x_2935_, 2, v_fileMap_2839_);
lean_ctor_set(v___x_2935_, 3, v___x_2929_);
lean_ctor_set(v___x_2935_, 4, v___x_2930_);
lean_ctor_set(v___x_2935_, 5, v___x_2931_);
lean_ctor_set(v___x_2935_, 6, v___x_2932_);
lean_ctor_set(v___x_2935_, 7, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2835_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v_stx_2835_);
lean_ctor_set(v___x_2887_, 0, v___x_2937_);
v___x_2939_ = v___x_2887_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2937_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_stx_2835_);
v___x_2939_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
v___x_2941_ = lean_unsigned_to_nat(2u);
v___x_2942_ = l_Lean_Syntax_getArg(v_stx_2835_, v___x_2941_);
lean_dec(v_stx_2835_);
v___x_2943_ = l_Lean_Syntax_getArgs(v___x_2942_);
lean_dec(v___x_2942_);
v___x_2944_ = lean_array_to_list(v___x_2943_);
v___x_2945_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2944_, v___x_2932_);
v___x_2946_ = l_Lean_List_toPArray_x27___redArg(v___x_2945_);
v___x_2947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2940_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2936_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_mk_empty_array_with_capacity(v___x_2933_);
v___x_2950_ = lean_array_push(v___x_2949_, v___x_2948_);
v___x_2951_ = l_Lean_Array_toPArray_x27___redArg(v___x_2950_);
lean_dec_ref(v___x_2950_);
lean_inc_ref(v___x_2951_);
v___x_2952_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2952_, 0, v___x_2927_);
lean_ctor_set(v___x_2952_, 1, v___x_2927_);
lean_ctor_set(v___x_2952_, 2, v___x_2951_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*3, v___x_2875_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 9, v_traceState_2909_);
lean_ctor_set(v___x_2925_, 8, v___x_2952_);
v___x_2954_ = v___x_2925_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_env_2913_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_messages_2914_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_scopes_2915_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_usedQuotCtxts_2916_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v_nextMacroScope_2917_);
lean_ctor_set(v_reuseFailAlloc_2989_, 5, v_maxRecDepth_2918_);
lean_ctor_set(v_reuseFailAlloc_2989_, 6, v_ngen_2919_);
lean_ctor_set(v_reuseFailAlloc_2989_, 7, v_auxDeclNGen_2920_);
lean_ctor_set(v_reuseFailAlloc_2989_, 8, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2989_, 9, v_traceState_2909_);
lean_ctor_set(v_reuseFailAlloc_2989_, 10, v_snapshotTasks_2921_);
lean_ctor_set(v_reuseFailAlloc_2989_, 11, v_prevLinterStates_2922_);
lean_ctor_set(v_reuseFailAlloc_2989_, 12, v_codeQualityEntryTasks_2923_);
v___x_2954_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; size_t v___x_2965_; lean_object* v___x_2966_; lean_object* v_size_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; uint64_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2955_ = lean_io_promise_new();
v___x_2956_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_2956_);
lean_inc(v___x_2955_);
lean_inc_ref(v___x_2954_);
v___x_2957_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2928_, v_parserState_2840_, v___x_2954_, v___x_2955_, v___x_2875_, v___x_2956_, v___x_2932_, v_a_2841_);
v___x_2958_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2959_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2960_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2838_, 3);
v___x_2961_ = l_Lean_Name_num___override(v___x_2960_, v___x_2838_);
v___x_2962_ = lean_unsigned_to_nat(32u);
v___x_2963_ = lean_mk_empty_array_with_capacity(v___x_2962_);
v___x_2964_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2965_ = ((size_t)5ULL);
v___x_2966_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2963_);
lean_ctor_set(v___x_2966_, 2, v___x_2838_);
lean_ctor_set(v___x_2966_, 3, v___x_2838_);
lean_ctor_set_usize(v___x_2966_, 4, v___x_2965_);
v_size_2967_ = lean_ctor_get(v___x_2951_, 2);
lean_inc(v_size_2967_);
v___x_2968_ = l_Lean_Name_str___override(v___x_2961_, v___x_2958_);
v___x_2969_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2842_);
v___x_2970_ = l_Lean_Name_str___override(v___x_2968_, v___x_2959_);
v___x_2971_ = l_Lean_Name_str___override(v___x_2970_, v___x_2958_);
v___x_2972_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2973_ = l_Lean_Name_str___override(v___x_2971_, v___x_2972_);
v___x_2974_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2975_ = l_Lean_Name_str___override(v___x_2973_, v___x_2974_);
v___x_2976_ = l_Lean_Name_toString(v___x_2975_, v___x_2875_);
v___x_2977_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2978_ = 0ULL;
v___x_2979_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2979_, 0, v___x_2966_);
lean_ctor_set_uint64(v___x_2979_, sizeof(void*)*1, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2956_);
v___x_2981_ = l_IO_Promise_result_x21___redArg(v___x_2955_);
lean_dec(v___x_2955_);
v___x_2982_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2842_);
lean_ctor_set(v___x_2982_, 1, v___x_2969_);
lean_ctor_set(v___x_2982_, 2, v___x_2980_);
lean_ctor_set(v___x_2982_, 3, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2954_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_inc_ref(v___x_2979_);
lean_inc_ref(v___x_2976_);
v___x_2985_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2985_, 0, v___x_2976_);
lean_ctor_set(v___x_2985_, 1, v___x_2977_);
lean_ctor_set(v___x_2985_, 2, v___x_2928_);
lean_ctor_set(v___x_2985_, 3, v___x_2979_);
lean_ctor_set_uint8(v___x_2985_, sizeof(void*)*4, v___x_2893_);
v___x_2986_ = lean_nat_dec_lt(v___x_2838_, v_size_2967_);
lean_dec(v_size_2967_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_dec_ref(v___x_2951_);
lean_dec(v___x_2838_);
v___x_2987_ = l_outOfBounds___redArg(v___x_2843_);
v___y_2895_ = v___x_2976_;
v___y_2896_ = v___x_2877_;
v___y_2897_ = v___x_2979_;
v___y_2898_ = v___x_2985_;
v___y_2899_ = v___x_2984_;
v___y_2900_ = v___x_2987_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2843_, v___x_2951_, v___x_2838_);
lean_dec(v___x_2838_);
lean_dec_ref(v___x_2951_);
v___y_2895_ = v___x_2976_;
v___y_2896_ = v___x_2877_;
v___y_2897_ = v___x_2979_;
v___y_2898_ = v___x_2985_;
v___y_2899_ = v___x_2984_;
v___y_2900_ = v___x_2988_;
goto v___jp_2894_;
}
}
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref(v_traceState_2909_);
lean_dec_ref(v___x_2892_);
lean_del_object(v___x_2887_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_del_object(v___x_2882_);
lean_dec_ref(v___x_2877_);
lean_dec(v___x_2842_);
lean_dec_ref(v_parserState_2840_);
lean_dec_ref(v_fileMap_2839_);
lean_dec(v___x_2838_);
lean_dec(v_stx_2835_);
v_a_2994_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2910_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2910_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
v___jp_3002_:
{
uint64_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3003_ = 0ULL;
v___x_3004_ = lean_box(0);
v___x_3005_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_3006_ = lean_box(0);
v___x_3007_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3008_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3008_, 0, v___x_3005_);
lean_ctor_set(v___x_3008_, 1, v___x_3006_);
lean_ctor_set(v___x_3008_, 2, v___x_3007_);
lean_ctor_set_float(v___x_3008_, sizeof(void*)*3, v___x_2872_);
lean_ctor_set_float(v___x_3008_, sizeof(void*)*3 + 8, v___x_2891_);
lean_ctor_set_uint8(v___x_3008_, sizeof(void*)*3 + 16, v___x_2875_);
v___x_3009_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3010_ = lean_mk_empty_array_with_capacity(v___x_2838_);
v___x_3011_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3008_);
lean_ctor_set(v___x_3011_, 1, v___x_3009_);
lean_ctor_set(v___x_3011_, 2, v___x_3010_);
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3004_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_unsigned_to_nat(1u);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_3013_);
v___x_3015_ = lean_array_push(v___x_3014_, v___x_3012_);
v___x_3016_ = l_Lean_Array_toPArray_x27___redArg(v___x_3015_);
lean_dec_ref(v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set_uint64(v___x_3017_, sizeof(void*)*1, v___x_3003_);
v_traceState_2909_ = v___x_3017_;
goto v___jp_2908_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_opts_2866_);
lean_del_object(v___x_2851_);
lean_dec_ref(v___x_2844_);
lean_dec(v___x_2842_);
lean_dec_ref(v_parserState_2840_);
lean_dec_ref(v_fileMap_2839_);
lean_dec(v___x_2838_);
lean_dec(v_stx_2835_);
v_a_3051_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_2879_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_2879_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
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
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec_ref(v___x_2844_);
lean_dec(v___x_2842_);
lean_dec_ref(v_parserState_2840_);
lean_dec_ref(v_fileMap_2839_);
lean_dec(v___x_2838_);
lean_dec_ref(v_toProcessingContext_2837_);
lean_dec(v_origStx_2836_);
lean_dec(v_stx_2835_);
v_a_3062_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2848_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2848_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3070_, lean_object* v_stx_3071_, lean_object* v_origStx_3072_, lean_object* v_toProcessingContext_3073_, lean_object* v___x_3074_, lean_object* v_fileMap_3075_, lean_object* v_parserState_3076_, lean_object* v_a_3077_, lean_object* v___x_3078_, lean_object* v___x_3079_, lean_object* v___x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3070_, v_stx_3071_, v_origStx_3072_, v_toProcessingContext_3073_, v___x_3074_, v_fileMap_3075_, v_parserState_3076_, v_a_3077_, v___x_3078_, v___x_3079_, v___x_3080_, v___y_3081_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v___x_3079_);
lean_dec_ref(v_a_3077_);
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___f_3085_; 
v___x_3084_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3085_, 0, v___x_3084_);
return v___f_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3086_, lean_object* v_stx_3087_, lean_object* v_origStx_3088_, lean_object* v_parserState_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_toProcessingContext_3092_; lean_object* v_fileMap_3093_; lean_object* v_endPos_3094_; lean_object* v___x_3095_; lean_object* v___f_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_toProcessingContext_3092_ = lean_ctor_get(v_a_3090_, 0);
v_fileMap_3093_ = lean_ctor_get(v_toProcessingContext_3092_, 2);
v_endPos_3094_ = lean_ctor_get(v_toProcessingContext_3092_, 3);
v___x_3095_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3096_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3097_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3090_, 2);
lean_inc_ref(v_fileMap_3093_);
lean_inc_ref(v_toProcessingContext_3092_);
v___f_3100_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3100_, 0, v_setupImports_3086_);
lean_closure_set(v___f_3100_, 1, v_stx_3087_);
lean_closure_set(v___f_3100_, 2, v_origStx_3088_);
lean_closure_set(v___f_3100_, 3, v_toProcessingContext_3092_);
lean_closure_set(v___f_3100_, 4, v___x_3099_);
lean_closure_set(v___f_3100_, 5, v_fileMap_3093_);
lean_closure_set(v___f_3100_, 6, v_parserState_3089_);
lean_closure_set(v___f_3100_, 7, v_a_3090_);
lean_closure_set(v___f_3100_, 8, v___x_3098_);
lean_closure_set(v___f_3100_, 9, v___x_3097_);
lean_closure_set(v___f_3100_, 10, v___x_3095_);
lean_inc(v_endPos_3094_);
v___x_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set(v___x_3101_, 1, v_endPos_3094_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
v___x_3103_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3103_, 0, lean_box(0));
lean_closure_set(v___x_3103_, 1, v___f_3096_);
lean_closure_set(v___x_3103_, 2, v___f_3100_);
lean_closure_set(v___x_3103_, 3, v_a_3090_);
v___x_3104_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3098_, v___x_3098_, v___x_3102_, v___x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3105_, lean_object* v_stx_3106_, lean_object* v_origStx_3107_, lean_object* v_parserState_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3105_, v_stx_3106_, v_origStx_3107_, v_parserState_3108_, v_a_3109_);
lean_dec_ref(v_a_3109_);
return v_res_3111_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_box(0);
v___x_3113_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3112_);
return v___x_3113_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3(void){
_start:
{
uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = 1;
v___x_3119_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__2));
v___x_3120_ = l_Lean_Name_toString(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3121_ = 0;
v___x_3122_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3123_ = lean_box(0);
v___x_3124_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3125_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3126_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3124_);
lean_ctor_set(v___x_3126_, 2, v___x_3123_);
lean_ctor_set(v___x_3126_, 3, v___x_3122_);
lean_ctor_set_uint8(v___x_3126_, sizeof(void*)*4, v___x_3121_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3127_, lean_object* v_cmdState_3128_, lean_object* v_a_3129_, lean_object* v_toSnapshot_3130_, lean_object* v_newStx_3131_, lean_object* v_oldCmd_3132_){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v_diagnostics_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3162_; 
v___x_3134_ = lean_io_promise_new();
v___x_3135_ = l_IO_CancelToken_new();
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_oldCmd_3132_);
v___x_3137_ = 1;
v___x_3138_ = lean_box(0);
lean_inc_ref(v___x_3135_);
lean_inc(v___x_3134_);
lean_inc_ref(v_cmdState_3128_);
v___x_3139_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3136_, v_newParserState_3127_, v_cmdState_3128_, v___x_3134_, v___x_3137_, v___x_3135_, v___x_3138_, v_a_3129_);
v_diagnostics_3140_ = lean_ctor_get(v_toSnapshot_3130_, 1);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_toSnapshot_3130_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3163_ = lean_ctor_get(v_toSnapshot_3130_, 3);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_toSnapshot_3130_, 2);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_toSnapshot_3130_, 0);
lean_dec(v_unused_3165_);
v___x_3142_ = v_toSnapshot_3130_;
v_isShared_3143_ = v_isSharedCheck_3162_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_diagnostics_3140_);
lean_dec(v_toSnapshot_3130_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3162_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0);
v___x_3146_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3147_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3135_);
v___x_3149_ = l_IO_Promise_result_x21___redArg(v___x_3134_);
lean_dec(v___x_3134_);
v___x_3150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3144_);
lean_ctor_set(v___x_3150_, 1, v___x_3145_);
lean_ctor_set(v___x_3150_, 2, v___x_3148_);
lean_ctor_set(v___x_3150_, 3, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v_cmdState_3128_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
v___x_3153_ = 0;
v___x_3154_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v_newStx_3131_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 3, v___x_3147_);
lean_ctor_set(v___x_3142_, 2, v___x_3144_);
lean_ctor_set(v___x_3142_, 0, v___x_3146_);
v___x_3157_ = v___x_3142_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_diagnostics_3140_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3161_, 3, v___x_3147_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*4, v___x_3153_);
v___x_3158_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3155_, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3154_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
lean_ctor_set(v___x_3159_, 2, v___x_3152_);
v___x_3160_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3144_, v___x_3159_);
return v___x_3160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3166_, lean_object* v_cmdState_3167_, lean_object* v_a_3168_, lean_object* v_toSnapshot_3169_, lean_object* v_newStx_3170_, lean_object* v_oldCmd_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3166_, v_cmdState_3167_, v_a_3168_, v_toSnapshot_3169_, v_newStx_3170_, v_oldCmd_3171_);
lean_dec_ref(v_a_3168_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3174_, lean_object* v_a_3175_, lean_object* v_newStx_3176_, lean_object* v___x_3177_, lean_object* v_oldProcessed_3178_){
_start:
{
lean_object* v_result_x3f_3180_; 
v_result_x3f_3180_ = lean_ctor_get(v_oldProcessed_3178_, 2);
if (lean_obj_tag(v_result_x3f_3180_) == 1)
{
lean_object* v_val_3181_; lean_object* v_firstCmdSnap_3182_; lean_object* v_toSnapshot_3183_; lean_object* v_cmdState_3184_; lean_object* v_stx_x3f_3185_; lean_object* v___f_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; 
v_val_3181_ = lean_ctor_get(v_result_x3f_3180_, 0);
lean_inc(v_val_3181_);
v_firstCmdSnap_3182_ = lean_ctor_get(v_val_3181_, 1);
lean_inc_ref(v_firstCmdSnap_3182_);
v_toSnapshot_3183_ = lean_ctor_get(v_oldProcessed_3178_, 0);
lean_inc_ref(v_toSnapshot_3183_);
lean_dec_ref(v_oldProcessed_3178_);
v_cmdState_3184_ = lean_ctor_get(v_val_3181_, 0);
lean_inc_ref(v_cmdState_3184_);
lean_dec(v_val_3181_);
v_stx_x3f_3185_ = lean_ctor_get(v_firstCmdSnap_3182_, 0);
lean_inc(v_stx_x3f_3185_);
lean_inc_ref(v_a_3175_);
v___f_3186_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3186_, 0, v_newParserState_3174_);
lean_closure_set(v___f_3186_, 1, v_cmdState_3184_);
lean_closure_set(v___f_3186_, 2, v_a_3175_);
lean_closure_set(v___f_3186_, 3, v_toSnapshot_3183_);
lean_closure_set(v___f_3186_, 4, v_newStx_3176_);
v___x_3187_ = lean_box(0);
v___x_3188_ = 1;
v___x_3189_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3182_, v___f_3186_, v_stx_x3f_3185_, v___x_3177_, v___x_3187_, v___x_3188_);
return v___x_3189_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec(v___x_3177_);
lean_dec_ref(v_newParserState_3174_);
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_newStx_3176_);
v___x_3191_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3190_, v_oldProcessed_3178_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3192_, lean_object* v_a_3193_, lean_object* v_newStx_3194_, lean_object* v___x_3195_, lean_object* v_oldProcessed_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3192_, v_a_3193_, v_newStx_3194_, v___x_3195_, v_oldProcessed_3196_);
lean_dec_ref(v_a_3193_);
return v_res_3198_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3199_ = 0;
v___x_3200_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3201_ = lean_box(0);
v___x_3202_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3203_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3204_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3202_);
lean_ctor_set(v___x_3204_, 2, v___x_3201_);
lean_ctor_set(v___x_3204_, 3, v___x_3200_);
lean_ctor_set_uint8(v___x_3204_, sizeof(void*)*4, v___x_3199_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3205_, lean_object* v_a_3206_, lean_object* v_old_3207_, lean_object* v_newStx_3208_, lean_object* v_newParserState_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_result_x3f_3212_; 
v_result_x3f_3212_ = lean_ctor_get(v_old_3207_, 4);
lean_inc(v_result_x3f_3212_);
if (lean_obj_tag(v_result_x3f_3212_) == 1)
{
lean_object* v_val_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3267_; 
v_val_3213_ = lean_ctor_get(v_result_x3f_3212_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_result_x3f_3212_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3215_ = v_result_x3f_3212_;
v_isShared_3216_ = v_isSharedCheck_3267_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_val_3213_);
lean_dec(v_result_x3f_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3267_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v_processedSnap_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3265_; 
v_processedSnap_3217_ = lean_ctor_get(v_val_3213_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_val_3213_);
if (v_isSharedCheck_3265_ == 0)
{
lean_object* v_unused_3266_; 
v_unused_3266_ = lean_ctor_get(v_val_3213_, 0);
lean_dec(v_unused_3266_);
v___x_3219_ = v_val_3213_;
v_isShared_3220_ = v_isSharedCheck_3265_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_processedSnap_3217_);
lean_dec(v_val_3213_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3265_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_toSnapshot_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3260_; 
v_toSnapshot_3221_ = lean_ctor_get(v_old_3207_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_old_3207_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; lean_object* v_unused_3262_; lean_object* v_unused_3263_; lean_object* v_unused_3264_; 
v_unused_3261_ = lean_ctor_get(v_old_3207_, 4);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_old_3207_, 3);
lean_dec(v_unused_3262_);
v_unused_3263_ = lean_ctor_get(v_old_3207_, 2);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_old_3207_, 1);
lean_dec(v_unused_3264_);
v___x_3223_ = v_old_3207_;
v_isShared_3224_ = v_isSharedCheck_3260_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_toSnapshot_3221_);
lean_dec(v_old_3207_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3260_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v_pos_3225_; lean_object* v_endPos_3226_; lean_object* v_stx_x3f_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v_diagnostics_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3256_; 
v_pos_3225_ = lean_ctor_get(v_newParserState_3209_, 0);
v_endPos_3226_ = lean_ctor_get(v_toProcessingContext_3205_, 3);
v_stx_x3f_3227_ = lean_ctor_get(v_processedSnap_3217_, 0);
lean_inc(v_stx_x3f_3227_);
lean_inc(v_endPos_3226_);
lean_inc(v_pos_3225_);
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_pos_3225_);
lean_ctor_set(v___x_3228_, 1, v_endPos_3226_);
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_inc_ref(v___x_3229_);
lean_inc(v_newStx_3208_);
lean_inc_ref(v_a_3206_);
lean_inc_ref(v_newParserState_3209_);
v___f_3230_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3230_, 0, v_newParserState_3209_);
lean_closure_set(v___f_3230_, 1, v_a_3206_);
lean_closure_set(v___f_3230_, 2, v_newStx_3208_);
lean_closure_set(v___f_3230_, 3, v___x_3229_);
v___x_3231_ = lean_box(0);
v___x_3232_ = 1;
v___x_3233_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3217_, v___f_3230_, v_stx_x3f_3227_, v___x_3229_, v___x_3231_, v___x_3232_);
v_diagnostics_3234_ = lean_ctor_get(v_toSnapshot_3221_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_toSnapshot_3221_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; lean_object* v_unused_3258_; lean_object* v_unused_3259_; 
v_unused_3257_ = lean_ctor_get(v_toSnapshot_3221_, 3);
lean_dec(v_unused_3257_);
v_unused_3258_ = lean_ctor_get(v_toSnapshot_3221_, 2);
lean_dec(v_unused_3258_);
v_unused_3259_ = lean_ctor_get(v_toSnapshot_3221_, 0);
lean_dec(v_unused_3259_);
v___x_3236_ = v_toSnapshot_3221_;
v_isShared_3237_ = v_isSharedCheck_3256_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_diagnostics_3234_);
lean_dec(v_toSnapshot_3221_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3256_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3238_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3239_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 1, v___x_3233_);
lean_ctor_set(v___x_3219_, 0, v_newParserState_3209_);
v___x_3241_ = v___x_3219_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_newParserState_3209_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3233_);
v___x_3241_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3241_);
v___x_3243_ = v___x_3215_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
uint8_t v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3244_ = 0;
v___x_3245_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3208_);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_newStx_3208_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 3, v___x_3239_);
lean_ctor_set(v___x_3236_, 2, v___x_3231_);
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3248_ = v___x_3236_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_diagnostics_3234_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3253_, 3, v___x_3239_);
v___x_3248_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
lean_ctor_set_uint8(v___x_3248_, sizeof(void*)*4, v___x_3244_);
v___x_3249_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3246_, v___x_3248_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 4, v___x_3243_);
lean_ctor_set(v___x_3223_, 3, v_newStx_3208_);
lean_ctor_set(v___x_3223_, 2, v_toProcessingContext_3205_);
lean_ctor_set(v___x_3223_, 1, v___x_3249_);
lean_ctor_set(v___x_3223_, 0, v___x_3245_);
v___x_3251_ = v___x_3223_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_toProcessingContext_3205_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_newStx_3208_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v___x_3243_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
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
lean_dec(v_result_x3f_3212_);
lean_dec_ref(v_newParserState_3209_);
lean_dec(v_newStx_3208_);
lean_dec_ref(v_toProcessingContext_3205_);
return v_old_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3268_, lean_object* v_a_3269_, lean_object* v_old_3270_, lean_object* v_newStx_3271_, lean_object* v_newParserState_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3268_, v_a_3269_, v_old_3270_, v_newStx_3271_, v_newParserState_3272_, v___y_3273_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v_a_3269_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3276_, lean_object* v_setupImports_3277_, lean_object* v_old_x3f_3278_, lean_object* v___x_3279_, lean_object* v___f_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; 
lean_inc_ref(v_toProcessingContext_3276_);
v___x_3283_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3276_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3352_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3352_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3352_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_snd_3288_; lean_object* v_fst_3289_; lean_object* v_fst_3290_; lean_object* v_snd_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3351_; 
v_snd_3288_ = lean_ctor_get(v_a_3284_, 1);
lean_inc(v_snd_3288_);
v_fst_3289_ = lean_ctor_get(v_a_3284_, 0);
lean_inc(v_fst_3289_);
lean_dec(v_a_3284_);
v_fst_3290_ = lean_ctor_get(v_snd_3288_, 0);
v_snd_3291_ = lean_ctor_get(v_snd_3288_, 1);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_snd_3288_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3293_ = v_snd_3288_;
v_isShared_3294_ = v_isSharedCheck_3351_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_snd_3291_);
lean_inc(v_fst_3290_);
lean_dec(v_snd_3288_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3351_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
uint8_t v___x_3295_; 
v___x_3295_ = l_Lean_MessageLog_hasErrors(v_snd_3291_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___y_3298_; 
lean_inc(v_fst_3289_);
v___x_3296_ = l_Lean_Syntax_unsetTrailing(v_fst_3289_);
if (lean_obj_tag(v_old_x3f_3278_) == 1)
{
lean_object* v_val_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3334_; 
v_val_3319_ = lean_ctor_get(v_old_x3f_3278_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_old_x3f_3278_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3321_ = v_old_x3f_3278_;
v_isShared_3322_ = v_isSharedCheck_3334_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_val_3319_);
lean_dec(v_old_x3f_3278_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3334_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_stx_3323_; lean_object* v_result_x3f_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v_stx_3323_ = lean_ctor_get(v_val_3319_, 3);
v_result_x3f_3324_ = lean_ctor_get(v_val_3319_, 4);
lean_inc(v_stx_3323_);
v___x_3325_ = l_Lean_Syntax_unsetTrailing(v_stx_3323_);
lean_inc(v___x_3296_);
v___x_3326_ = l_Lean_Syntax_eqWithInfo(v___x_3296_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_inc(v_result_x3f_3324_);
lean_del_object(v___x_3321_);
lean_dec(v_val_3319_);
lean_dec_ref(v___f_3280_);
if (lean_obj_tag(v_result_x3f_3324_) == 0)
{
lean_dec_ref(v___x_3279_);
v___y_3298_ = v___y_3281_;
goto v___jp_3297_;
}
else
{
lean_object* v_val_3327_; lean_object* v_processedSnap_3328_; lean_object* v___x_3329_; 
v_val_3327_ = lean_ctor_get(v_result_x3f_3324_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v_result_x3f_3324_, 1);
v_processedSnap_3328_ = lean_ctor_get(v_val_3327_, 1);
lean_inc_ref(v_processedSnap_3328_);
lean_dec(v_val_3327_);
v___x_3329_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3279_, v_processedSnap_3328_);
v___y_3298_ = v___y_3281_;
goto v___jp_3297_;
}
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3332_; 
lean_dec(v___x_3296_);
lean_del_object(v___x_3293_);
lean_dec(v_snd_3291_);
lean_del_object(v___x_3286_);
lean_dec_ref(v___x_3279_);
lean_dec_ref(v_setupImports_3277_);
lean_dec_ref(v_toProcessingContext_3276_);
lean_inc_ref(v___y_3281_);
v___x_3330_ = lean_apply_5(v___f_3280_, v_val_3319_, v_fst_3289_, v_fst_3290_, v___y_3281_, lean_box(0));
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3330_);
v___x_3332_ = v___x_3321_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
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
else
{
lean_dec_ref(v___f_3280_);
lean_dec_ref(v___x_3279_);
lean_dec(v_old_x3f_3278_);
v___y_3298_ = v___y_3281_;
goto v___jp_3297_;
}
v___jp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3299_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3291_);
lean_inc(v_fst_3290_);
lean_inc(v_fst_3289_);
v___x_3300_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3277_, v___x_3296_, v_fst_3289_, v_fst_3290_, v___y_3298_);
v___x_3301_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3302_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_unsigned_to_nat(32u);
v___x_3305_ = lean_mk_empty_array_with_capacity(v___x_3304_);
lean_dec_ref(v___x_3305_);
v___x_3306_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 1, v___x_3300_);
v___x_3308_ = v___x_3293_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_fst_3290_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___x_3300_);
v___x_3308_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3310_, 0, v___x_3301_);
lean_ctor_set(v___x_3310_, 1, v___x_3302_);
lean_ctor_set(v___x_3310_, 2, v___x_3303_);
lean_ctor_set(v___x_3310_, 3, v___x_3306_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*4, v___x_3295_);
lean_inc(v_fst_3289_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_fst_3289_);
v___x_3312_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3312_, 0, v___x_3301_);
lean_ctor_set(v___x_3312_, 1, v___x_3299_);
lean_ctor_set(v___x_3312_, 2, v___x_3303_);
lean_ctor_set(v___x_3312_, 3, v___x_3306_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*4, v___x_3295_);
v___x_3313_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3311_, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3310_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
lean_ctor_set(v___x_3314_, 2, v_toProcessingContext_3276_);
lean_ctor_set(v___x_3314_, 3, v_fst_3289_);
lean_ctor_set(v___x_3314_, 4, v___x_3309_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3314_);
v___x_3316_ = v___x_3286_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
lean_del_object(v___x_3293_);
lean_dec(v_fst_3290_);
lean_dec_ref(v___f_3280_);
lean_dec_ref(v___x_3279_);
lean_dec(v_old_x3f_3278_);
lean_dec_ref(v_setupImports_3277_);
v___x_3335_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3291_);
v___x_3336_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3);
v___x_3337_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_unsigned_to_nat(32u);
v___x_3340_ = lean_mk_empty_array_with_capacity(v___x_3339_);
lean_dec_ref(v___x_3340_);
v___x_3341_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3342_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3342_, 0, v___x_3336_);
lean_ctor_set(v___x_3342_, 1, v___x_3337_);
lean_ctor_set(v___x_3342_, 2, v___x_3338_);
lean_ctor_set(v___x_3342_, 3, v___x_3341_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*4, v___x_3295_);
lean_inc(v_fst_3289_);
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_fst_3289_);
v___x_3344_ = 0;
v___x_3345_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3345_, 0, v___x_3336_);
lean_ctor_set(v___x_3345_, 1, v___x_3335_);
lean_ctor_set(v___x_3345_, 2, v___x_3338_);
lean_ctor_set(v___x_3345_, 3, v___x_3341_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*4, v___x_3344_);
v___x_3346_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3343_, v___x_3345_);
v___x_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3342_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
lean_ctor_set(v___x_3347_, 2, v_toProcessingContext_3276_);
lean_ctor_set(v___x_3347_, 3, v_fst_3289_);
lean_ctor_set(v___x_3347_, 4, v___x_3338_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3347_);
v___x_3349_ = v___x_3286_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v___f_3280_);
lean_dec_ref(v___x_3279_);
lean_dec(v_old_x3f_3278_);
lean_dec_ref(v_setupImports_3277_);
lean_dec_ref(v_toProcessingContext_3276_);
v_a_3353_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3283_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3283_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3361_, lean_object* v_setupImports_3362_, lean_object* v_old_x3f_3363_, lean_object* v___x_3364_, lean_object* v___f_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3361_, v_setupImports_3362_, v_old_x3f_3363_, v___x_3364_, v___f_3365_, v___y_3366_);
lean_dec_ref(v___y_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3369_, lean_object* v_toProcessingContext_3370_, lean_object* v_x_3371_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3372_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3369_);
v___x_3373_ = lean_box(0);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3375_, 0, v_x_3371_);
lean_ctor_set(v___x_3375_, 1, v___x_3372_);
lean_ctor_set(v___x_3375_, 2, v_toProcessingContext_3370_);
lean_ctor_set(v___x_3375_, 3, v___x_3373_);
lean_ctor_set(v___x_3375_, 4, v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3376_, lean_object* v_old_x3f_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v_toProcessingContext_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; 
v_toProcessingContext_3380_ = lean_ctor_get(v_a_3378_, 0);
v___x_3381_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3382_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3378_);
lean_inc_ref_n(v_toProcessingContext_3380_, 3);
v___f_3383_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3383_, 0, v_toProcessingContext_3380_);
lean_closure_set(v___f_3383_, 1, v_a_3378_);
lean_inc(v_old_x3f_3377_);
v___f_3384_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3384_, 0, v_toProcessingContext_3380_);
lean_closure_set(v___f_3384_, 1, v_setupImports_3376_);
lean_closure_set(v___f_3384_, 2, v_old_x3f_3377_);
lean_closure_set(v___f_3384_, 3, v___x_3382_);
lean_closure_set(v___f_3384_, 4, v___f_3383_);
v___f_3385_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3385_, 0, v___x_3381_);
lean_closure_set(v___f_3385_, 1, v_toProcessingContext_3380_);
if (lean_obj_tag(v_old_x3f_3377_) == 1)
{
lean_object* v_val_3386_; lean_object* v_result_x3f_3387_; 
v_val_3386_ = lean_ctor_get(v_old_x3f_3377_, 0);
lean_inc(v_val_3386_);
lean_dec_ref_known(v_old_x3f_3377_, 1);
v_result_x3f_3387_ = lean_ctor_get(v_val_3386_, 4);
if (lean_obj_tag(v_result_x3f_3387_) == 1)
{
lean_object* v_stx_3388_; lean_object* v_val_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_stx_3388_ = lean_ctor_get(v_val_3386_, 3);
lean_inc(v_stx_3388_);
v_val_3389_ = lean_ctor_get(v_result_x3f_3387_, 0);
lean_inc(v_val_3386_);
v___x_3390_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3386_);
v___x_3391_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3390_);
if (lean_obj_tag(v___x_3391_) == 1)
{
lean_object* v_val_3392_; 
v_val_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_val_3392_);
lean_dec_ref_known(v___x_3391_, 1);
if (lean_obj_tag(v_val_3392_) == 1)
{
lean_object* v_val_3393_; lean_object* v_firstCmdSnap_3394_; lean_object* v___x_3395_; 
v_val_3393_ = lean_ctor_get(v_val_3392_, 0);
lean_inc(v_val_3393_);
lean_dec_ref_known(v_val_3392_, 1);
v_firstCmdSnap_3394_ = lean_ctor_get(v_val_3393_, 1);
lean_inc_ref(v_firstCmdSnap_3394_);
lean_dec(v_val_3393_);
v___x_3395_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3394_);
if (lean_obj_tag(v___x_3395_) == 1)
{
lean_object* v_val_3396_; lean_object* v_nextCmdSnap_x3f_3397_; 
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v_nextCmdSnap_x3f_3397_ = lean_ctor_get(v_val_3396_, 4);
lean_inc(v_nextCmdSnap_x3f_3397_);
lean_dec(v_val_3396_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3397_) == 0)
{
lean_object* v___x_3398_; 
lean_dec(v_stx_3388_);
lean_dec(v_val_3386_);
v___x_3398_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3398_;
}
else
{
lean_object* v_val_3399_; lean_object* v___x_3400_; 
v_val_3399_ = lean_ctor_get(v_nextCmdSnap_x3f_3397_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3397_, 1);
v___x_3400_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3399_);
if (lean_obj_tag(v___x_3400_) == 1)
{
lean_object* v_val_3401_; lean_object* v_parserState_3402_; lean_object* v_pos_3403_; uint8_t v___x_3404_; 
v_val_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v_parserState_3402_ = lean_ctor_get(v_val_3401_, 2);
lean_inc_ref(v_parserState_3402_);
lean_dec(v_val_3401_);
v_pos_3403_ = lean_ctor_get(v_parserState_3402_, 0);
lean_inc(v_pos_3403_);
lean_dec_ref(v_parserState_3402_);
v___x_3404_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3403_, v_a_3378_);
lean_dec(v_pos_3403_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
lean_dec(v_stx_3388_);
lean_dec(v_val_3386_);
v___x_3405_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3405_;
}
else
{
lean_object* v_parserState_3406_; lean_object* v___x_3407_; 
lean_dec_ref(v___f_3385_);
lean_dec_ref(v___f_3384_);
v_parserState_3406_ = lean_ctor_get(v_val_3389_, 0);
lean_inc_ref(v_parserState_3406_);
lean_inc_ref(v_toProcessingContext_3380_);
v___x_3407_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3380_, v_a_3378_, v_val_3386_, v_stx_3388_, v_parserState_3406_, v_a_3378_);
return v___x_3407_;
}
}
else
{
lean_object* v___x_3408_; 
lean_dec(v___x_3400_);
lean_dec(v_stx_3388_);
lean_dec(v_val_3386_);
v___x_3408_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3408_;
}
}
}
else
{
lean_object* v___x_3409_; 
lean_dec(v___x_3395_);
lean_dec(v_stx_3388_);
lean_dec(v_val_3386_);
v___x_3409_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3409_;
}
}
else
{
lean_object* v___x_3410_; 
lean_dec(v_val_3392_);
lean_dec(v_stx_3388_);
lean_dec(v_val_3386_);
v___x_3410_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3410_;
}
}
else
{
lean_object* v___x_3411_; 
lean_dec(v___x_3391_);
lean_dec(v_stx_3388_);
lean_dec(v_val_3386_);
v___x_3411_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3411_;
}
}
else
{
lean_object* v___x_3412_; 
lean_dec(v_val_3386_);
v___x_3412_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3412_;
}
}
else
{
lean_object* v___x_3413_; 
lean_dec(v_old_x3f_3377_);
v___x_3413_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3385_, v___f_3384_, v_a_3378_);
return v___x_3413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3414_, lean_object* v_old_x3f_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3414_, v_old_x3f_3415_, v_a_3416_);
lean_dec_ref(v_a_3416_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3419_, lean_object* v_old_x3f_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v___x_3423_; 
lean_inc(v_old_x3f_3420_);
v___x_3423_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3423_, 0, v_setupImports_3419_);
lean_closure_set(v___x_3423_, 1, v_old_x3f_3420_);
if (lean_obj_tag(v_old_x3f_3420_) == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3423_, v___x_3424_, v_a_3421_);
return v___x_3425_;
}
else
{
lean_object* v_val_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3435_; 
v_val_3426_ = lean_ctor_get(v_old_x3f_3420_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_old_x3f_3420_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3428_ = v_old_x3f_3420_;
v_isShared_3429_ = v_isSharedCheck_3435_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_val_3426_);
lean_dec(v_old_x3f_3420_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3435_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_ictx_3430_; lean_object* v___x_3432_; 
v_ictx_3430_ = lean_ctor_get(v_val_3426_, 2);
lean_inc_ref(v_ictx_3430_);
lean_dec(v_val_3426_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v_ictx_3430_);
v___x_3432_ = v___x_3428_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_ictx_3430_);
v___x_3432_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3423_, v___x_3432_, v_a_3421_);
return v___x_3433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3436_, lean_object* v_old_x3f_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Language_Lean_process(v_setupImports_3436_, v_old_x3f_3437_, v_a_3438_);
lean_dec_ref(v_a_3438_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3441_, lean_object* v_parserState_3442_, lean_object* v_commandState_3443_, lean_object* v_old_x3f_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3454_; 
v___x_3446_ = lean_io_promise_new();
v___x_3447_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3444_) == 0)
{
lean_object* v___x_3469_; 
v___x_3469_ = lean_box(0);
v___y_3454_ = v___x_3469_;
goto v___jp_3453_;
}
else
{
lean_object* v_val_3470_; lean_object* v_snd_3471_; lean_object* v___x_3472_; 
v_val_3470_ = lean_ctor_get(v_old_x3f_3444_, 0);
v_snd_3471_ = lean_ctor_get(v_val_3470_, 1);
lean_inc(v_snd_3471_);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v_snd_3471_);
v___y_3454_ = v___x_3472_;
goto v___jp_3453_;
}
v___jp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3449_, v___y_3450_, v_inputCtx_3441_);
lean_dec(v___x_3451_);
v___x_3452_ = l_IO_Promise_result_x21___redArg(v___x_3446_);
lean_dec(v___x_3446_);
return v___x_3452_;
}
v___jp_3453_:
{
uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3455_ = 1;
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_box(v___x_3455_);
lean_inc(v___x_3446_);
v___x_3458_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3458_, 0, v___y_3454_);
lean_closure_set(v___x_3458_, 1, v_parserState_3442_);
lean_closure_set(v___x_3458_, 2, v_commandState_3443_);
lean_closure_set(v___x_3458_, 3, v___x_3446_);
lean_closure_set(v___x_3458_, 4, v___x_3457_);
lean_closure_set(v___x_3458_, 5, v___x_3447_);
lean_closure_set(v___x_3458_, 6, v___x_3456_);
if (lean_obj_tag(v_old_x3f_3444_) == 0)
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_box(0);
v___y_3449_ = v___x_3458_;
v___y_3450_ = v___x_3459_;
goto v___jp_3448_;
}
else
{
lean_object* v_val_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3468_; 
v_val_3460_ = lean_ctor_get(v_old_x3f_3444_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_old_x3f_3444_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3462_ = v_old_x3f_3444_;
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_val_3460_);
lean_dec(v_old_x3f_3444_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3468_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v_fst_3464_; lean_object* v___x_3466_; 
v_fst_3464_ = lean_ctor_get(v_val_3460_, 0);
lean_inc(v_fst_3464_);
lean_dec(v_val_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v_fst_3464_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_fst_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
v___y_3449_ = v___x_3458_;
v___y_3450_ = v___x_3466_;
goto v___jp_3448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3473_, lean_object* v_parserState_3474_, lean_object* v_commandState_3475_, lean_object* v_old_x3f_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3473_, v_parserState_3474_, v_commandState_3475_, v_old_x3f_3476_);
lean_dec_ref(v_inputCtx_3473_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3479_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3480_; 
v_nextCmdSnap_x3f_3480_ = lean_ctor_get(v_snap_3479_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3480_) == 1)
{
lean_object* v_val_3481_; lean_object* v___x_3482_; 
lean_inc_ref(v_nextCmdSnap_x3f_3480_);
lean_dec_ref(v_snap_3479_);
v_val_3481_ = lean_ctor_get(v_nextCmdSnap_x3f_3480_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3480_, 1);
v___x_3482_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3481_);
v_snap_3479_ = v___x_3482_;
goto _start;
}
else
{
lean_object* v_elabSnap_3484_; lean_object* v_resultSnap_3485_; lean_object* v___x_3486_; lean_object* v_cmdState_3487_; lean_object* v___x_3488_; 
v_elabSnap_3484_ = lean_ctor_get(v_snap_3479_, 3);
lean_inc_ref(v_elabSnap_3484_);
lean_dec_ref(v_snap_3479_);
v_resultSnap_3485_ = lean_ctor_get(v_elabSnap_3484_, 2);
lean_inc_ref(v_resultSnap_3485_);
lean_dec_ref(v_elabSnap_3484_);
v___x_3486_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3485_);
v_cmdState_3487_ = lean_ctor_get(v___x_3486_, 1);
lean_inc_ref(v_cmdState_3487_);
lean_dec(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_cmdState_3487_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3489_){
_start:
{
lean_object* v_result_x3f_3490_; 
v_result_x3f_3490_ = lean_ctor_get(v_snap_3489_, 4);
lean_inc(v_result_x3f_3490_);
lean_dec_ref(v_snap_3489_);
if (lean_obj_tag(v_result_x3f_3490_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_box(0);
return v___x_3491_;
}
else
{
lean_object* v_val_3492_; lean_object* v_processedSnap_3493_; lean_object* v___x_3494_; lean_object* v_result_x3f_3495_; 
v_val_3492_ = lean_ctor_get(v_result_x3f_3490_, 0);
lean_inc(v_val_3492_);
lean_dec_ref_known(v_result_x3f_3490_, 1);
v_processedSnap_3493_ = lean_ctor_get(v_val_3492_, 1);
lean_inc_ref(v_processedSnap_3493_);
lean_dec(v_val_3492_);
v___x_3494_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3493_);
v_result_x3f_3495_ = lean_ctor_get(v___x_3494_, 2);
lean_inc(v_result_x3f_3495_);
lean_dec(v___x_3494_);
if (lean_obj_tag(v_result_x3f_3495_) == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_box(0);
return v___x_3496_;
}
else
{
lean_object* v_val_3497_; lean_object* v_firstCmdSnap_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_val_3497_ = lean_ctor_get(v_result_x3f_3495_, 0);
lean_inc(v_val_3497_);
lean_dec_ref_known(v_result_x3f_3495_, 1);
v_firstCmdSnap_3498_ = lean_ctor_get(v_val_3497_, 1);
lean_inc_ref(v_firstCmdSnap_3498_);
lean_dec(v_val_3497_);
v___x_3499_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3498_);
v___x_3500_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3499_);
return v___x_3500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(lean_object* v_f_3501_, lean_object* v_snap_3502_, lean_object* v_acc_3503_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3504_; lean_object* v_acc_3505_; 
v_nextCmdSnap_x3f_3504_ = lean_ctor_get(v_snap_3502_, 4);
lean_inc(v_nextCmdSnap_x3f_3504_);
lean_inc(v_f_3501_);
v_acc_3505_ = lean_apply_2(v_f_3501_, v_acc_3503_, v_snap_3502_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3504_) == 1)
{
lean_object* v_val_3506_; lean_object* v___x_3507_; 
v_val_3506_ = lean_ctor_get(v_nextCmdSnap_x3f_3504_, 0);
lean_inc(v_val_3506_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3504_, 1);
v___x_3507_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3506_);
v_snap_3502_ = v___x_3507_;
v_acc_3503_ = v_acc_3505_;
goto _start;
}
else
{
lean_dec(v_nextCmdSnap_x3f_3504_);
lean_dec(v_f_3501_);
return v_acc_3505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go(lean_object* v_00_u03b1_3509_, lean_object* v_f_3510_, lean_object* v_snap_3511_, lean_object* v_acc_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3510_, v_snap_3511_, v_acc_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object* v_snap_3514_, lean_object* v_init_3515_, lean_object* v_f_3516_){
_start:
{
lean_object* v_result_x3f_3517_; 
v_result_x3f_3517_ = lean_ctor_get(v_snap_3514_, 4);
lean_inc(v_result_x3f_3517_);
lean_dec_ref(v_snap_3514_);
if (lean_obj_tag(v_result_x3f_3517_) == 0)
{
lean_object* v___x_3518_; 
lean_dec(v_f_3516_);
lean_dec(v_init_3515_);
v___x_3518_ = lean_box(0);
return v___x_3518_;
}
else
{
lean_object* v_val_3519_; lean_object* v_processedSnap_3520_; lean_object* v___x_3521_; lean_object* v_result_x3f_3522_; 
v_val_3519_ = lean_ctor_get(v_result_x3f_3517_, 0);
lean_inc(v_val_3519_);
lean_dec_ref_known(v_result_x3f_3517_, 1);
v_processedSnap_3520_ = lean_ctor_get(v_val_3519_, 1);
lean_inc_ref(v_processedSnap_3520_);
lean_dec(v_val_3519_);
v___x_3521_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3520_);
v_result_x3f_3522_ = lean_ctor_get(v___x_3521_, 2);
lean_inc(v_result_x3f_3522_);
lean_dec(v___x_3521_);
if (lean_obj_tag(v_result_x3f_3522_) == 0)
{
lean_object* v___x_3523_; 
lean_dec(v_f_3516_);
lean_dec(v_init_3515_);
v___x_3523_ = lean_box(0);
return v___x_3523_;
}
else
{
lean_object* v_val_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3534_; 
v_val_3524_ = lean_ctor_get(v_result_x3f_3522_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_result_x3f_3522_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3526_ = v_result_x3f_3522_;
v_isShared_3527_ = v_isSharedCheck_3534_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_val_3524_);
lean_dec(v_result_x3f_3522_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3534_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_firstCmdSnap_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v_firstCmdSnap_3528_ = lean_ctor_get(v_val_3524_, 1);
lean_inc_ref(v_firstCmdSnap_3528_);
lean_dec(v_val_3524_);
v___x_3529_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3528_);
v___x_3530_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_foldCmdSnaps_x3f_go___redArg(v_f_3516_, v___x_3529_, v_init_3515_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3530_);
v___x_3532_ = v___x_3526_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f(lean_object* v_00_u03b1_3535_, lean_object* v_snap_3536_, lean_object* v_init_3537_, lean_object* v_f_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v_snap_3536_, v_init_3537_, v_f_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = 1;
v___x_3546_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3547_ = l_Lean_Name_toString(v___x_3546_, v___x_3545_);
return v___x_3547_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3548_ = 0;
v___x_3549_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3550_ = lean_box(0);
v___x_3551_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3552_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3553_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
lean_ctor_set(v___x_3553_, 1, v___x_3551_);
lean_ctor_set(v___x_3553_, 2, v___x_3550_);
lean_ctor_set(v___x_3553_, 3, v___x_3549_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*4, v___x_3548_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3555_ = lean_box(0);
v___x_3556_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3557_){
_start:
{
lean_object* v_result_x3f_3558_; 
v_result_x3f_3558_ = lean_ctor_get(v_snap_3557_, 4);
lean_inc(v_result_x3f_3558_);
if (lean_obj_tag(v_result_x3f_3558_) == 1)
{
lean_object* v_val_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3634_; 
v_val_3559_ = lean_ctor_get(v_result_x3f_3558_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_result_x3f_3558_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3561_ = v_result_x3f_3558_;
v_isShared_3562_ = v_isSharedCheck_3634_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_val_3559_);
lean_dec(v_result_x3f_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3634_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_toSnapshot_3563_; lean_object* v_metaSnap_3564_; lean_object* v_ictx_3565_; lean_object* v_stx_3566_; lean_object* v_parserState_3567_; lean_object* v_processedSnap_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3633_; 
v_toSnapshot_3563_ = lean_ctor_get(v_snap_3557_, 0);
v_metaSnap_3564_ = lean_ctor_get(v_snap_3557_, 1);
v_ictx_3565_ = lean_ctor_get(v_snap_3557_, 2);
v_stx_3566_ = lean_ctor_get(v_snap_3557_, 3);
v_parserState_3567_ = lean_ctor_get(v_val_3559_, 0);
v_processedSnap_3568_ = lean_ctor_get(v_val_3559_, 1);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_val_3559_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3570_ = v_val_3559_;
v_isShared_3571_ = v_isSharedCheck_3633_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_processedSnap_3568_);
lean_inc(v_parserState_3567_);
lean_dec(v_val_3559_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3633_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_processed_3572_; lean_object* v_result_x3f_3573_; 
v_processed_3572_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3568_);
v_result_x3f_3573_ = lean_ctor_get(v_processed_3572_, 2);
lean_inc(v_result_x3f_3573_);
if (lean_obj_tag(v_result_x3f_3573_) == 1)
{
lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3627_; 
lean_inc(v_stx_3566_);
lean_inc_ref(v_ictx_3565_);
lean_inc_ref(v_metaSnap_3564_);
lean_inc_ref(v_toSnapshot_3563_);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_snap_3557_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; lean_object* v_unused_3631_; lean_object* v_unused_3632_; 
v_unused_3628_ = lean_ctor_get(v_snap_3557_, 4);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_snap_3557_, 3);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_snap_3557_, 2);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_snap_3557_, 1);
lean_dec(v_unused_3631_);
v_unused_3632_ = lean_ctor_get(v_snap_3557_, 0);
lean_dec(v_unused_3632_);
v___x_3575_ = v_snap_3557_;
v_isShared_3576_ = v_isSharedCheck_3627_;
goto v_resetjp_3574_;
}
else
{
lean_dec(v_snap_3557_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3627_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v_val_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3626_; 
v_val_3577_ = lean_ctor_get(v_result_x3f_3573_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_result_x3f_3573_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3579_ = v_result_x3f_3573_;
v_isShared_3580_ = v_isSharedCheck_3626_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_val_3577_);
lean_dec(v_result_x3f_3573_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3626_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_toSnapshot_3581_; lean_object* v_metaSnap_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3624_; 
v_toSnapshot_3581_ = lean_ctor_get(v_processed_3572_, 0);
v_metaSnap_3582_ = lean_ctor_get(v_processed_3572_, 1);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_processed_3572_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v_processed_3572_, 2);
lean_dec(v_unused_3625_);
v___x_3584_ = v_processed_3572_;
v_isShared_3585_ = v_isSharedCheck_3624_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_metaSnap_3582_);
lean_inc(v_toSnapshot_3581_);
lean_dec(v_processed_3572_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3624_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_cmdState_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3622_; 
v_cmdState_3586_ = lean_ctor_get(v_val_3577_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_val_3577_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_val_3577_, 1);
lean_dec(v_unused_3623_);
v___x_3588_ = v_val_3577_;
v_isShared_3589_ = v_isSharedCheck_3622_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_cmdState_3586_);
lean_dec(v_val_3577_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3622_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_resultSnap_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_elabSnap_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_termCmd_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3590_ = lean_box(0);
v___x_3591_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3592_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
lean_inc_ref(v_cmdState_3586_);
v_resultSnap_3593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_resultSnap_3593_, 0, v___x_3591_);
lean_ctor_set(v_resultSnap_3593_, 1, v_cmdState_3586_);
lean_ctor_set(v_resultSnap_3593_, 2, v___x_3592_);
v___x_3594_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3595_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3590_, v_resultSnap_3593_);
v___x_3596_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3597_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5);
v_elabSnap_3598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3598_, 0, v___x_3591_);
lean_ctor_set(v_elabSnap_3598_, 1, v___x_3594_);
lean_ctor_set(v_elabSnap_3598_, 2, v___x_3595_);
lean_ctor_set(v_elabSnap_3598_, 3, v___x_3596_);
lean_ctor_set(v_elabSnap_3598_, 4, v___x_3597_);
v___x_3599_ = lean_box(0);
v___x_3600_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3601_, 0, v___x_3591_);
lean_ctor_set(v_termCmd_3601_, 1, v___x_3599_);
lean_ctor_set(v_termCmd_3601_, 2, v___x_3600_);
lean_ctor_set(v_termCmd_3601_, 3, v_elabSnap_3598_);
lean_ctor_set(v_termCmd_3601_, 4, v___x_3590_);
v___x_3602_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3590_, v_termCmd_3601_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v___x_3602_);
v___x_3604_ = v___x_3588_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_cmdState_3586_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3604_);
v___x_3606_ = v___x_3579_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v_newProcessed_3608_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 2, v___x_3606_);
v_newProcessed_3608_ = v___x_3584_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_toSnapshot_3581_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_metaSnap_3582_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v___x_3606_);
v_newProcessed_3608_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3590_, v_newProcessed_3608_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___x_3609_);
v___x_3611_ = v___x_3570_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_parserState_3567_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3611_);
v___x_3613_ = v___x_3561_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 4, v___x_3613_);
v___x_3615_ = v___x_3575_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_toSnapshot_3563_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_metaSnap_3564_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v_ictx_3565_);
lean_ctor_set(v_reuseFailAlloc_3616_, 3, v_stx_3566_);
lean_ctor_set(v_reuseFailAlloc_3616_, 4, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
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
lean_dec(v_result_x3f_3573_);
lean_dec(v_processed_3572_);
lean_del_object(v___x_3570_);
lean_dec_ref(v_parserState_3567_);
lean_del_object(v___x_3561_);
return v_snap_3557_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3558_);
return v_snap_3557_;
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

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
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_IO_CancelToken_new();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
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
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
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
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parsing"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_594_, lean_object* v_cmds_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_597_);
lean_dec_ref(v___x_599_);
v___x_600_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_594_, v_cmds_595_, v___y_596_, v___y_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_601_, lean_object* v_cmds_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_601_, v_cmds_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_606_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_ctor_set(v___x_612_, 2, v___x_611_);
lean_ctor_set(v___x_612_, 3, v___x_611_);
lean_ctor_set(v___x_612_, 4, v___x_610_);
lean_ctor_set(v___x_612_, 5, v___x_610_);
lean_ctor_set(v___x_612_, 6, v___x_610_);
lean_ctor_set(v___x_612_, 7, v___x_610_);
lean_ctor_set(v___x_612_, 8, v___x_610_);
lean_ctor_set(v___x_612_, 9, v___x_610_);
lean_ctor_set(v___x_612_, 10, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(32u);
v___x_614_ = lean_mk_empty_array_with_capacity(v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_616_ = ((size_t)5ULL);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_unsigned_to_nat(32u);
v___x_619_ = lean_mk_empty_array_with_capacity(v___x_618_);
v___x_620_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_621_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_617_);
lean_ctor_set(v___x_621_, 3, v___x_617_);
lean_ctor_set_usize(v___x_621_, 4, v___x_616_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_box(1);
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; lean_object* v_env_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_scopes_633_; lean_object* v___x_634_; lean_object* v_opts_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_629_ = lean_st_ref_get(v___y_627_);
v_env_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc_ref(v_env_630_);
lean_dec(v___x_629_);
v___x_631_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_632_ = lean_st_ref_get(v___y_627_);
v_scopes_633_ = lean_ctor_get(v___x_632_, 2);
lean_inc(v_scopes_633_);
lean_dec(v___x_632_);
v___x_634_ = l_List_head_x21___redArg(v___x_631_, v_scopes_633_);
lean_dec(v_scopes_633_);
v_opts_635_ = lean_ctor_get(v___x_634_, 1);
lean_inc_ref(v_opts_635_);
lean_dec(v___x_634_);
v___x_636_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_638_, 0, v_env_630_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
lean_ctor_set(v___x_638_, 3, v_opts_635_);
v___x_639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_msgData_626_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_641_, v___y_642_);
lean_dec(v___y_642_);
return v_res_644_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_645_, uint8_t v___y_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_647_) == 1)
{
lean_object* v_pre_648_; 
v_pre_648_ = lean_ctor_get(v_x_647_, 0);
if (lean_obj_tag(v_pre_648_) == 0)
{
lean_object* v_str_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_str_649_ = lean_ctor_get(v_x_647_, 1);
v___x_650_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_651_ = lean_string_dec_eq(v_str_649_, v___x_650_);
if (v___x_651_ == 0)
{
return v___x_651_;
}
else
{
return v_suppressElabErrors_645_;
}
}
else
{
return v___y_646_;
}
}
else
{
return v___y_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_652_, lean_object* v___y_653_, lean_object* v_x_654_){
_start:
{
uint8_t v_suppressElabErrors_boxed_655_; uint8_t v___y_9152__boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_suppressElabErrors_boxed_655_ = lean_unbox(v_suppressElabErrors_652_);
v___y_9152__boxed_656_ = lean_unbox(v___y_653_);
v_res_657_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_655_, v___y_9152__boxed_656_, v_x_654_);
lean_dec(v_x_654_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_660_, lean_object* v_msgData_661_, uint8_t v_severity_662_, uint8_t v_isSilent_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; uint8_t v___y_733_; lean_object* v___y_734_; uint8_t v___y_735_; uint8_t v___y_736_; lean_object* v___y_737_; uint8_t v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; uint8_t v___y_764_; lean_object* v___y_765_; uint8_t v___y_769_; uint8_t v___y_770_; uint8_t v___y_771_; uint8_t v___x_786_; uint8_t v___y_788_; uint8_t v___y_789_; uint8_t v___y_790_; uint8_t v___y_792_; uint8_t v___x_804_; 
v___x_786_ = 2;
v___x_804_ = l_Lean_instBEqMessageSeverity_beq(v_severity_662_, v___x_786_);
if (v___x_804_ == 0)
{
v___y_792_ = v___x_804_;
goto v___jp_791_;
}
else
{
uint8_t v___x_805_; 
lean_inc_ref(v_msgData_661_);
v___x_805_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_661_);
v___y_792_ = v___x_805_;
goto v___jp_791_;
}
v___jp_667_:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Elab_Command_getScope___redArg(v___y_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v_currNamespace_678_; lean_object* v___x_679_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v_currNamespace_678_ = lean_ctor_get(v_a_677_, 2);
lean_inc(v_currNamespace_678_);
lean_dec(v_a_677_);
v___x_679_ = l_Lean_Elab_Command_getScope___redArg(v___y_675_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_715_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_715_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_715_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_715_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_openDecls_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v_messages_690_; lean_object* v_scopes_691_; lean_object* v_usedQuotCtxts_692_; lean_object* v_nextMacroScope_693_; lean_object* v_maxRecDepth_694_; lean_object* v_ngen_695_; lean_object* v_auxDeclNGen_696_; lean_object* v_infoState_697_; lean_object* v_traceState_698_; lean_object* v_snapshotTasks_699_; lean_object* v_prevLinterStates_700_; lean_object* v_codeQualityEntryTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_714_; 
v_openDecls_684_ = lean_ctor_get(v_a_680_, 3);
lean_inc(v_openDecls_684_);
lean_dec(v_a_680_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_currNamespace_678_);
lean_ctor_set(v___x_685_, 1, v_openDecls_684_);
v___x_686_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___y_668_);
lean_inc_ref(v___y_673_);
lean_inc_ref(v___y_669_);
v___x_687_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_687_, 0, v___y_669_);
lean_ctor_set(v___x_687_, 1, v___y_672_);
lean_ctor_set(v___x_687_, 2, v___y_671_);
lean_ctor_set(v___x_687_, 3, v___y_673_);
lean_ctor_set(v___x_687_, 4, v___x_686_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*5, v___y_674_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*5 + 1, v___y_670_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*5 + 2, v_isSilent_663_);
v___x_688_ = lean_st_ref_take(v___y_675_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
v_messages_690_ = lean_ctor_get(v___x_688_, 1);
v_scopes_691_ = lean_ctor_get(v___x_688_, 2);
v_usedQuotCtxts_692_ = lean_ctor_get(v___x_688_, 3);
v_nextMacroScope_693_ = lean_ctor_get(v___x_688_, 4);
v_maxRecDepth_694_ = lean_ctor_get(v___x_688_, 5);
v_ngen_695_ = lean_ctor_get(v___x_688_, 6);
v_auxDeclNGen_696_ = lean_ctor_get(v___x_688_, 7);
v_infoState_697_ = lean_ctor_get(v___x_688_, 8);
v_traceState_698_ = lean_ctor_get(v___x_688_, 9);
v_snapshotTasks_699_ = lean_ctor_get(v___x_688_, 10);
v_prevLinterStates_700_ = lean_ctor_get(v___x_688_, 11);
v_codeQualityEntryTasks_701_ = lean_ctor_get(v___x_688_, 12);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_714_ == 0)
{
v___x_703_ = v___x_688_;
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_codeQualityEntryTasks_701_);
lean_inc(v_prevLinterStates_700_);
lean_inc(v_snapshotTasks_699_);
lean_inc(v_traceState_698_);
lean_inc(v_infoState_697_);
lean_inc(v_auxDeclNGen_696_);
lean_inc(v_ngen_695_);
lean_inc(v_maxRecDepth_694_);
lean_inc(v_nextMacroScope_693_);
lean_inc(v_usedQuotCtxts_692_);
lean_inc(v_scopes_691_);
lean_inc(v_messages_690_);
lean_inc(v_env_689_);
lean_dec(v___x_688_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_MessageLog_add(v___x_687_, v_messages_690_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_env_689_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_scopes_691_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_usedQuotCtxts_692_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_nextMacroScope_693_);
lean_ctor_set(v_reuseFailAlloc_713_, 5, v_maxRecDepth_694_);
lean_ctor_set(v_reuseFailAlloc_713_, 6, v_ngen_695_);
lean_ctor_set(v_reuseFailAlloc_713_, 7, v_auxDeclNGen_696_);
lean_ctor_set(v_reuseFailAlloc_713_, 8, v_infoState_697_);
lean_ctor_set(v_reuseFailAlloc_713_, 9, v_traceState_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 10, v_snapshotTasks_699_);
lean_ctor_set(v_reuseFailAlloc_713_, 11, v_prevLinterStates_700_);
lean_ctor_set(v_reuseFailAlloc_713_, 12, v_codeQualityEntryTasks_701_);
v___x_708_ = v_reuseFailAlloc_713_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_st_ref_put(v___y_675_, v___x_708_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_705_);
v___x_711_ = v___x_682_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_705_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_currNamespace_678_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_668_);
v_a_716_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_679_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_679_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_668_);
v_a_724_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_676_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_676_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
v___jp_732_:
{
lean_object* v_fileName_738_; lean_object* v_fileMap_739_; uint8_t v_suppressElabErrors_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_759_; 
v_fileName_738_ = lean_ctor_get(v___y_664_, 0);
v_fileMap_739_ = lean_ctor_get(v___y_664_, 1);
v_suppressElabErrors_740_ = lean_ctor_get_uint8(v___y_664_, sizeof(void*)*10);
v___x_741_ = lean_box(v_suppressElabErrors_740_);
v___x_742_ = lean_box(v___y_733_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_743_, 0, v___x_741_);
lean_closure_set(v___f_743_, 1, v___x_742_);
v___x_744_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_661_);
v___x_745_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_744_, v___y_665_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_759_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_759_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_759_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_inc_ref_n(v_fileMap_739_, 2);
v___x_750_ = l_Lean_FileMap_toPosition(v_fileMap_739_, v___y_734_);
lean_dec(v___y_734_);
v___x_751_ = l_Lean_FileMap_toPosition(v_fileMap_739_, v___y_737_);
lean_dec(v___y_737_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_740_ == 0)
{
lean_del_object(v___x_748_);
lean_dec_ref(v___f_743_);
v___y_668_ = v_a_746_;
v___y_669_ = v_fileName_738_;
v___y_670_ = v___y_735_;
v___y_671_ = v___x_752_;
v___y_672_ = v___x_750_;
v___y_673_ = v___x_753_;
v___y_674_ = v___y_736_;
v___y_675_ = v___y_665_;
goto v___jp_667_;
}
else
{
uint8_t v___x_754_; 
lean_inc(v_a_746_);
v___x_754_ = l_Lean_MessageData_hasTag(v___f_743_, v_a_746_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec_ref_known(v___x_752_, 1);
lean_dec_ref(v___x_750_);
lean_dec(v_a_746_);
v___x_755_ = lean_box(0);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_755_);
v___x_757_ = v___x_748_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_del_object(v___x_748_);
v___y_668_ = v_a_746_;
v___y_669_ = v_fileName_738_;
v___y_670_ = v___y_735_;
v___y_671_ = v___x_752_;
v___y_672_ = v___x_750_;
v___y_673_ = v___x_753_;
v___y_674_ = v___y_736_;
v___y_675_ = v___y_665_;
goto v___jp_667_;
}
}
}
}
v___jp_760_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Syntax_getTailPos_x3f(v___y_763_, v___y_764_);
lean_dec(v___y_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_inc(v___y_765_);
v___y_733_ = v___y_761_;
v___y_734_ = v___y_765_;
v___y_735_ = v___y_762_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_765_;
goto v___jp_732_;
}
else
{
lean_object* v_val_767_; 
v_val_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v___x_766_, 1);
v___y_733_ = v___y_761_;
v___y_734_ = v___y_765_;
v___y_735_ = v___y_762_;
v___y_736_ = v___y_764_;
v___y_737_ = v_val_767_;
goto v___jp_732_;
}
}
v___jp_768_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Elab_Command_getRef___redArg(v___y_664_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_ref_774_; lean_object* v___x_775_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
v_ref_774_ = l_Lean_replaceRef(v_ref_660_, v_a_773_);
lean_dec(v_a_773_);
v___x_775_ = l_Lean_Syntax_getPos_x3f(v_ref_774_, v___y_770_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___y_761_ = v___y_769_;
v___y_762_ = v___y_771_;
v___y_763_ = v_ref_774_;
v___y_764_ = v___y_770_;
v___y_765_ = v___x_776_;
goto v___jp_760_;
}
else
{
lean_object* v_val_777_; 
v_val_777_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v___x_775_, 1);
v___y_761_ = v___y_769_;
v___y_762_ = v___y_771_;
v___y_763_ = v_ref_774_;
v___y_764_ = v___y_770_;
v___y_765_ = v_val_777_;
goto v___jp_760_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_msgData_661_);
v_a_778_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_772_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_772_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
v___jp_787_:
{
if (v___y_790_ == 0)
{
v___y_769_ = v___y_788_;
v___y_770_ = v___y_789_;
v___y_771_ = v_severity_662_;
goto v___jp_768_;
}
else
{
v___y_769_ = v___y_788_;
v___y_770_ = v___y_789_;
v___y_771_ = v___x_786_;
goto v___jp_768_;
}
}
v___jp_791_:
{
if (v___y_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_scopes_795_; lean_object* v___x_796_; lean_object* v_opts_797_; uint8_t v___x_798_; uint8_t v___x_799_; 
v___x_793_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_794_ = lean_st_ref_get(v___y_665_);
v_scopes_795_ = lean_ctor_get(v___x_794_, 2);
lean_inc(v_scopes_795_);
lean_dec(v___x_794_);
v___x_796_ = l_List_head_x21___redArg(v___x_793_, v_scopes_795_);
lean_dec(v_scopes_795_);
v_opts_797_ = lean_ctor_get(v___x_796_, 1);
lean_inc_ref(v_opts_797_);
lean_dec(v___x_796_);
v___x_798_ = 1;
v___x_799_ = l_Lean_instBEqMessageSeverity_beq(v_severity_662_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_opts_797_);
v___y_788_ = v___y_792_;
v___y_789_ = v___y_792_;
v___y_790_ = v___x_799_;
goto v___jp_787_;
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = l_Lean_warningAsError;
v___x_801_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_797_, v___x_800_);
lean_dec_ref(v_opts_797_);
v___y_788_ = v___y_792_;
v___y_789_ = v___y_792_;
v___y_790_ = v___x_801_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v_msgData_661_);
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_806_, lean_object* v_msgData_807_, lean_object* v_severity_808_, lean_object* v_isSilent_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_severity_boxed_813_; uint8_t v_isSilent_boxed_814_; lean_object* v_res_815_; 
v_severity_boxed_813_ = lean_unbox(v_severity_808_);
v_isSilent_boxed_814_ = lean_unbox(v_isSilent_809_);
v_res_815_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_806_, v_msgData_807_, v_severity_boxed_813_, v_isSilent_boxed_814_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v_ref_806_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_816_, uint8_t v_severity_817_, uint8_t v_isSilent_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_Command_getRef___redArg(v___y_819_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_823_, v_msgData_816_, v_severity_817_, v_isSilent_818_, v___y_819_, v___y_820_);
lean_dec(v_a_823_);
return v___x_824_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_msgData_816_);
v_a_825_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_822_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_822_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_833_, lean_object* v_severity_834_, lean_object* v_isSilent_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v_severity_boxed_839_; uint8_t v_isSilent_boxed_840_; lean_object* v_res_841_; 
v_severity_boxed_839_ = lean_unbox(v_severity_834_);
v_isSilent_boxed_840_ = lean_unbox(v_isSilent_835_);
v_res_841_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_833_, v_severity_boxed_839_, v_isSilent_boxed_840_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = 2;
v___x_847_ = 0;
v___x_848_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_842_, v___x_846_, v___x_847_, v___y_843_, v___y_844_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_854_, lean_object* v_msgData_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 2;
v___x_860_ = 0;
v___x_861_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_854_, v_msgData_855_, v___x_859_, v___x_860_, v___y_856_, v___y_857_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_862_, lean_object* v_msgData_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_862_, v_msgData_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v_ref_862_);
return v_res_867_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
if (lean_obj_tag(v_ex_871_) == 0)
{
lean_object* v_ref_875_; lean_object* v_msg_876_; lean_object* v___x_877_; 
v_ref_875_ = lean_ctor_get(v_ex_871_, 0);
lean_inc(v_ref_875_);
v_msg_876_ = lean_ctor_get(v_ex_871_, 1);
lean_inc_ref(v_msg_876_);
lean_dec_ref_known(v_ex_871_, 2);
v___x_877_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_875_, v_msg_876_, v___y_872_, v___y_873_);
lean_dec(v_ref_875_);
return v___x_877_;
}
else
{
lean_object* v_id_878_; uint8_t v___y_880_; uint8_t v___x_902_; 
v_id_878_ = lean_ctor_get(v_ex_871_, 0);
lean_inc(v_id_878_);
v___x_902_ = l_Lean_Elab_isAbortExceptionId(v_id_878_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Exception_isInterrupt(v_ex_871_);
lean_dec_ref_known(v_ex_871_, 2);
v___y_880_ = v___x_903_;
goto v___jp_879_;
}
else
{
lean_dec_ref_known(v_ex_871_, 2);
v___y_880_ = v___x_902_;
goto v___jp_879_;
}
v___jp_879_:
{
if (v___y_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_InternalExceptionId_getName(v_id_878_);
lean_dec(v_id_878_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_884_ = l_Lean_MessageData_ofName(v_a_882_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_885_, v___y_872_, v___y_873_);
return v___x_886_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_899_; 
v_a_887_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_899_ == 0)
{
v___x_889_ = v___x_881_;
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_881_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_899_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v_ref_891_ = lean_ctor_get(v___y_872_, 7);
v___x_892_ = lean_io_error_to_string(v_a_887_);
v___x_893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = l_Lean_MessageData_ofFormat(v___x_893_);
lean_inc(v_ref_891_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_ref_891_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_895_);
v___x_897_ = v___x_889_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_id_878_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
v___x_913_ = lean_apply_3(v_x_909_, v___y_910_, v___y_911_, lean_box(0));
if (lean_obj_tag(v___x_913_) == 0)
{
return v___x_913_;
}
else
{
lean_object* v_a_914_; uint8_t v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
v___x_915_ = l_Lean_Exception_isInterrupt(v_a_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_916_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_914_, v___y_910_, v___y_911_);
return v___x_916_;
}
else
{
lean_dec(v_a_914_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_922_, lean_object* v___x_923_, lean_object* v_val_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_a_928_; lean_object* v___x_930_; 
v___x_930_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_922_, v___x_923_, v_val_924_);
if (lean_obj_tag(v___x_930_) == 0)
{
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v_a_928_ = v_a_931_;
goto v___jp_927_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_932_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_930_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_930_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v___x_940_; 
lean_dec_ref_known(v___x_930_, 1);
v___x_940_ = lean_box(0);
v_a_928_ = v___x_940_;
goto v___jp_927_;
}
v___jp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_a_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_941_, lean_object* v___x_942_, lean_object* v_val_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_941_, v___x_942_, v_val_943_, v___y_944_);
lean_dec_ref(v___y_944_);
lean_dec(v_val_943_);
lean_dec_ref(v___x_942_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_947_, lean_object* v_x_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_get_set_stderr(v_h_947_);
lean_inc_ref(v___y_949_);
v___x_952_ = lean_apply_2(v_x_948_, v___y_949_, lean_box(0));
v___x_953_ = lean_get_set_stderr(v___x_951_);
lean_dec_ref(v___x_953_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_954_, lean_object* v_x_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_954_, v_x_955_, v___y_956_);
lean_dec_ref(v___y_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_959_, lean_object* v_h_960_, lean_object* v_x_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_960_, v_x_961_, v___y_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_965_, lean_object* v_h_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_965_, v_h_966_, v_x_967_, v___y_968_);
lean_dec_ref(v___y_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_971_, lean_object* v_x_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_get_set_stdin(v_h_971_);
lean_inc_ref(v___y_973_);
v___x_976_ = lean_apply_2(v_x_972_, v___y_973_, lean_box(0));
v___x_977_ = lean_get_set_stdin(v___x_975_);
lean_dec_ref(v___x_977_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_978_, lean_object* v_x_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_978_, v_x_979_, v___y_980_);
lean_dec_ref(v___y_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_985_ = lean_panic_fn_borrowed(v___x_984_, v_msg_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_986_, lean_object* v_x_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_get_set_stdout(v_h_986_);
lean_inc_ref(v___y_988_);
v___x_991_ = lean_apply_2(v_x_987_, v___y_988_, lean_box(0));
v___x_992_ = lean_get_set_stdout(v___x_990_);
lean_dec_ref(v___x_992_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_993_, v_x_994_, v___y_995_);
lean_dec_ref(v___y_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_998_, lean_object* v_h_999_, lean_object* v_x_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_999_, v_x_1000_, v___y_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_h_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_1004_, v_h_1005_, v_x_1006_, v___y_1007_);
lean_dec_ref(v___y_1007_);
return v_res_1009_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = l_ByteArray_empty;
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1016_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1017_ = lean_unsigned_to_nat(46u);
v___x_1018_ = lean_unsigned_to_nat(193u);
v___x_1019_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1020_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1021_ = l_mkPanicMessageWithDecl(v___x_1020_, v___x_1019_, v___x_1018_, v___x_1017_, v___x_1016_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1022_, uint8_t v_isolateStderr_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___y_1036_; 
v___x_1030_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1031_ = lean_st_mk_ref(v___x_1030_);
v___x_1032_ = lean_st_mk_ref(v___x_1030_);
v___x_1033_ = l_IO_FS_Stream_ofBuffer(v___x_1031_);
lean_inc(v___x_1032_);
v___x_1034_ = l_IO_FS_Stream_ofBuffer(v___x_1032_);
if (v_isolateStderr_1023_ == 0)
{
v___y_1036_ = v_x_1022_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1045_; 
lean_inc_ref(v___x_1034_);
v___x_1045_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1045_, 0, lean_box(0));
lean_closure_set(v___x_1045_, 1, v___x_1034_);
lean_closure_set(v___x_1045_, 2, v_x_1022_);
v___y_1036_ = v___x_1045_;
goto v___jp_1035_;
}
v___jp_1026_:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___y_1028_);
lean_ctor_set(v___x_1029_, 1, v___y_1027_);
return v___x_1029_;
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_data_1040_; uint8_t v___x_1041_; 
v___x_1037_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1037_, 0, lean_box(0));
lean_closure_set(v___x_1037_, 1, v___x_1034_);
lean_closure_set(v___x_1037_, 2, v___y_1036_);
v___x_1038_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1033_, v___x_1037_, v___y_1024_);
v___x_1039_ = lean_st_ref_get(v___x_1032_);
lean_dec(v___x_1032_);
v_data_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc_ref(v_data_1040_);
lean_dec(v___x_1039_);
v___x_1041_ = lean_string_validate_utf8(v_data_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_data_1040_);
v___x_1042_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1043_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1042_);
v___y_1027_ = v___x_1038_;
v___y_1028_ = v___x_1043_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_string_from_utf8_unchecked(v_data_1040_);
v___y_1027_ = v___x_1038_;
v___y_1028_ = v___x_1044_;
goto v___jp_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1046_, lean_object* v_isolateStderr_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
uint8_t v_isolateStderr_boxed_1050_; lean_object* v_res_1051_; 
v_isolateStderr_boxed_1050_ = lean_unbox(v_isolateStderr_1047_);
v_res_1051_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1046_, v_isolateStderr_boxed_1050_, v___y_1048_);
lean_dec_ref(v___y_1048_);
return v_res_1051_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = 1;
v___x_1061_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1062_ = l_Lean_Name_toString(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1063_, lean_object* v_cmds_1064_, lean_object* v_cmdState_1065_, lean_object* v_beginPos_1066_, lean_object* v_snap_1067_, lean_object* v_cancelTk_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_env_1071_; lean_object* v_scopes_1072_; lean_object* v_usedQuotCtxts_1073_; lean_object* v_nextMacroScope_1074_; lean_object* v_maxRecDepth_1075_; lean_object* v_ngen_1076_; lean_object* v_auxDeclNGen_1077_; lean_object* v_infoState_1078_; lean_object* v_prevLinterStates_1079_; lean_object* v_codeQualityEntryTasks_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1162_; 
v_env_1071_ = lean_ctor_get(v_cmdState_1065_, 0);
v_scopes_1072_ = lean_ctor_get(v_cmdState_1065_, 2);
v_usedQuotCtxts_1073_ = lean_ctor_get(v_cmdState_1065_, 3);
v_nextMacroScope_1074_ = lean_ctor_get(v_cmdState_1065_, 4);
v_maxRecDepth_1075_ = lean_ctor_get(v_cmdState_1065_, 5);
v_ngen_1076_ = lean_ctor_get(v_cmdState_1065_, 6);
v_auxDeclNGen_1077_ = lean_ctor_get(v_cmdState_1065_, 7);
v_infoState_1078_ = lean_ctor_get(v_cmdState_1065_, 8);
v_prevLinterStates_1079_ = lean_ctor_get(v_cmdState_1065_, 11);
v_codeQualityEntryTasks_1080_ = lean_ctor_get(v_cmdState_1065_, 12);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_cmdState_1065_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1163_ = lean_ctor_get(v_cmdState_1065_, 10);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_cmdState_1065_, 9);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_cmdState_1065_, 1);
lean_dec(v_unused_1165_);
v___x_1082_ = v_cmdState_1065_;
v_isShared_1083_ = v_isSharedCheck_1162_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1080_);
lean_inc(v_prevLinterStates_1079_);
lean_inc(v_infoState_1078_);
lean_inc(v_auxDeclNGen_1077_);
lean_inc(v_ngen_1076_);
lean_inc(v_maxRecDepth_1075_);
lean_inc(v_nextMacroScope_1074_);
lean_inc(v_usedQuotCtxts_1073_);
lean_inc(v_scopes_1072_);
lean_inc(v_env_1071_);
lean_dec(v_cmdState_1065_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1162_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___f_1084_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1084_, 0, v_stx_1063_);
lean_closure_set(v___f_1084_, 1, v_cmds_1064_);
v___x_1085_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1086_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1087_ = l_List_head_x21___redArg(v___x_1085_, v_scopes_1072_);
v___x_1088_ = l_Lean_MessageLog_empty;
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1091_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 10, v___x_1091_);
lean_ctor_set(v___x_1082_, 9, v___x_1090_);
lean_ctor_set(v___x_1082_, 1, v___x_1088_);
v___x_1093_ = v___x_1082_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_env_1071_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_scopes_1072_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_usedQuotCtxts_1073_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_nextMacroScope_1074_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_maxRecDepth_1075_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_ngen_1076_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v_auxDeclNGen_1077_);
lean_ctor_set(v_reuseFailAlloc_1161_, 8, v_infoState_1078_);
lean_ctor_set(v_reuseFailAlloc_1161_, 9, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1161_, 10, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1161_, 11, v_prevLinterStates_1079_);
lean_ctor_set(v_reuseFailAlloc_1161_, 12, v_codeQualityEntryTasks_1080_);
v___x_1093_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v_toProcessingContext_1095_; lean_object* v_fileName_1096_; lean_object* v_fileMap_1097_; lean_object* v_opts_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; uint8_t v___y_1106_; lean_object* v_env_1107_; lean_object* v_scopes_1108_; lean_object* v_usedQuotCtxts_1109_; lean_object* v_nextMacroScope_1110_; lean_object* v_maxRecDepth_1111_; lean_object* v_ngen_1112_; lean_object* v_auxDeclNGen_1113_; lean_object* v_infoState_1114_; lean_object* v_traceState_1115_; lean_object* v_snapshotTasks_1116_; lean_object* v_prevLinterStates_1117_; lean_object* v_codeQualityEntryTasks_1118_; lean_object* v_messages_1119_; lean_object* v___y_1128_; 
v___x_1094_ = lean_st_mk_ref(v___x_1093_);
v_toProcessingContext_1095_ = lean_ctor_get(v_a_1069_, 0);
v_fileName_1096_ = lean_ctor_get(v_toProcessingContext_1095_, 1);
v_fileMap_1097_ = lean_ctor_get(v_toProcessingContext_1095_, 2);
v_opts_1098_ = lean_ctor_get(v___x_1087_, 1);
lean_inc_ref(v_opts_1098_);
lean_dec(v___x_1087_);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_firstFrontendMacroScope;
v___x_1102_ = lean_box(0);
v___x_1103_ = l_Lean_internal_cmdlineSnapshots;
v___x_1104_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1098_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1160_; 
lean_inc_ref(v_snap_1067_);
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_snap_1067_);
v___y_1128_ = v___x_1160_;
goto v___jp_1127_;
}
else
{
v___y_1128_ = v___x_1100_;
goto v___jp_1127_;
}
v___jp_1105_:
{
lean_object* v_new_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_new_1120_ = lean_ctor_get(v_snap_1067_, 1);
lean_inc(v_new_1120_);
lean_dec_ref(v_snap_1067_);
v___x_1121_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_1121_, 0, v_env_1107_);
lean_ctor_set(v___x_1121_, 1, v_messages_1119_);
lean_ctor_set(v___x_1121_, 2, v_scopes_1108_);
lean_ctor_set(v___x_1121_, 3, v_usedQuotCtxts_1109_);
lean_ctor_set(v___x_1121_, 4, v_nextMacroScope_1110_);
lean_ctor_set(v___x_1121_, 5, v_maxRecDepth_1111_);
lean_ctor_set(v___x_1121_, 6, v_ngen_1112_);
lean_ctor_set(v___x_1121_, 7, v_auxDeclNGen_1113_);
lean_ctor_set(v___x_1121_, 8, v_infoState_1114_);
lean_ctor_set(v___x_1121_, 9, v_traceState_1115_);
lean_ctor_set(v___x_1121_, 10, v_snapshotTasks_1116_);
lean_ctor_set(v___x_1121_, 11, v_prevLinterStates_1117_);
lean_ctor_set(v___x_1121_, 12, v_codeQualityEntryTasks_1118_);
v___x_1122_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1123_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1124_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_ctor_set(v___x_1124_, 2, v___x_1100_);
lean_ctor_set(v___x_1124_, 3, v___x_1090_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*4, v___y_1106_);
v___x_1125_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1086_, v___x_1124_);
v___x_1126_ = lean_io_promise_resolve(v___x_1125_, v_new_1120_);
lean_dec(v_new_1120_);
return v___x_1121_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v_fst_1136_; lean_object* v___x_1137_; lean_object* v_env_1138_; lean_object* v_messages_1139_; lean_object* v_scopes_1140_; lean_object* v_usedQuotCtxts_1141_; lean_object* v_nextMacroScope_1142_; lean_object* v_maxRecDepth_1143_; lean_object* v_ngen_1144_; lean_object* v_auxDeclNGen_1145_; lean_object* v_infoState_1146_; lean_object* v_traceState_1147_; lean_object* v_snapshotTasks_1148_; lean_object* v_prevLinterStates_1149_; lean_object* v_codeQualityEntryTasks_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_cancelTk_1068_);
v___x_1130_ = 0;
lean_inc(v_beginPos_1066_);
lean_inc_ref(v_fileMap_1097_);
lean_inc_ref(v_fileName_1096_);
v___x_1131_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1131_, 0, v_fileName_1096_);
lean_ctor_set(v___x_1131_, 1, v_fileMap_1097_);
lean_ctor_set(v___x_1131_, 2, v___x_1089_);
lean_ctor_set(v___x_1131_, 3, v_beginPos_1066_);
lean_ctor_set(v___x_1131_, 4, v___x_1099_);
lean_ctor_set(v___x_1131_, 5, v___x_1100_);
lean_ctor_set(v___x_1131_, 6, v___x_1101_);
lean_ctor_set(v___x_1131_, 7, v___x_1102_);
lean_ctor_set(v___x_1131_, 8, v___y_1128_);
lean_ctor_set(v___x_1131_, 9, v___x_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*10, v___x_1130_);
lean_inc(v___x_1094_);
v___f_1132_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1132_, 0, v___f_1084_);
lean_closure_set(v___f_1132_, 1, v___x_1131_);
lean_closure_set(v___f_1132_, 2, v___x_1094_);
v___x_1133_ = l_Lean_Core_stderrAsMessages;
v___x_1134_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1098_, v___x_1133_);
lean_dec_ref(v_opts_1098_);
v___x_1135_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1132_, v___x_1134_, v_a_1069_);
v_fst_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_fst_1136_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_st_ref_get(v___x_1094_);
lean_dec(v___x_1094_);
v_env_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_ref(v_env_1138_);
v_messages_1139_ = lean_ctor_get(v___x_1137_, 1);
lean_inc_ref(v_messages_1139_);
v_scopes_1140_ = lean_ctor_get(v___x_1137_, 2);
lean_inc(v_scopes_1140_);
v_usedQuotCtxts_1141_ = lean_ctor_get(v___x_1137_, 3);
lean_inc(v_usedQuotCtxts_1141_);
v_nextMacroScope_1142_ = lean_ctor_get(v___x_1137_, 4);
lean_inc(v_nextMacroScope_1142_);
v_maxRecDepth_1143_ = lean_ctor_get(v___x_1137_, 5);
lean_inc(v_maxRecDepth_1143_);
v_ngen_1144_ = lean_ctor_get(v___x_1137_, 6);
lean_inc_ref(v_ngen_1144_);
v_auxDeclNGen_1145_ = lean_ctor_get(v___x_1137_, 7);
lean_inc_ref(v_auxDeclNGen_1145_);
v_infoState_1146_ = lean_ctor_get(v___x_1137_, 8);
lean_inc_ref(v_infoState_1146_);
v_traceState_1147_ = lean_ctor_get(v___x_1137_, 9);
lean_inc_ref(v_traceState_1147_);
v_snapshotTasks_1148_ = lean_ctor_get(v___x_1137_, 10);
lean_inc_ref(v_snapshotTasks_1148_);
v_prevLinterStates_1149_ = lean_ctor_get(v___x_1137_, 11);
lean_inc(v_prevLinterStates_1149_);
v_codeQualityEntryTasks_1150_ = lean_ctor_get(v___x_1137_, 12);
lean_inc_ref(v_codeQualityEntryTasks_1150_);
lean_dec(v___x_1137_);
v___x_1151_ = lean_string_utf8_byte_size(v_fst_1136_);
v___x_1152_ = lean_nat_dec_eq(v___x_1151_, v___x_1089_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc_ref(v_fileMap_1097_);
v___x_1153_ = l_Lean_FileMap_toPosition(v_fileMap_1097_, v_beginPos_1066_);
lean_dec(v_beginPos_1066_);
v___x_1154_ = 0;
v___x_1155_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_fst_1136_);
v___x_1157_ = l_Lean_MessageData_ofFormat(v___x_1156_);
lean_inc_ref(v_fileName_1096_);
v___x_1158_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1158_, 0, v_fileName_1096_);
lean_ctor_set(v___x_1158_, 1, v___x_1153_);
lean_ctor_set(v___x_1158_, 2, v___x_1100_);
lean_ctor_set(v___x_1158_, 3, v___x_1155_);
lean_ctor_set(v___x_1158_, 4, v___x_1157_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5, v___x_1130_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5 + 1, v___x_1154_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5 + 2, v___x_1130_);
v___x_1159_ = l_Lean_MessageLog_add(v___x_1158_, v_messages_1139_);
v___y_1106_ = v___x_1130_;
v_env_1107_ = v_env_1138_;
v_scopes_1108_ = v_scopes_1140_;
v_usedQuotCtxts_1109_ = v_usedQuotCtxts_1141_;
v_nextMacroScope_1110_ = v_nextMacroScope_1142_;
v_maxRecDepth_1111_ = v_maxRecDepth_1143_;
v_ngen_1112_ = v_ngen_1144_;
v_auxDeclNGen_1113_ = v_auxDeclNGen_1145_;
v_infoState_1114_ = v_infoState_1146_;
v_traceState_1115_ = v_traceState_1147_;
v_snapshotTasks_1116_ = v_snapshotTasks_1148_;
v_prevLinterStates_1117_ = v_prevLinterStates_1149_;
v_codeQualityEntryTasks_1118_ = v_codeQualityEntryTasks_1150_;
v_messages_1119_ = v___x_1159_;
goto v___jp_1105_;
}
else
{
lean_dec(v_fst_1136_);
lean_dec(v_beginPos_1066_);
v___y_1106_ = v___x_1130_;
v_env_1107_ = v_env_1138_;
v_scopes_1108_ = v_scopes_1140_;
v_usedQuotCtxts_1109_ = v_usedQuotCtxts_1141_;
v_nextMacroScope_1110_ = v_nextMacroScope_1142_;
v_maxRecDepth_1111_ = v_maxRecDepth_1143_;
v_ngen_1112_ = v_ngen_1144_;
v_auxDeclNGen_1113_ = v_auxDeclNGen_1145_;
v_infoState_1114_ = v_infoState_1146_;
v_traceState_1115_ = v_traceState_1147_;
v_snapshotTasks_1116_ = v_snapshotTasks_1148_;
v_prevLinterStates_1117_ = v_prevLinterStates_1149_;
v_codeQualityEntryTasks_1118_ = v_codeQualityEntryTasks_1150_;
v_messages_1119_ = v_messages_1139_;
goto v___jp_1105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1166_, lean_object* v_cmds_1167_, lean_object* v_cmdState_1168_, lean_object* v_beginPos_1169_, lean_object* v_snap_1170_, lean_object* v_cancelTk_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1166_, v_cmds_1167_, v_cmdState_1168_, v_beginPos_1169_, v_snap_1170_, v_cancelTk_1171_, v_a_1172_);
lean_dec_ref(v_a_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1175_, lean_object* v_h_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1176_, v_x_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_h_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1181_, v_h_1182_, v_x_1183_, v___y_1184_);
lean_dec_ref(v___y_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1187_, lean_object* v_x_1188_, uint8_t v_isolateStderr_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1188_, v_isolateStderr_1189_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1193_, lean_object* v_x_1194_, lean_object* v_isolateStderr_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_isolateStderr_boxed_1198_; lean_object* v_res_1199_; 
v_isolateStderr_boxed_1198_ = lean_unbox(v_isolateStderr_1195_);
v_res_1199_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1193_, v_x_1194_, v_isolateStderr_boxed_1198_, v___y_1196_);
lean_dec_ref(v___y_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1200_, v___y_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1210_){
_start:
{
lean_object* v_toSnapshotTreeM_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_toSnapshotTreeM_1211_ = lean_ctor_get(v_a_1210_, 1);
lean_inc_ref(v_toSnapshotTreeM_1211_);
lean_dec_ref(v_a_1210_);
v___x_1212_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1213_ = lean_apply_1(v_toSnapshotTreeM_1211_, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1214_){
_start:
{
lean_object* v_toSnapshot_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_toSnapshot_1215_ = lean_ctor_get(v_a_1214_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_a_1214_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_a_1214_, 1);
lean_dec(v_unused_1226_);
v___x_1217_ = v_a_1214_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_toSnapshot_1215_);
lean_dec(v_a_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1219_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1220_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1215_, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1221_);
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1223_ = v___x_1217_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1229_ = l_Lean_Language_Snapshot_transform(v_a_1227_, v___x_1228_);
v___x_1230_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1232_, lean_object* v_opt_1233_){
_start:
{
lean_object* v_name_1234_; lean_object* v_defValue_1235_; lean_object* v_map_1236_; lean_object* v___x_1237_; 
v_name_1234_ = lean_ctor_get(v_opt_1233_, 0);
v_defValue_1235_ = lean_ctor_get(v_opt_1233_, 1);
v_map_1236_ = lean_ctor_get(v_opts_1232_, 0);
v___x_1237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1236_, v_name_1234_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_inc(v_defValue_1235_);
return v_defValue_1235_;
}
else
{
lean_object* v_val_1238_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1237_, 1);
if (lean_obj_tag(v_val_1238_) == 3)
{
lean_object* v_v_1239_; 
v_v_1239_ = lean_ctor_get(v_val_1238_, 0);
lean_inc(v_v_1239_);
lean_dec_ref_known(v_val_1238_, 1);
return v_v_1239_;
}
else
{
lean_dec(v_val_1238_);
lean_inc(v_defValue_1235_);
return v_defValue_1235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1240_, lean_object* v_opt_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1240_, v_opt_1241_);
lean_dec_ref(v_opt_1241_);
lean_dec_ref(v_opts_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1245_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1243_, v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1252_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1253_ = l_Lean_Name_append(v___x_1252_, v___x_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1254_, lean_object* v___x_1255_, uint8_t v_val_1256_, lean_object* v_val_1257_, lean_object* v_val_1258_, lean_object* v___x_1259_, lean_object* v___x_1260_, uint8_t v___x_1261_, lean_object* v_a_1262_, lean_object* v_pos_1263_, lean_object* v___x_1264_, lean_object* v_infoSt_1265_){
_start:
{
lean_object* v___y_1268_; lean_object* v_msgLog_1269_; lean_object* v___y_1275_; lean_object* v_trees_1307_; lean_object* v_size_1308_; uint8_t v___x_1309_; 
v_trees_1307_ = lean_ctor_get(v_infoSt_1265_, 2);
v_size_1308_ = lean_ctor_get(v_trees_1307_, 2);
v___x_1309_ = lean_nat_dec_lt(v___x_1260_, v_size_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = l_outOfBounds___redArg(v___x_1264_);
v___y_1275_ = v___x_1310_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1264_, v_trees_1307_, v___x_1260_);
v___y_1275_ = v___x_1311_;
goto v___jp_1274_;
}
v___jp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1270_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1269_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___y_1268_);
v___x_1272_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1254_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
lean_ctor_set(v___x_1272_, 2, v___x_1271_);
lean_ctor_set(v___x_1272_, 3, v___x_1255_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*4, v_val_1256_);
v___x_1273_ = lean_io_promise_resolve(v___x_1272_, v_val_1257_);
return v___x_1273_;
}
v___jp_1274_:
{
lean_object* v_scopes_1276_; lean_object* v___x_1277_; lean_object* v_opts_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v_hasTrace_1282_; 
v_scopes_1276_ = lean_ctor_get(v_val_1258_, 2);
v___x_1277_ = l_List_head_x21___redArg(v___x_1259_, v_scopes_1276_);
v_opts_1278_ = lean_ctor_get(v___x_1277_, 1);
lean_inc_ref(v_opts_1278_);
lean_dec(v___x_1277_);
v___x_1279_ = l_Lean_MessageLog_empty;
v___x_1280_ = l_Lean_inheritedTraceOptions;
v___x_1281_ = lean_st_ref_get(v___x_1280_);
v_hasTrace_1282_ = lean_ctor_get_uint8(v_opts_1278_, sizeof(void*)*1);
if (v_hasTrace_1282_ == 0)
{
lean_dec(v___x_1281_);
lean_dec_ref(v_opts_1278_);
lean_dec(v___x_1260_);
v___y_1268_ = v___y_1275_;
v_msgLog_1269_ = v___x_1279_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1284_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1285_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1286_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1281_, v_opts_1278_, v___x_1285_);
lean_dec_ref(v_opts_1278_);
lean_dec(v___x_1281_);
if (v___x_1286_ == 0)
{
lean_dec(v___x_1260_);
v___y_1268_ = v___y_1275_;
v_msgLog_1269_ = v___x_1279_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_box(0);
lean_inc_ref(v___y_1275_);
v___x_1288_ = l_Lean_Elab_InfoTree_format(v___y_1275_, v___x_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; double v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_toProcessingContext_1293_; lean_object* v_fileName_1294_; lean_object* v_fileMap_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1290_ = lean_float_of_nat(v___x_1260_);
v___x_1291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1292_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1292_, 0, v___x_1283_);
lean_ctor_set(v___x_1292_, 1, v___x_1287_);
lean_ctor_set(v___x_1292_, 2, v___x_1291_);
lean_ctor_set_float(v___x_1292_, sizeof(void*)*3, v___x_1290_);
lean_ctor_set_float(v___x_1292_, sizeof(void*)*3 + 8, v___x_1290_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*3 + 16, v___x_1261_);
v_toProcessingContext_1293_ = lean_ctor_get(v_a_1262_, 0);
v_fileName_1294_ = lean_ctor_get(v_toProcessingContext_1293_, 1);
v_fileMap_1295_ = lean_ctor_get(v_toProcessingContext_1293_, 2);
v___x_1296_ = l_Lean_MessageData_nil;
v___x_1297_ = l_Lean_MessageData_ofFormat(v_a_1289_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_mk_empty_array_with_capacity(v___x_1298_);
v___x_1300_ = lean_array_push(v___x_1299_, v___x_1297_);
v___x_1301_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1292_);
lean_ctor_set(v___x_1301_, 1, v___x_1296_);
lean_ctor_set(v___x_1301_, 2, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1284_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_inc_ref(v_fileMap_1295_);
v___x_1303_ = l_Lean_FileMap_toPosition(v_fileMap_1295_, v_pos_1263_);
v___x_1304_ = 0;
lean_inc_ref(v_fileName_1294_);
v___x_1305_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1305_, 0, v_fileName_1294_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1287_);
lean_ctor_set(v___x_1305_, 3, v___x_1291_);
lean_ctor_set(v___x_1305_, 4, v___x_1302_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*5, v_val_1256_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*5 + 1, v___x_1304_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*5 + 2, v_val_1256_);
v___x_1306_ = l_Lean_MessageLog_add(v___x_1305_, v___x_1279_);
v___y_1268_ = v___y_1275_;
v_msgLog_1269_ = v___x_1306_;
goto v___jp_1267_;
}
else
{
lean_dec_ref_known(v___x_1288_, 1);
lean_dec(v___x_1260_);
v___y_1268_ = v___y_1275_;
v_msgLog_1269_ = v___x_1279_;
goto v___jp_1267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v_val_1314_, lean_object* v_val_1315_, lean_object* v_val_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v_a_1320_, lean_object* v_pos_1321_, lean_object* v___x_1322_, lean_object* v_infoSt_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v_val_35232__boxed_1325_; uint8_t v___x_35237__boxed_1326_; lean_object* v_res_1327_; 
v_val_35232__boxed_1325_ = lean_unbox(v_val_1314_);
v___x_35237__boxed_1326_ = lean_unbox(v___x_1319_);
v_res_1327_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1312_, v___x_1313_, v_val_35232__boxed_1325_, v_val_1315_, v_val_1316_, v___x_1317_, v___x_1318_, v___x_35237__boxed_1326_, v_a_1320_, v_pos_1321_, v___x_1322_, v_infoSt_1323_);
lean_dec_ref(v_infoSt_1323_);
lean_dec_ref(v___x_1322_);
lean_dec(v_pos_1321_);
lean_dec_ref(v_a_1320_);
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_val_1316_);
lean_dec(v_val_1315_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, uint8_t v_val_1331_, lean_object* v_as_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_b_1335_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1328_);
return v_b_1335_;
}
else
{
lean_object* v_snd_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1356_; 
v_snd_1338_ = lean_ctor_get(v_b_1335_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_b_1335_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; 
v_unused_1357_ = lean_ctor_get(v_b_1335_, 0);
lean_dec(v_unused_1357_);
v___x_1340_ = v_b_1335_;
v_isShared_1341_ = v_isSharedCheck_1356_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snd_1338_);
lean_dec(v_b_1335_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1356_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_a_1342_; lean_object* v_msg_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v_a_1342_ = lean_array_uget_borrowed(v_as_1332_, v_i_1334_);
v_msg_1343_ = lean_ctor_get(v_a_1342_, 1);
v___x_1344_ = lean_box(0);
lean_inc_ref(v___x_1328_);
v___x_1345_ = l_Lean_FileMap_toPosition(v___x_1328_, v___x_1329_);
v___x_1346_ = 0;
v___x_1347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1343_);
lean_inc_ref(v___x_1330_);
v___x_1348_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1348_, 0, v___x_1330_);
lean_ctor_set(v___x_1348_, 1, v___x_1345_);
lean_ctor_set(v___x_1348_, 2, v___x_1344_);
lean_ctor_set(v___x_1348_, 3, v___x_1347_);
lean_ctor_set(v___x_1348_, 4, v_msg_1343_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5, v_val_1331_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5 + 1, v___x_1346_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5 + 2, v_val_1331_);
v___x_1349_ = l_Lean_MessageLog_add(v___x_1348_, v_snd_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___x_1349_);
lean_ctor_set(v___x_1340_, 0, v___x_1344_);
v___x_1351_ = v___x_1340_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
size_t v___x_1352_; size_t v___x_1353_; 
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1334_, v___x_1352_);
v_i_1334_ = v___x_1353_;
v_b_1335_ = v___x_1351_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v_val_1361_, lean_object* v_as_1362_, lean_object* v_sz_1363_, lean_object* v_i_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v_val_35345__boxed_1367_; size_t v_sz_boxed_1368_; size_t v_i_boxed_1369_; lean_object* v_res_1370_; 
v_val_35345__boxed_1367_ = lean_unbox(v_val_1361_);
v_sz_boxed_1368_ = lean_unbox_usize(v_sz_1363_);
lean_dec(v_sz_1363_);
v_i_boxed_1369_ = lean_unbox_usize(v_i_1364_);
lean_dec(v_i_1364_);
v_res_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1358_, v___x_1359_, v___x_1360_, v_val_35345__boxed_1367_, v_as_1362_, v_sz_boxed_1368_, v_i_boxed_1369_, v_b_1365_);
lean_dec_ref(v_as_1362_);
lean_dec(v___x_1359_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1371_, lean_object* v___x_1372_, lean_object* v___x_1373_, uint8_t v_val_1374_, lean_object* v_as_1375_, size_t v_sz_1376_, size_t v_i_1377_, lean_object* v_b_1378_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_usize_dec_lt(v_i_1377_, v_sz_1376_);
if (v___x_1380_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___x_1371_);
return v_b_1378_;
}
else
{
lean_object* v_snd_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1399_; 
v_snd_1381_ = lean_ctor_get(v_b_1378_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_b_1378_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_b_1378_, 0);
lean_dec(v_unused_1400_);
v___x_1383_ = v_b_1378_;
v_isShared_1384_ = v_isSharedCheck_1399_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1381_);
lean_dec(v_b_1378_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1399_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_a_1385_; lean_object* v_msg_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v_a_1385_ = lean_array_uget_borrowed(v_as_1375_, v_i_1377_);
v_msg_1386_ = lean_ctor_get(v_a_1385_, 1);
v___x_1387_ = lean_box(0);
lean_inc_ref(v___x_1371_);
v___x_1388_ = l_Lean_FileMap_toPosition(v___x_1371_, v___x_1372_);
v___x_1389_ = 0;
v___x_1390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1386_);
lean_inc_ref(v___x_1373_);
v___x_1391_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1391_, 0, v___x_1373_);
lean_ctor_set(v___x_1391_, 1, v___x_1388_);
lean_ctor_set(v___x_1391_, 2, v___x_1387_);
lean_ctor_set(v___x_1391_, 3, v___x_1390_);
lean_ctor_set(v___x_1391_, 4, v_msg_1386_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5, v_val_1374_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5 + 1, v___x_1389_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*5 + 2, v_val_1374_);
v___x_1392_ = l_Lean_MessageLog_add(v___x_1391_, v_snd_1381_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1392_);
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1394_ = v___x_1383_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1377_, v___x_1395_);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1371_, v___x_1372_, v___x_1373_, v_val_1374_, v_as_1375_, v_sz_1376_, v___x_1396_, v___x_1394_);
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1401_, lean_object* v___x_1402_, lean_object* v___x_1403_, lean_object* v_val_1404_, lean_object* v_as_1405_, lean_object* v_sz_1406_, lean_object* v_i_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_val_35397__boxed_1410_; size_t v_sz_boxed_1411_; size_t v_i_boxed_1412_; lean_object* v_res_1413_; 
v_val_35397__boxed_1410_ = lean_unbox(v_val_1404_);
v_sz_boxed_1411_ = lean_unbox_usize(v_sz_1406_);
lean_dec(v_sz_1406_);
v_i_boxed_1412_ = lean_unbox_usize(v_i_1407_);
lean_dec(v_i_1407_);
v_res_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1401_, v___x_1402_, v___x_1403_, v_val_35397__boxed_1410_, v_as_1405_, v_sz_boxed_1411_, v_i_boxed_1412_, v_b_1408_);
lean_dec_ref(v_as_1405_);
lean_dec(v___x_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1414_, lean_object* v___x_1415_, lean_object* v___x_1416_, lean_object* v___x_1417_, uint8_t v_val_1418_, lean_object* v_n_1419_, lean_object* v_b_1420_){
_start:
{
if (lean_obj_tag(v_n_1419_) == 0)
{
lean_object* v_cs_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v_fst_1428_; 
v_cs_1422_ = lean_ctor_get(v_n_1419_, 0);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_b_1420_);
v_sz_1425_ = lean_array_size(v_cs_1422_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1414_, v___x_1415_, v___x_1416_, v___x_1417_, v_val_1418_, v_cs_1422_, v_sz_1425_, v___x_1426_, v___x_1424_);
v_fst_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_fst_1428_);
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
lean_dec_ref(v___x_1427_);
v_val_1431_ = lean_ctor_get(v_fst_1428_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v_fst_1428_, 1);
return v_val_1431_;
}
}
else
{
lean_object* v_vs_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; size_t v_sz_1435_; size_t v___x_1436_; lean_object* v___x_1437_; lean_object* v_fst_1438_; 
v_vs_1432_ = lean_ctor_get(v_n_1419_, 0);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v_b_1420_);
v_sz_1435_ = lean_array_size(v_vs_1432_);
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1415_, v___x_1416_, v___x_1417_, v_val_1418_, v_vs_1432_, v_sz_1435_, v___x_1436_, v___x_1434_);
v_fst_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_fst_1438_);
if (lean_obj_tag(v_fst_1438_) == 0)
{
lean_object* v_snd_1439_; lean_object* v___x_1440_; 
v_snd_1439_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_snd_1439_);
lean_dec_ref(v___x_1437_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_snd_1439_);
return v___x_1440_;
}
else
{
lean_object* v_val_1441_; 
lean_dec_ref(v___x_1437_);
v_val_1441_ = lean_ctor_get(v_fst_1438_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v_fst_1438_, 1);
return v_val_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1442_, lean_object* v___x_1443_, lean_object* v___x_1444_, lean_object* v___x_1445_, uint8_t v_val_1446_, lean_object* v_as_1447_, size_t v_sz_1448_, size_t v_i_1449_, lean_object* v_b_1450_){
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
lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_box(0);
v_a_1458_ = lean_array_uget_borrowed(v_as_1447_, v_i_1449_);
lean_inc(v_snd_1453_);
lean_inc_ref(v___x_1445_);
lean_inc_ref(v___x_1443_);
v___x_1459_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1442_, v___x_1443_, v___x_1444_, v___x_1445_, v_val_1446_, v_a_1458_, v_snd_1453_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec_ref(v___x_1445_);
lean_dec_ref(v___x_1443_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1460_);
v___x_1462_ = v___x_1455_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_snd_1453_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; 
lean_dec(v_snd_1453_);
v_a_1464_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1459_, 1);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_a_1464_);
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1466_ = v___x_1455_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_a_1464_);
v___x_1466_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
size_t v___x_1467_; size_t v___x_1468_; 
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1449_, v___x_1467_);
v_i_1449_ = v___x_1468_;
v_b_1450_ = v___x_1466_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1473_, lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v_val_1477_, lean_object* v_as_1478_, lean_object* v_sz_1479_, lean_object* v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_val_35448__boxed_1483_; size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_val_35448__boxed_1483_ = lean_unbox(v_val_1477_);
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1473_, v___x_1474_, v___x_1475_, v___x_1476_, v_val_35448__boxed_1483_, v_as_1478_, v_sz_boxed_1484_, v_i_boxed_1485_, v_b_1481_);
lean_dec_ref(v_as_1478_);
lean_dec(v___x_1475_);
lean_dec_ref(v_init_1473_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1487_, lean_object* v___x_1488_, lean_object* v___x_1489_, lean_object* v___x_1490_, lean_object* v_val_1491_, lean_object* v_n_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_val_35464__boxed_1495_; lean_object* v_res_1496_; 
v_val_35464__boxed_1495_ = lean_unbox(v_val_1491_);
v_res_1496_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1487_, v___x_1488_, v___x_1489_, v___x_1490_, v_val_35464__boxed_1495_, v_n_1492_, v_b_1493_);
lean_dec_ref(v_n_1492_);
lean_dec(v___x_1489_);
lean_dec_ref(v_init_1487_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v___x_1499_, uint8_t v_val_1500_, lean_object* v_as_1501_, size_t v_sz_1502_, size_t v_i_1503_, lean_object* v_b_1504_){
_start:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_usize_dec_lt(v_i_1503_, v_sz_1502_);
if (v___x_1506_ == 0)
{
lean_dec_ref(v___x_1499_);
lean_dec_ref(v___x_1497_);
return v_b_1504_;
}
else
{
lean_object* v_snd_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1525_; 
v_snd_1507_ = lean_ctor_get(v_b_1504_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_b_1504_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v_b_1504_, 0);
lean_dec(v_unused_1526_);
v___x_1509_ = v_b_1504_;
v_isShared_1510_ = v_isSharedCheck_1525_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snd_1507_);
lean_dec(v_b_1504_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1525_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_a_1511_; lean_object* v_msg_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v_a_1511_ = lean_array_uget_borrowed(v_as_1501_, v_i_1503_);
v_msg_1512_ = lean_ctor_get(v_a_1511_, 1);
v___x_1513_ = lean_box(0);
lean_inc_ref(v___x_1497_);
v___x_1514_ = l_Lean_FileMap_toPosition(v___x_1497_, v___x_1498_);
v___x_1515_ = 0;
v___x_1516_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1512_);
lean_inc_ref(v___x_1499_);
v___x_1517_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1517_, 0, v___x_1499_);
lean_ctor_set(v___x_1517_, 1, v___x_1514_);
lean_ctor_set(v___x_1517_, 2, v___x_1513_);
lean_ctor_set(v___x_1517_, 3, v___x_1516_);
lean_ctor_set(v___x_1517_, 4, v_msg_1512_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*5, v_val_1500_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*5 + 1, v___x_1515_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*5 + 2, v_val_1500_);
v___x_1518_ = l_Lean_MessageLog_add(v___x_1517_, v_snd_1507_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v___x_1518_);
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1520_ = v___x_1509_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
size_t v___x_1521_; size_t v___x_1522_; 
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1503_, v___x_1521_);
v_i_1503_ = v___x_1522_;
v_b_1504_ = v___x_1520_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_val_1530_, lean_object* v_as_1531_, lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_val_35546__boxed_1536_; size_t v_sz_boxed_1537_; size_t v_i_boxed_1538_; lean_object* v_res_1539_; 
v_val_35546__boxed_1536_ = lean_unbox(v_val_1530_);
v_sz_boxed_1537_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1538_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1527_, v___x_1528_, v___x_1529_, v_val_35546__boxed_1536_, v_as_1531_, v_sz_boxed_1537_, v_i_boxed_1538_, v_b_1534_);
lean_dec_ref(v_as_1531_);
lean_dec(v___x_1528_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1540_, lean_object* v___x_1541_, lean_object* v___x_1542_, uint8_t v_val_1543_, lean_object* v_as_1544_, size_t v_sz_1545_, size_t v_i_1546_, lean_object* v_b_1547_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
if (v___x_1549_ == 0)
{
lean_dec_ref(v___x_1542_);
lean_dec_ref(v___x_1540_);
return v_b_1547_;
}
else
{
lean_object* v_snd_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1568_; 
v_snd_1550_ = lean_ctor_get(v_b_1547_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_b_1547_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_b_1547_, 0);
lean_dec(v_unused_1569_);
v___x_1552_ = v_b_1547_;
v_isShared_1553_ = v_isSharedCheck_1568_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_snd_1550_);
lean_dec(v_b_1547_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1568_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_a_1554_; lean_object* v_msg_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v_a_1554_ = lean_array_uget_borrowed(v_as_1544_, v_i_1546_);
v_msg_1555_ = lean_ctor_get(v_a_1554_, 1);
v___x_1556_ = lean_box(0);
lean_inc_ref(v___x_1540_);
v___x_1557_ = l_Lean_FileMap_toPosition(v___x_1540_, v___x_1541_);
v___x_1558_ = 0;
v___x_1559_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1555_);
lean_inc_ref(v___x_1542_);
v___x_1560_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1560_, 0, v___x_1542_);
lean_ctor_set(v___x_1560_, 1, v___x_1557_);
lean_ctor_set(v___x_1560_, 2, v___x_1556_);
lean_ctor_set(v___x_1560_, 3, v___x_1559_);
lean_ctor_set(v___x_1560_, 4, v_msg_1555_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*5, v_val_1543_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*5 + 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*5 + 2, v_val_1543_);
v___x_1561_ = l_Lean_MessageLog_add(v___x_1560_, v_snd_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v___x_1561_);
lean_ctor_set(v___x_1552_, 0, v___x_1556_);
v___x_1563_ = v___x_1552_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = ((size_t)1ULL);
v___x_1565_ = lean_usize_add(v_i_1546_, v___x_1564_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1540_, v___x_1541_, v___x_1542_, v_val_1543_, v_as_1544_, v_sz_1545_, v___x_1565_, v___x_1563_);
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v_val_1573_, lean_object* v_as_1574_, lean_object* v_sz_1575_, lean_object* v_i_1576_, lean_object* v_b_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_val_35598__boxed_1579_; size_t v_sz_boxed_1580_; size_t v_i_boxed_1581_; lean_object* v_res_1582_; 
v_val_35598__boxed_1579_ = lean_unbox(v_val_1573_);
v_sz_boxed_1580_ = lean_unbox_usize(v_sz_1575_);
lean_dec(v_sz_1575_);
v_i_boxed_1581_ = lean_unbox_usize(v_i_1576_);
lean_dec(v_i_1576_);
v_res_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1570_, v___x_1571_, v___x_1572_, v_val_35598__boxed_1579_, v_as_1574_, v_sz_boxed_1580_, v_i_boxed_1581_, v_b_1577_);
lean_dec_ref(v_as_1574_);
lean_dec(v___x_1571_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, uint8_t v_val_1586_, lean_object* v_t_1587_, lean_object* v_init_1588_){
_start:
{
lean_object* v_root_1590_; lean_object* v_tail_1591_; lean_object* v___x_1592_; 
v_root_1590_ = lean_ctor_get(v_t_1587_, 0);
v_tail_1591_ = lean_ctor_get(v_t_1587_, 1);
lean_inc_ref(v___x_1585_);
lean_inc_ref(v___x_1583_);
lean_inc_ref(v_init_1588_);
v___x_1592_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1588_, v___x_1583_, v___x_1584_, v___x_1585_, v_val_1586_, v_root_1590_, v_init_1588_);
lean_dec_ref(v_init_1588_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; 
lean_dec_ref(v___x_1585_);
lean_dec_ref(v___x_1583_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
return v_a_1593_;
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; size_t v_sz_1597_; size_t v___x_1598_; lean_object* v___x_1599_; lean_object* v_fst_1600_; 
v_a_1594_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_a_1594_);
v_sz_1597_ = lean_array_size(v_tail_1591_);
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1583_, v___x_1584_, v___x_1585_, v_val_1586_, v_tail_1591_, v_sz_1597_, v___x_1598_, v___x_1596_);
v_fst_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_fst_1600_);
if (lean_obj_tag(v_fst_1600_) == 0)
{
lean_object* v_snd_1601_; 
v_snd_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_snd_1601_);
lean_dec_ref(v___x_1599_);
return v_snd_1601_;
}
else
{
lean_object* v_val_1602_; 
lean_dec_ref(v___x_1599_);
v_val_1602_ = lean_ctor_get(v_fst_1600_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v_fst_1600_, 1);
return v_val_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v___x_1605_, lean_object* v_val_1606_, lean_object* v_t_1607_, lean_object* v_init_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v_val_35649__boxed_1610_; lean_object* v_res_1611_; 
v_val_35649__boxed_1610_ = lean_unbox(v_val_1606_);
v_res_1611_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1603_, v___x_1604_, v___x_1605_, v_val_35649__boxed_1610_, v_t_1607_, v_init_1608_);
lean_dec_ref(v_t_1607_);
lean_dec(v___x_1604_);
return v_res_1611_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_unsigned_to_nat(1u);
v___x_1613_ = l_Lean_firstFrontendMacroScope;
v___x_1614_ = lean_nat_add(v___x_1613_, v___x_1612_);
return v___x_1614_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v_a_1625_, lean_object* v_opts_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, size_t v___x_1630_, uint8_t v___x_1631_, lean_object* v_env_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, lean_object* v___x_1635_, uint8_t v_val_1636_, lean_object* v___x_1637_, lean_object* v_pos_1638_, lean_object* v___x_1639_, lean_object* v___x_1640_, lean_object* v___x_1641_, uint8_t v___x_1642_, lean_object* v_x_1643_){
_start:
{
lean_object* v_toProcessingContext_1645_; lean_object* v_fileName_1646_; lean_object* v_fileMap_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___y_1671_; lean_object* v___x_1688_; uint8_t v___y_1690_; lean_object* v_env_1710_; uint8_t v___x_1711_; 
v_toProcessingContext_1645_ = lean_ctor_get(v_a_1625_, 0);
v_fileName_1646_ = lean_ctor_get(v_toProcessingContext_1645_, 1);
v_fileMap_1647_ = lean_ctor_get(v_toProcessingContext_1645_, 2);
v___x_1648_ = lean_box(0);
v___x_1649_ = l_Lean_Core_getMaxHeartbeats(v_opts_1626_);
v___x_1650_ = l_Lean_firstFrontendMacroScope;
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1654_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
lean_inc(v___x_1627_);
v___x_1655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1627_);
lean_ctor_set(v___x_1655_, 1, v___x_1652_);
lean_ctor_set(v___x_1655_, 2, v___x_1648_);
v___x_1656_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1657_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1658_ = lean_mk_empty_array_with_capacity(v___x_1628_);
lean_inc_ref(v___x_1658_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_inc_n(v___x_1629_, 2);
v___x_1660_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set(v___x_1660_, 1, v___x_1658_);
lean_ctor_set(v___x_1660_, 2, v___x_1629_);
lean_ctor_set(v___x_1660_, 3, v___x_1629_);
lean_ctor_set_usize(v___x_1660_, 4, v___x_1630_);
v___x_1661_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1660_, 2);
v___x_1662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1660_);
lean_ctor_set(v___x_1662_, 2, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1663_, 0, v___x_1656_);
lean_ctor_set(v___x_1663_, 1, v___x_1656_);
lean_ctor_set(v___x_1663_, 2, v___x_1660_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*3, v___x_1631_);
v___x_1664_ = lean_mk_empty_array_with_capacity(v___x_1629_);
lean_inc_ref(v___x_1664_);
lean_inc_ref(v___x_1633_);
v___x_1665_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1665_, 0, v_env_1632_);
lean_ctor_set(v___x_1665_, 1, v___x_1653_);
lean_ctor_set(v___x_1665_, 2, v___x_1654_);
lean_ctor_set(v___x_1665_, 3, v___x_1655_);
lean_ctor_set(v___x_1665_, 4, v___x_1633_);
lean_ctor_set(v___x_1665_, 5, v___x_1657_);
lean_ctor_set(v___x_1665_, 6, v___x_1662_);
lean_ctor_set(v___x_1665_, 7, v___x_1663_);
lean_ctor_set(v___x_1665_, 8, v___x_1664_);
v___x_1666_ = lean_st_mk_ref(v___x_1665_);
v___x_1667_ = lean_st_ref_get(v___x_1634_);
v___x_1668_ = l_Lean_diagnostics;
v___x_1669_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1626_, v___x_1668_);
v___x_1688_ = lean_st_ref_get(v___x_1666_);
v_env_1710_ = lean_ctor_get(v___x_1688_, 0);
lean_inc_ref(v_env_1710_);
lean_dec(v___x_1688_);
v___x_1711_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1710_);
lean_dec_ref(v_env_1710_);
if (v___x_1669_ == 0)
{
if (v___x_1711_ == 0)
{
v___y_1690_ = v___x_1642_;
goto v___jp_1689_;
}
else
{
v___y_1690_ = v___x_1669_;
goto v___jp_1689_;
}
}
else
{
v___y_1690_ = v___x_1711_;
goto v___jp_1689_;
}
v___jp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1672_ = l_Lean_maxRecDepth;
v___x_1673_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1626_, v___x_1672_);
lean_inc(v___x_1629_);
lean_inc(v___x_1627_);
lean_inc_ref(v_fileMap_1647_);
lean_inc_ref(v_fileName_1646_);
v___x_1674_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1674_, 0, v_fileName_1646_);
lean_ctor_set(v___x_1674_, 1, v_fileMap_1647_);
lean_ctor_set(v___x_1674_, 2, v_opts_1626_);
lean_ctor_set(v___x_1674_, 3, v___x_1673_);
lean_ctor_set(v___x_1674_, 4, v___x_1627_);
lean_ctor_set(v___x_1674_, 5, v___x_1648_);
lean_ctor_set(v___x_1674_, 6, v___x_1629_);
lean_ctor_set(v___x_1674_, 7, v___x_1649_);
lean_ctor_set(v___x_1674_, 8, v___x_1627_);
lean_ctor_set(v___x_1674_, 9, v___x_1650_);
lean_ctor_set(v___x_1674_, 10, v___x_1635_);
lean_ctor_set(v___x_1674_, 11, v___x_1667_);
v___x_1675_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___x_1629_);
lean_ctor_set(v___x_1675_, 2, v___x_1651_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*3, v___x_1669_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*3 + 1, v_val_1636_);
v___x_1676_ = l_Lean_Language_SnapshotTree_trace(v___x_1637_, v___x_1675_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref_known(v___x_1675_, 3);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; lean_object* v_traceState_1678_; lean_object* v_traces_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref_known(v___x_1676_, 1);
lean_dec_ref(v___x_1641_);
v___x_1677_ = lean_st_ref_get(v___x_1666_);
lean_dec(v___x_1666_);
v_traceState_1678_ = lean_ctor_get(v___x_1677_, 4);
lean_inc_ref(v_traceState_1678_);
lean_dec(v___x_1677_);
v_traces_1679_ = lean_ctor_get(v_traceState_1678_, 0);
lean_inc_ref(v_traces_1679_);
lean_dec_ref(v_traceState_1678_);
v___x_1680_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1646_);
lean_inc_ref(v_fileMap_1647_);
v___x_1681_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1647_, v_pos_1638_, v_fileName_1646_, v_val_1636_, v_traces_1679_, v___x_1680_);
lean_dec_ref(v_traces_1679_);
v___x_1682_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1639_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_ctor_set(v___x_1683_, 2, v___x_1640_);
lean_ctor_set(v___x_1683_, 3, v___x_1633_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*4, v_val_1636_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v___x_1664_);
v___x_1685_ = lean_task_pure(v___x_1684_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1676_, 1);
lean_dec(v___x_1666_);
lean_dec(v___x_1640_);
lean_dec_ref(v___x_1639_);
lean_dec_ref(v___x_1633_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1641_);
lean_ctor_set(v___x_1686_, 1, v___x_1664_);
v___x_1687_ = lean_task_pure(v___x_1686_);
return v___x_1687_;
}
}
v___jp_1689_:
{
if (v___y_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v_env_1692_; lean_object* v_nextMacroScope_1693_; lean_object* v_ngen_1694_; lean_object* v_auxDeclNGen_1695_; lean_object* v_traceState_1696_; lean_object* v_messages_1697_; lean_object* v_infoState_1698_; lean_object* v_snapshotTasks_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
v___x_1691_ = lean_st_ref_take(v___x_1666_);
v_env_1692_ = lean_ctor_get(v___x_1691_, 0);
v_nextMacroScope_1693_ = lean_ctor_get(v___x_1691_, 1);
v_ngen_1694_ = lean_ctor_get(v___x_1691_, 2);
v_auxDeclNGen_1695_ = lean_ctor_get(v___x_1691_, 3);
v_traceState_1696_ = lean_ctor_get(v___x_1691_, 4);
v_messages_1697_ = lean_ctor_get(v___x_1691_, 6);
v_infoState_1698_ = lean_ctor_get(v___x_1691_, 7);
v_snapshotTasks_1699_ = lean_ctor_get(v___x_1691_, 8);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1691_, 5);
lean_dec(v_unused_1709_);
v___x_1701_ = v___x_1691_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_snapshotTasks_1699_);
lean_inc(v_infoState_1698_);
lean_inc(v_messages_1697_);
lean_inc(v_traceState_1696_);
lean_inc(v_auxDeclNGen_1695_);
lean_inc(v_ngen_1694_);
lean_inc(v_nextMacroScope_1693_);
lean_inc(v_env_1692_);
lean_dec(v___x_1691_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = l_Lean_Kernel_enableDiag(v_env_1692_, v___x_1669_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 5, v___x_1657_);
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_nextMacroScope_1693_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_ngen_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_auxDeclNGen_1695_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_traceState_1696_);
lean_ctor_set(v_reuseFailAlloc_1707_, 5, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_messages_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 7, v_infoState_1698_);
lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_snapshotTasks_1699_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_st_ref_put(v___x_1666_, v___x_1705_);
lean_inc(v___x_1666_);
v___y_1671_ = v___x_1666_;
goto v___jp_1670_;
}
}
}
else
{
lean_inc(v___x_1666_);
v___y_1671_ = v___x_1666_;
goto v___jp_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v_a_1712_ = _args[0];
lean_object* v_opts_1713_ = _args[1];
lean_object* v___x_1714_ = _args[2];
lean_object* v___x_1715_ = _args[3];
lean_object* v___x_1716_ = _args[4];
lean_object* v___x_1717_ = _args[5];
lean_object* v___x_1718_ = _args[6];
lean_object* v_env_1719_ = _args[7];
lean_object* v___x_1720_ = _args[8];
lean_object* v___x_1721_ = _args[9];
lean_object* v___x_1722_ = _args[10];
lean_object* v_val_1723_ = _args[11];
lean_object* v___x_1724_ = _args[12];
lean_object* v_pos_1725_ = _args[13];
lean_object* v___x_1726_ = _args[14];
lean_object* v___x_1727_ = _args[15];
lean_object* v___x_1728_ = _args[16];
lean_object* v___x_1729_ = _args[17];
lean_object* v_x_1730_ = _args[18];
lean_object* v___y_1731_ = _args[19];
_start:
{
size_t v___x_35709__boxed_1732_; uint8_t v___x_35710__boxed_1733_; uint8_t v_val_35714__boxed_1734_; uint8_t v___x_35719__boxed_1735_; lean_object* v_res_1736_; 
v___x_35709__boxed_1732_ = lean_unbox_usize(v___x_1717_);
lean_dec(v___x_1717_);
v___x_35710__boxed_1733_ = lean_unbox(v___x_1718_);
v_val_35714__boxed_1734_ = lean_unbox(v_val_1723_);
v___x_35719__boxed_1735_ = lean_unbox(v___x_1729_);
v_res_1736_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v_a_1712_, v_opts_1713_, v___x_1714_, v___x_1715_, v___x_1716_, v___x_35709__boxed_1732_, v___x_35710__boxed_1733_, v_env_1719_, v___x_1720_, v___x_1721_, v___x_1722_, v_val_35714__boxed_1734_, v___x_1724_, v_pos_1725_, v___x_1726_, v___x_1727_, v___x_1728_, v___x_35719__boxed_1735_, v_x_1730_);
lean_dec(v_pos_1725_);
lean_dec(v___x_1721_);
lean_dec(v___x_1715_);
lean_dec_ref(v_a_1712_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1737_, lean_object* v___x_1738_, lean_object* v_parserState_1739_, lean_object* v_x_1740_){
_start:
{
lean_object* v_toProcessingContext_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_toProcessingContext_1741_ = lean_ctor_get(v_a_1737_, 0);
v___x_1742_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1741_);
v___x_1743_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1741_, v___x_1738_, v_parserState_1739_, v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1744_, lean_object* v___x_1745_, lean_object* v_parserState_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1744_, v___x_1745_, v_parserState_1746_, v_x_1747_);
lean_dec_ref(v_a_1744_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1750_, size_t v_i_1751_, size_t v_stop_1752_, lean_object* v_b_1753_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_usize_dec_eq(v_i_1751_, v_stop_1752_);
if (v___x_1755_ == 0)
{
lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; 
v___f_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1757_ = lean_array_uget_borrowed(v_as_1750_, v_i_1751_);
lean_inc(v___x_1757_);
v___x_1758_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1756_, v___x_1757_);
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1751_, v___x_1759_);
v_i_1751_ = v___x_1760_;
v_b_1753_ = v___x_1758_;
goto _start;
}
else
{
return v_b_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1762_, lean_object* v_i_1763_, lean_object* v_stop_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_i_boxed_1767_; size_t v_stop_boxed_1768_; lean_object* v_res_1769_; 
v_i_boxed_1767_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_stop_boxed_1768_ = lean_unbox_usize(v_stop_1764_);
lean_dec(v_stop_1764_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1762_, v_i_boxed_1767_, v_stop_boxed_1768_, v_b_1765_);
lean_dec_ref(v_as_1762_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1770_, lean_object* v_cmds_1771_, lean_object* v_stx_1772_, lean_object* v_newParserState_1773_, lean_object* v_val_1774_, lean_object* v_sync_1775_, lean_object* v_val_1776_, lean_object* v_a_1777_, lean_object* v_oldNext_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v_sync_boxed_1780_; lean_object* v_res_1781_; 
v_sync_boxed_1780_ = lean_unbox(v_sync_1775_);
v_res_1781_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1770_, v_cmds_1771_, v_stx_1772_, v_newParserState_1773_, v_val_1774_, v_sync_boxed_1780_, v_val_1776_, v_a_1777_, v_oldNext_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1782_, lean_object* v_cmds_1783_, lean_object* v_stx_1784_, lean_object* v_newParserState_1785_, lean_object* v_val_1786_, uint8_t v_sync_1787_, lean_object* v_val_1788_, lean_object* v_a_1789_, lean_object* v_oldResult_1790_){
_start:
{
lean_object* v_task_1792_; lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; 
v_task_1792_ = lean_ctor_get(v_val_1782_, 3);
lean_inc_ref(v_task_1792_);
lean_dec_ref(v_val_1782_);
v___x_1793_ = lean_box(v_sync_1787_);
lean_inc_ref(v_a_1789_);
v___f_1794_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1794_, 0, v_oldResult_1790_);
lean_closure_set(v___f_1794_, 1, v_cmds_1783_);
lean_closure_set(v___f_1794_, 2, v_stx_1784_);
lean_closure_set(v___f_1794_, 3, v_newParserState_1785_);
lean_closure_set(v___f_1794_, 4, v_val_1786_);
lean_closure_set(v___f_1794_, 5, v___x_1793_);
lean_closure_set(v___f_1794_, 6, v_val_1788_);
lean_closure_set(v___f_1794_, 7, v_a_1789_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = 1;
v___x_1797_ = l_BaseIO_chainTask___redArg(v_task_1792_, v___f_1794_, v___x_1795_, v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1798_, lean_object* v_cmds_1799_, lean_object* v_stx_1800_, lean_object* v_newParserState_1801_, lean_object* v_val_1802_, lean_object* v_sync_1803_, lean_object* v_val_1804_, lean_object* v_a_1805_, lean_object* v_oldResult_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v_sync_boxed_1808_; lean_object* v_res_1809_; 
v_sync_boxed_1808_ = lean_unbox(v_sync_1803_);
v_res_1809_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1798_, v_cmds_1799_, v_stx_1800_, v_newParserState_1801_, v_val_1802_, v_sync_boxed_1808_, v_val_1804_, v_a_1805_, v_oldResult_1806_);
lean_dec_ref(v_a_1805_);
return v_res_1809_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1818_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1819_ = l_Lean_Name_append(v___x_1818_, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1823_, lean_object* v_val_1824_, lean_object* v_cmds_1825_, lean_object* v_fst_1826_, lean_object* v_fst_1827_, uint8_t v_val_1828_, lean_object* v_a_1829_, lean_object* v_snd_1830_, lean_object* v___x_1831_, uint8_t v___x_1832_, lean_object* v_fst_1833_, lean_object* v_val_1834_, lean_object* v_val_1835_, lean_object* v___x_1836_, lean_object* v___f_1837_, lean_object* v___f_1838_, lean_object* v___f_1839_, lean_object* v_pos_1840_, lean_object* v_cmdState_1841_, lean_object* v_val_1842_, lean_object* v___x_1843_, lean_object* v_opts_1844_, lean_object* v___x_1845_, lean_object* v_snd_1846_, lean_object* v_prom_1847_, lean_object* v_old_x3f_1848_, lean_object* v_parseCancelTk_1849_, lean_object* v_next_x3f_1850_){
_start:
{
lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v_snapshotTasks_1857_; lean_object* v___y_1858_; lean_object* v_traceTask_1859_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; size_t v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_env_1898_; lean_object* v_messages_1899_; lean_object* v_scopes_1900_; lean_object* v_infoState_1901_; lean_object* v_traceState_1902_; lean_object* v_snapshotTasks_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v_reportedCmdState_1909_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; size_t v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_reportedCmdState_1966_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; size_t v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_2022_; 
if (lean_obj_tag(v_next_x3f_1850_) == 0)
{
lean_object* v___x_2075_; 
lean_dec_ref(v_parseCancelTk_1849_);
v___x_2075_ = lean_box(0);
v___y_2022_ = v___x_2075_;
goto v___jp_2021_;
}
else
{
lean_object* v_toProcessingContext_2076_; lean_object* v_val_2077_; lean_object* v_pos_2078_; lean_object* v_endPos_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_toProcessingContext_2076_ = lean_ctor_get(v_a_1829_, 0);
v_val_2077_ = lean_ctor_get(v_next_x3f_1850_, 0);
v_pos_2078_ = lean_ctor_get(v_fst_1827_, 0);
v_endPos_2079_ = lean_ctor_get(v_toProcessingContext_2076_, 3);
v___x_2080_ = lean_box(0);
lean_inc(v_endPos_2079_);
lean_inc(v_pos_2078_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_pos_2078_);
lean_ctor_set(v___x_2081_, 1, v_endPos_2079_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_parseCancelTk_1849_);
v___x_2084_ = l_IO_Promise_result_x21___redArg(v_val_2077_);
v___x_2085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2080_);
lean_ctor_set(v___x_2085_, 1, v___x_2082_);
lean_ctor_set(v___x_2085_, 2, v___x_2083_);
lean_ctor_set(v___x_2085_, 3, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
v___y_2022_ = v___x_2086_;
goto v___jp_2021_;
}
v___jp_1852_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1855_);
lean_ctor_set(v___x_1860_, 1, v___x_1823_);
lean_ctor_set(v___x_1860_, 2, v___y_1854_);
lean_ctor_set(v___x_1860_, 3, v_traceTask_1859_);
v___x_1861_ = lean_array_push(v_snapshotTasks_1857_, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1853_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_io_promise_resolve(v___x_1862_, v_val_1824_);
if (lean_obj_tag(v_next_x3f_1850_) == 1)
{
lean_object* v_val_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_val_1864_ = lean_ctor_get(v_next_x3f_1850_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v_next_x3f_1850_, 1);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_array_push(v_cmds_1825_, v_fst_1826_);
v___x_1867_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1865_, v_fst_1827_, v___y_1856_, v_val_1864_, v_val_1828_, v___y_1858_, v___x_1866_, v_a_1829_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; 
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___y_1856_);
lean_dec(v_next_x3f_1850_);
lean_dec_ref(v_fst_1827_);
lean_dec(v_fst_1826_);
lean_dec_ref(v_cmds_1825_);
v___x_1868_ = lean_box(0);
return v___x_1868_;
}
}
v___jp_1869_:
{
lean_object* v_snapshotTasks_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_snapshotTasks_1876_ = lean_ctor_get(v___y_1873_, 10);
lean_inc_ref(v_snapshotTasks_1876_);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___y_1874_);
lean_dec(v___y_1874_);
lean_inc_ref(v___y_1870_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___y_1870_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_task_pure(v___x_1878_);
v___y_1853_ = v___y_1870_;
v___y_1854_ = v___y_1871_;
v___y_1855_ = v___y_1872_;
v___y_1856_ = v___y_1873_;
v_snapshotTasks_1857_ = v_snapshotTasks_1876_;
v___y_1858_ = v___y_1875_;
v_traceTask_1859_ = v___x_1879_;
goto v___jp_1852_;
}
v___jp_1880_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_opts_1919_; uint8_t v_hasTrace_1920_; 
v___x_1910_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1899_);
v___x_1911_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1911_, 0, v___y_1908_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
lean_ctor_set(v___x_1911_, 2, v___y_1895_);
lean_ctor_set(v___x_1911_, 3, v_traceState_1902_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*4, v_val_1828_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v_reportedCmdState_1909_);
v___x_1913_ = lean_io_promise_resolve(v___x_1912_, v_val_1835_);
v___x_1914_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1901_);
lean_inc(v___y_1906_);
v___x_1915_ = l_BaseIO_chainTask___redArg(v___x_1914_, v___y_1905_, v___y_1906_, v___x_1832_);
v___x_1916_ = l_Lean_inheritedTraceOptions;
v___x_1917_ = lean_st_ref_get(v___x_1916_);
v___x_1918_ = l_List_head_x21___redArg(v___x_1836_, v_scopes_1900_);
lean_dec(v_scopes_1900_);
lean_dec_ref(v___x_1836_);
v_opts_1919_ = lean_ctor_get(v___x_1918_, 1);
lean_inc_ref(v_opts_1919_);
lean_dec(v___x_1918_);
v_hasTrace_1920_ = lean_ctor_get_uint8(v_opts_1919_, sizeof(void*)*1);
if (v_hasTrace_1920_ == 0)
{
lean_dec_ref(v_opts_1919_);
lean_dec(v___x_1917_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_snapshotTasks_1903_);
lean_dec_ref(v_env_1898_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_pos_1840_);
lean_dec_ref(v___f_1839_);
lean_dec_ref(v___f_1838_);
lean_dec_ref(v___f_1837_);
lean_dec(v___x_1831_);
v___y_1870_ = v___y_1894_;
v___y_1871_ = v___y_1889_;
v___y_1872_ = v___y_1890_;
v___y_1873_ = v___y_1897_;
v___y_1874_ = v___y_1906_;
v___y_1875_ = v___y_1892_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1922_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1917_, v_opts_1919_, v___x_1921_);
lean_dec(v___x_1917_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_opts_1919_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_snapshotTasks_1903_);
lean_dec_ref(v_env_1898_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_pos_1840_);
lean_dec_ref(v___f_1839_);
lean_dec_ref(v___f_1838_);
lean_dec_ref(v___f_1837_);
lean_dec(v___x_1831_);
v___y_1870_ = v___y_1894_;
v___y_1871_ = v___y_1889_;
v___y_1872_ = v___y_1890_;
v___y_1873_ = v___y_1897_;
v___y_1874_ = v___y_1906_;
v___y_1875_ = v___y_1892_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_inc_n(v___y_1906_, 3);
v___x_1923_ = lean_task_map(v___f_1837_, v___y_1907_, v___y_1906_, v___x_1832_);
lean_inc_n(v___y_1889_, 3);
lean_inc_n(v___y_1893_, 2);
lean_inc_n(v___y_1891_, 2);
v___x_1924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1924_, 0, v___y_1891_);
lean_ctor_set(v___x_1924_, 1, v___y_1893_);
lean_ctor_set(v___x_1924_, 2, v___y_1889_);
lean_ctor_set(v___x_1924_, 3, v___x_1923_);
v___x_1925_ = lean_task_map(v___f_1838_, v___y_1896_, v___y_1906_, v___x_1832_);
v___x_1926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1891_);
lean_ctor_set(v___x_1926_, 1, v___y_1893_);
lean_ctor_set(v___x_1926_, 2, v___y_1889_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = lean_task_map(v___f_1839_, v___y_1904_, v___y_1906_, v___x_1832_);
v___x_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1891_);
lean_ctor_set(v___x_1928_, 1, v___y_1893_);
lean_ctor_set(v___x_1928_, 2, v___y_1889_);
lean_ctor_set(v___x_1928_, 3, v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(3u);
v___x_1930_ = lean_mk_empty_array_with_capacity(v___x_1929_);
v___x_1931_ = lean_array_push(v___x_1930_, v___x_1924_);
v___x_1932_ = lean_array_push(v___x_1931_, v___x_1926_);
v___x_1933_ = lean_array_push(v___x_1932_, v___x_1928_);
v___x_1934_ = l_Array_append___redArg(v___x_1933_, v_snapshotTasks_1903_);
lean_inc_ref(v___y_1894_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___y_1894_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_box_usize(v___y_1886_);
v___x_1937_ = lean_box(v___x_1832_);
v___x_1938_ = lean_box(v_val_1828_);
v___x_1939_ = lean_box(v___x_1922_);
lean_inc_ref(v___x_1935_);
lean_inc_ref(v___y_1881_);
lean_inc_ref(v_a_1829_);
v___f_1940_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1940_, 0, v_a_1829_);
lean_closure_set(v___f_1940_, 1, v_opts_1919_);
lean_closure_set(v___f_1940_, 2, v___x_1831_);
lean_closure_set(v___f_1940_, 3, v___y_1885_);
lean_closure_set(v___f_1940_, 4, v___y_1888_);
lean_closure_set(v___f_1940_, 5, v___x_1936_);
lean_closure_set(v___f_1940_, 6, v___x_1937_);
lean_closure_set(v___f_1940_, 7, v_env_1898_);
lean_closure_set(v___f_1940_, 8, v___y_1881_);
lean_closure_set(v___f_1940_, 9, v___x_1916_);
lean_closure_set(v___f_1940_, 10, v___y_1887_);
lean_closure_set(v___f_1940_, 11, v___x_1938_);
lean_closure_set(v___f_1940_, 12, v___x_1935_);
lean_closure_set(v___f_1940_, 13, v_pos_1840_);
lean_closure_set(v___f_1940_, 14, v___y_1883_);
lean_closure_set(v___f_1940_, 15, v___y_1884_);
lean_closure_set(v___f_1940_, 16, v___y_1882_);
lean_closure_set(v___f_1940_, 17, v___x_1939_);
v___x_1941_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1935_);
v___x_1942_ = lean_io_bind_task(v___x_1941_, v___f_1940_, v___y_1906_, v_val_1828_);
v___y_1853_ = v___y_1894_;
v___y_1854_ = v___y_1889_;
v___y_1855_ = v___y_1890_;
v___y_1856_ = v___y_1897_;
v_snapshotTasks_1857_ = v_snapshotTasks_1903_;
v___y_1858_ = v___y_1892_;
v_traceTask_1859_ = v___x_1942_;
goto v___jp_1852_;
}
}
}
v___jp_1943_:
{
lean_object* v_env_1967_; lean_object* v_messages_1968_; lean_object* v_scopes_1969_; lean_object* v_infoState_1970_; lean_object* v_traceState_1971_; lean_object* v_snapshotTasks_1972_; 
v_env_1967_ = lean_ctor_get(v___y_1960_, 0);
lean_inc_ref(v_env_1967_);
v_messages_1968_ = lean_ctor_get(v___y_1960_, 1);
lean_inc_ref(v_messages_1968_);
v_scopes_1969_ = lean_ctor_get(v___y_1960_, 2);
lean_inc(v_scopes_1969_);
v_infoState_1970_ = lean_ctor_get(v___y_1960_, 8);
lean_inc_ref(v_infoState_1970_);
v_traceState_1971_ = lean_ctor_get(v___y_1960_, 9);
lean_inc_ref(v_traceState_1971_);
v_snapshotTasks_1972_ = lean_ctor_get(v___y_1960_, 10);
lean_inc_ref(v_snapshotTasks_1972_);
v___y_1881_ = v___y_1944_;
v___y_1882_ = v___y_1945_;
v___y_1883_ = v___y_1946_;
v___y_1884_ = v___y_1948_;
v___y_1885_ = v___y_1947_;
v___y_1886_ = v___y_1949_;
v___y_1887_ = v___y_1950_;
v___y_1888_ = v___y_1951_;
v___y_1889_ = v___y_1952_;
v___y_1890_ = v___y_1953_;
v___y_1891_ = v___y_1954_;
v___y_1892_ = v___y_1955_;
v___y_1893_ = v___y_1956_;
v___y_1894_ = v___y_1957_;
v___y_1895_ = v___y_1958_;
v___y_1896_ = v___y_1959_;
v___y_1897_ = v___y_1960_;
v_env_1898_ = v_env_1967_;
v_messages_1899_ = v_messages_1968_;
v_scopes_1900_ = v_scopes_1969_;
v_infoState_1901_ = v_infoState_1970_;
v_traceState_1902_ = v_traceState_1971_;
v_snapshotTasks_1903_ = v_snapshotTasks_1972_;
v___y_1904_ = v___y_1961_;
v___y_1905_ = v___y_1962_;
v___y_1906_ = v___y_1963_;
v___y_1907_ = v___y_1964_;
v___y_1908_ = v___y_1965_;
v_reportedCmdState_1909_ = v_reportedCmdState_1966_;
goto v___jp_1880_;
}
v___jp_1973_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; uint8_t v___x_1995_; 
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1989_);
lean_ctor_set(v___x_1990_, 1, v_val_1834_);
lean_inc_ref(v___y_1976_);
lean_inc_n(v_pos_1840_, 2);
lean_inc_ref(v_cmds_1825_);
lean_inc(v_fst_1826_);
v___x_1991_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1826_, v_cmds_1825_, v_cmdState_1841_, v_pos_1840_, v___x_1990_, v___y_1976_, v_a_1829_);
v___x_1992_ = lean_box(v_val_1828_);
v___x_1993_ = lean_box(v___x_1832_);
lean_inc_ref(v_a_1829_);
lean_inc(v___y_1983_);
lean_inc_ref(v___x_1836_);
lean_inc_ref(v___x_1991_);
lean_inc_ref(v___y_1974_);
lean_inc_ref(v___y_1977_);
v___f_1994_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_1994_, 0, v___y_1977_);
lean_closure_set(v___f_1994_, 1, v___y_1974_);
lean_closure_set(v___f_1994_, 2, v___x_1992_);
lean_closure_set(v___f_1994_, 3, v_val_1842_);
lean_closure_set(v___f_1994_, 4, v___x_1991_);
lean_closure_set(v___f_1994_, 5, v___x_1836_);
lean_closure_set(v___f_1994_, 6, v___y_1983_);
lean_closure_set(v___f_1994_, 7, v___x_1993_);
lean_closure_set(v___f_1994_, 8, v_a_1829_);
lean_closure_set(v___f_1994_, 9, v_pos_1840_);
lean_closure_set(v___f_1994_, 10, v___x_1843_);
v___x_1995_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1844_, v___x_1845_);
if (v___x_1995_ == 0)
{
lean_inc_ref(v___x_1991_);
lean_inc(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1977_);
lean_inc_ref(v___y_1975_);
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___y_1978_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1982_;
v___y_1951_ = v___y_1983_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1986_;
v___y_1954_ = v___y_1981_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1975_;
v___y_1958_ = v___y_1979_;
v___y_1959_ = v___y_1987_;
v___y_1960_ = v___x_1991_;
v___y_1961_ = v___y_1988_;
v___y_1962_ = v___f_1994_;
v___y_1963_ = v___y_1983_;
v___y_1964_ = v___y_1984_;
v___y_1965_ = v___y_1977_;
v_reportedCmdState_1966_ = v___x_1991_;
goto v___jp_1943_;
}
else
{
uint8_t v___x_1996_; 
lean_inc(v_fst_1826_);
v___x_1996_ = l_Lean_Parser_isTerminalCommand(v_fst_1826_);
if (v___x_1996_ == 0)
{
if (v___x_1995_ == 0)
{
lean_inc_ref(v___x_1991_);
lean_inc(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1977_);
lean_inc_ref(v___y_1975_);
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___y_1978_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1982_;
v___y_1951_ = v___y_1983_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1986_;
v___y_1954_ = v___y_1981_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1975_;
v___y_1958_ = v___y_1979_;
v___y_1959_ = v___y_1987_;
v___y_1960_ = v___x_1991_;
v___y_1961_ = v___y_1988_;
v___y_1962_ = v___f_1994_;
v___y_1963_ = v___y_1983_;
v___y_1964_ = v___y_1984_;
v___y_1965_ = v___y_1977_;
v_reportedCmdState_1966_ = v___x_1991_;
goto v___jp_1943_;
}
else
{
lean_object* v_env_1997_; lean_object* v_messages_1998_; lean_object* v_scopes_1999_; lean_object* v_infoState_2000_; lean_object* v_traceState_2001_; lean_object* v_snapshotTasks_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_env_1997_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_ref_n(v_env_1997_, 2);
v_messages_1998_ = lean_ctor_get(v___x_1991_, 1);
lean_inc_ref(v_messages_1998_);
v_scopes_1999_ = lean_ctor_get(v___x_1991_, 2);
lean_inc(v_scopes_1999_);
v_infoState_2000_ = lean_ctor_get(v___x_1991_, 8);
lean_inc_ref(v_infoState_2000_);
v_traceState_2001_ = lean_ctor_get(v___x_1991_, 9);
lean_inc_ref(v_traceState_2001_);
v_snapshotTasks_2002_ = lean_ctor_get(v___x_1991_, 10);
lean_inc_ref(v_snapshotTasks_2002_);
v___x_2003_ = lean_mk_empty_array_with_capacity(v___y_1978_);
lean_inc_ref(v___x_2003_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_inc_n(v___y_1983_, 4);
v___x_2005_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v___x_2003_);
lean_ctor_set(v___x_2005_, 2, v___y_1983_);
lean_ctor_set(v___x_2005_, 3, v___y_1983_);
lean_ctor_set_usize(v___x_2005_, 4, v___y_1980_);
v___x_2006_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2005_, 2);
v___x_2007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2005_);
lean_ctor_set(v___x_2007_, 2, v___x_2006_);
v___x_2008_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2009_ = l_Lean_Options_empty;
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_mk_empty_array_with_capacity(v___y_1983_);
lean_inc_ref_n(v___x_2011_, 3);
lean_inc_n(v___x_1831_, 2);
v___x_2012_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2012_, 0, v___x_2008_);
lean_ctor_set(v___x_2012_, 1, v___x_2009_);
lean_ctor_set(v___x_2012_, 2, v___x_1831_);
lean_ctor_set(v___x_2012_, 3, v___x_2010_);
lean_ctor_set(v___x_2012_, 4, v___x_2010_);
lean_ctor_set(v___x_2012_, 5, v___x_2011_);
lean_ctor_set(v___x_2012_, 6, v___x_2011_);
lean_ctor_set(v___x_2012_, 7, v___x_2010_);
lean_ctor_set(v___x_2012_, 8, v___x_2010_);
lean_ctor_set(v___x_2012_, 9, v___x_2010_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*10, v_val_1828_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*10 + 1, v_val_1828_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*10 + 2, v_val_1828_);
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v___x_2010_);
v___x_2014_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2015_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2016_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1831_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2018_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
lean_ctor_set(v___x_2018_, 2, v___x_2005_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*3, v___x_1832_);
v___x_2019_ = lean_box(0);
lean_inc_ref(v___y_1974_);
v___x_2020_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2020_, 0, v_env_1997_);
lean_ctor_set(v___x_2020_, 1, v___x_2007_);
lean_ctor_set(v___x_2020_, 2, v___x_2013_);
lean_ctor_set(v___x_2020_, 3, v___x_2006_);
lean_ctor_set(v___x_2020_, 4, v___x_2014_);
lean_ctor_set(v___x_2020_, 5, v___y_1983_);
lean_ctor_set(v___x_2020_, 6, v___x_2015_);
lean_ctor_set(v___x_2020_, 7, v___x_2016_);
lean_ctor_set(v___x_2020_, 8, v___x_2018_);
lean_ctor_set(v___x_2020_, 9, v___y_1974_);
lean_ctor_set(v___x_2020_, 10, v___x_2011_);
lean_ctor_set(v___x_2020_, 11, v___x_2019_);
lean_ctor_set(v___x_2020_, 12, v___x_2011_);
lean_inc(v___y_1982_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1977_);
lean_inc_ref(v___y_1975_);
v___y_1881_ = v___y_1974_;
v___y_1882_ = v___y_1975_;
v___y_1883_ = v___y_1977_;
v___y_1884_ = v___y_1979_;
v___y_1885_ = v___y_1978_;
v___y_1886_ = v___y_1980_;
v___y_1887_ = v___y_1982_;
v___y_1888_ = v___y_1983_;
v___y_1889_ = v___y_1982_;
v___y_1890_ = v___y_1986_;
v___y_1891_ = v___y_1981_;
v___y_1892_ = v___y_1976_;
v___y_1893_ = v___y_1985_;
v___y_1894_ = v___y_1975_;
v___y_1895_ = v___y_1979_;
v___y_1896_ = v___y_1987_;
v___y_1897_ = v___x_1991_;
v_env_1898_ = v_env_1997_;
v_messages_1899_ = v_messages_1998_;
v_scopes_1900_ = v_scopes_1999_;
v_infoState_1901_ = v_infoState_2000_;
v_traceState_1902_ = v_traceState_2001_;
v_snapshotTasks_1903_ = v_snapshotTasks_2002_;
v___y_1904_ = v___y_1988_;
v___y_1905_ = v___f_1994_;
v___y_1906_ = v___y_1983_;
v___y_1907_ = v___y_1984_;
v___y_1908_ = v___y_1977_;
v_reportedCmdState_1909_ = v___x_2020_;
goto v___jp_1880_;
}
}
else
{
lean_inc_ref(v___x_1991_);
lean_inc(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc(v___y_1979_);
lean_inc_ref(v___y_1977_);
lean_inc_ref(v___y_1975_);
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1977_;
v___y_1947_ = v___y_1978_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1982_;
v___y_1951_ = v___y_1983_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1986_;
v___y_1954_ = v___y_1981_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1975_;
v___y_1958_ = v___y_1979_;
v___y_1959_ = v___y_1987_;
v___y_1960_ = v___x_1991_;
v___y_1961_ = v___y_1988_;
v___y_1962_ = v___f_1994_;
v___y_1963_ = v___y_1983_;
v___y_1964_ = v___y_1984_;
v___y_1965_ = v___y_1977_;
v_reportedCmdState_1966_ = v___x_1991_;
goto v___jp_1943_;
}
}
}
v___jp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2023_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1830_);
v___x_2024_ = l_IO_CancelToken_new();
v___x_2025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1831_);
v___x_2026_ = l_Lean_Name_str___override(v___x_1831_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2028_ = l_Lean_Name_str___override(v___x_2026_, v___x_2027_);
v___x_2029_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2030_ = l_Lean_Name_str___override(v___x_2028_, v___x_2029_);
v___x_2031_ = l_Lean_Name_str___override(v___x_2030_, v___x_2027_);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = l_Lean_Name_num___override(v___x_2031_, v___x_2032_);
v___x_2034_ = l_Lean_Name_str___override(v___x_2033_, v___x_2027_);
v___x_2035_ = l_Lean_Name_str___override(v___x_2034_, v___x_2029_);
v___x_2036_ = l_Lean_Name_str___override(v___x_2035_, v___x_2027_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2038_ = l_Lean_Name_str___override(v___x_2036_, v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2040_ = l_Lean_Name_str___override(v___x_2038_, v___x_2039_);
v___x_2041_ = l_Lean_Name_toString(v___x_2040_, v___x_1832_);
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_unsigned_to_nat(32u);
v___x_2044_ = ((size_t)5ULL);
v___x_2045_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2041_, 2);
v___x_2046_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2046_, 0, v___x_2041_);
lean_ctor_set(v___x_2046_, 1, v___x_2023_);
lean_ctor_set(v___x_2046_, 2, v___x_2042_);
lean_ctor_set(v___x_2046_, 3, v___x_2045_);
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*4, v_val_1828_);
v___x_2047_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2048_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2048_, 0, v___x_2041_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_ctor_set(v___x_2048_, 2, v___x_2042_);
lean_ctor_set(v___x_2048_, 3, v___x_2045_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*4, v_val_1828_);
lean_inc(v_fst_1833_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_fst_1833_);
v___x_2050_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2049_);
lean_inc_ref(v___x_2024_);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2024_);
v___x_2052_ = l_IO_Promise_result_x21___redArg(v_val_1834_);
lean_inc_ref(v___x_2052_);
lean_inc(v___x_2050_);
lean_inc_ref_n(v___x_2049_, 3);
v___x_2053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2049_);
lean_ctor_set(v___x_2053_, 1, v___x_2050_);
lean_ctor_set(v___x_2053_, 2, v___x_2051_);
lean_ctor_set(v___x_2053_, 3, v___x_2052_);
v___x_2054_ = l_IO_Promise_result_x21___redArg(v_val_1835_);
lean_inc_ref(v___x_2054_);
lean_inc_n(v___x_1823_, 3);
v___x_2055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2049_);
lean_ctor_set(v___x_2055_, 1, v___x_1823_);
lean_ctor_set(v___x_2055_, 2, v___x_2042_);
lean_ctor_set(v___x_2055_, 3, v___x_2054_);
v___x_2056_ = l_IO_Promise_result_x21___redArg(v_val_1842_);
lean_inc_ref(v___x_2056_);
v___x_2057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2049_);
lean_ctor_set(v___x_2057_, 1, v___x_1823_);
lean_ctor_set(v___x_2057_, 2, v___x_2042_);
lean_ctor_set(v___x_2057_, 3, v___x_2056_);
v___x_2058_ = l_IO_Promise_result_x21___redArg(v_val_1824_);
v___x_2059_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2042_);
lean_ctor_set(v___x_2059_, 1, v___x_1823_);
lean_ctor_set(v___x_2059_, 2, v___x_2042_);
lean_ctor_set(v___x_2059_, 3, v___x_2058_);
lean_inc_ref(v___x_2048_);
v___x_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2048_);
lean_ctor_set(v___x_2060_, 1, v___x_2053_);
lean_ctor_set(v___x_2060_, 2, v___x_2055_);
lean_ctor_set(v___x_2060_, 3, v___x_2057_);
lean_ctor_set(v___x_2060_, 4, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2046_);
lean_ctor_set(v___x_2061_, 1, v_fst_1833_);
lean_ctor_set(v___x_2061_, 2, v_snd_1846_);
lean_ctor_set(v___x_2061_, 3, v___x_2060_);
lean_ctor_set(v___x_2061_, 4, v___y_2022_);
v___x_2062_ = lean_io_promise_resolve(v___x_2061_, v_prom_1847_);
if (lean_obj_tag(v_old_x3f_1848_) == 0)
{
v___y_1974_ = v___x_2045_;
v___y_1975_ = v___x_2048_;
v___y_1976_ = v___x_2024_;
v___y_1977_ = v___x_2041_;
v___y_1978_ = v___x_2043_;
v___y_1979_ = v___x_2042_;
v___y_1980_ = v___x_2044_;
v___y_1981_ = v___x_2049_;
v___y_1982_ = v___x_2042_;
v___y_1983_ = v___x_2032_;
v___y_1984_ = v___x_2052_;
v___y_1985_ = v___x_2050_;
v___y_1986_ = v___x_2042_;
v___y_1987_ = v___x_2054_;
v___y_1988_ = v___x_2056_;
v___y_1989_ = v___x_2042_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_val_2063_ = lean_ctor_get(v_old_x3f_1848_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_old_x3f_1848_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2065_ = v_old_x3f_1848_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v_old_x3f_1848_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_elabSnap_2067_; lean_object* v_stx_2068_; lean_object* v_elabSnap_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v_elabSnap_2067_ = lean_ctor_get(v_val_2063_, 3);
lean_inc_ref(v_elabSnap_2067_);
v_stx_2068_ = lean_ctor_get(v_val_2063_, 1);
lean_inc(v_stx_2068_);
lean_dec(v_val_2063_);
v_elabSnap_2069_ = lean_ctor_get(v_elabSnap_2067_, 1);
lean_inc_ref(v_elabSnap_2069_);
lean_dec_ref(v_elabSnap_2067_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_stx_2068_);
lean_ctor_set(v___x_2070_, 1, v_elabSnap_2069_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2070_);
v___x_2072_ = v___x_2065_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
v___y_1974_ = v___x_2045_;
v___y_1975_ = v___x_2048_;
v___y_1976_ = v___x_2024_;
v___y_1977_ = v___x_2041_;
v___y_1978_ = v___x_2043_;
v___y_1979_ = v___x_2042_;
v___y_1980_ = v___x_2044_;
v___y_1981_ = v___x_2049_;
v___y_1982_ = v___x_2042_;
v___y_1983_ = v___x_2032_;
v___y_1984_ = v___x_2052_;
v___y_1985_ = v___x_2050_;
v___y_1986_ = v___x_2042_;
v___y_1987_ = v___x_2054_;
v___y_1988_ = v___x_2056_;
v___y_1989_ = v___x_2072_;
goto v___jp_1973_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2088_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2090_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_cmds_2091_, lean_object* v_fst_2092_, lean_object* v_fst_2093_, uint8_t v_val_2094_, lean_object* v_a_2095_, lean_object* v_snd_2096_, lean_object* v___x_2097_, uint8_t v___x_2098_, lean_object* v___x_2099_, lean_object* v___f_2100_, lean_object* v___f_2101_, lean_object* v___f_2102_, lean_object* v_pos_2103_, lean_object* v_cmdState_2104_, lean_object* v___x_2105_, lean_object* v_opts_2106_, lean_object* v_prom_2107_, lean_object* v_old_x3f_2108_, lean_object* v_parseCancelTk_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v_snapshotTasks_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v_traceTask_2124_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2148_; lean_object* v___y_2149_; size_t v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v_env_2164_; lean_object* v_messages_2165_; lean_object* v_scopes_2166_; lean_object* v_infoState_2167_; lean_object* v_traceState_2168_; lean_object* v_snapshotTasks_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v_reportedCmdState_2178_; lean_object* v___y_2213_; size_t v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v_reportedCmdState_2237_; lean_object* v___x_2244_; lean_object* v___y_2246_; size_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v_fst_2374_; lean_object* v_snd_2375_; uint8_t v___x_2387_; 
v___x_2111_ = lean_io_promise_new();
v___x_2112_ = lean_io_promise_new();
v___x_2113_ = lean_io_promise_new();
v___x_2114_ = lean_io_promise_new();
v___x_2244_ = l_Lean_internal_cmdlineSnapshots;
v___x_2387_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2106_, v___x_2244_);
if (v___x_2387_ == 0)
{
lean_inc_ref(v_fst_2093_);
lean_inc(v_fst_2092_);
v_fst_2374_ = v_fst_2092_;
v_snd_2375_ = v_fst_2093_;
goto v___jp_2373_;
}
else
{
uint8_t v___x_2388_; 
lean_inc(v_fst_2092_);
v___x_2388_ = l_Lean_Parser_isTerminalCommand(v_fst_2092_);
if (v___x_2388_ == 0)
{
if (v___x_2387_ == 0)
{
lean_inc_ref(v_fst_2093_);
lean_inc(v_fst_2092_);
v_fst_2374_ = v_fst_2092_;
v_snd_2375_ = v_fst_2093_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_box(0);
v___x_2390_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2374_ = v___x_2389_;
v_snd_2375_ = v___x_2390_;
goto v___jp_2373_;
}
}
else
{
lean_inc_ref(v_fst_2093_);
lean_inc(v_fst_2092_);
v_fst_2374_ = v_fst_2092_;
v_snd_2375_ = v_fst_2093_;
goto v___jp_2373_;
}
}
v___jp_2115_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2125_, 0, v___y_2118_);
lean_ctor_set(v___x_2125_, 1, v___y_2121_);
lean_ctor_set(v___x_2125_, 2, v___y_2122_);
lean_ctor_set(v___x_2125_, 3, v_traceTask_2124_);
v___x_2126_ = lean_array_push(v_snapshotTasks_2120_, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___y_2116_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_io_promise_resolve(v___x_2127_, v___x_2114_);
lean_dec(v___x_2114_);
if (lean_obj_tag(v___y_2123_) == 1)
{
lean_object* v_val_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_val_2129_ = lean_ctor_get(v___y_2123_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v___y_2123_, 1);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_array_push(v_cmds_2091_, v_fst_2092_);
v___x_2132_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2130_, v_fst_2093_, v___y_2119_, v_val_2129_, v_val_2094_, v___y_2117_, v___x_2131_, v_a_2095_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; 
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_fst_2093_);
lean_dec(v_fst_2092_);
lean_dec_ref(v_cmds_2091_);
v___x_2133_ = lean_box(0);
return v___x_2133_;
}
}
v___jp_2134_:
{
lean_object* v_snapshotTasks_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_snapshotTasks_2143_ = lean_ctor_get(v___y_2139_, 10);
lean_inc_ref(v_snapshotTasks_2143_);
v___x_2144_ = lean_mk_empty_array_with_capacity(v___y_2137_);
lean_dec(v___y_2137_);
lean_inc_ref(v___y_2135_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___y_2135_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_task_pure(v___x_2145_);
v___y_2116_ = v___y_2135_;
v___y_2117_ = v___y_2136_;
v___y_2118_ = v___y_2138_;
v___y_2119_ = v___y_2139_;
v_snapshotTasks_2120_ = v_snapshotTasks_2143_;
v___y_2121_ = v___y_2140_;
v___y_2122_ = v___y_2141_;
v___y_2123_ = v___y_2142_;
v_traceTask_2124_ = v___x_2146_;
goto v___jp_2115_;
}
v___jp_2147_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_opts_2188_; uint8_t v_hasTrace_2189_; 
v___x_2179_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2165_);
v___x_2180_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2180_, 0, v___y_2170_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
lean_ctor_set(v___x_2180_, 2, v___y_2160_);
lean_ctor_set(v___x_2180_, 3, v_traceState_2168_);
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*4, v_val_2094_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v_reportedCmdState_2178_);
v___x_2182_ = lean_io_promise_resolve(v___x_2181_, v___x_2112_);
lean_dec(v___x_2112_);
v___x_2183_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2167_);
lean_inc(v___y_2161_);
v___x_2184_ = l_BaseIO_chainTask___redArg(v___x_2183_, v___y_2157_, v___y_2161_, v___x_2098_);
v___x_2185_ = l_Lean_inheritedTraceOptions;
v___x_2186_ = lean_st_ref_get(v___x_2185_);
v___x_2187_ = l_List_head_x21___redArg(v___x_2099_, v_scopes_2166_);
lean_dec(v_scopes_2166_);
lean_dec_ref(v___x_2099_);
v_opts_2188_ = lean_ctor_get(v___x_2187_, 1);
lean_inc_ref(v_opts_2188_);
lean_dec(v___x_2187_);
v_hasTrace_2189_ = lean_ctor_get_uint8(v_opts_2188_, sizeof(void*)*1);
if (v_hasTrace_2189_ == 0)
{
lean_dec_ref(v_opts_2188_);
lean_dec(v___x_2186_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v___y_2172_);
lean_dec_ref(v_snapshotTasks_2169_);
lean_dec_ref(v_env_2164_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec(v_pos_2103_);
lean_dec_ref(v___f_2102_);
lean_dec_ref(v___f_2101_);
lean_dec_ref(v___f_2100_);
lean_dec(v___x_2097_);
v___y_2135_ = v___y_2158_;
v___y_2136_ = v___y_2173_;
v___y_2137_ = v___y_2161_;
v___y_2138_ = v___y_2162_;
v___y_2139_ = v___y_2163_;
v___y_2140_ = v___y_2176_;
v___y_2141_ = v___y_2177_;
v___y_2142_ = v___y_2171_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2191_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2186_, v_opts_2188_, v___x_2190_);
lean_dec(v___x_2186_);
if (v___x_2191_ == 0)
{
lean_dec_ref(v_opts_2188_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v___y_2172_);
lean_dec_ref(v_snapshotTasks_2169_);
lean_dec_ref(v_env_2164_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec(v_pos_2103_);
lean_dec_ref(v___f_2102_);
lean_dec_ref(v___f_2101_);
lean_dec_ref(v___f_2100_);
lean_dec(v___x_2097_);
v___y_2135_ = v___y_2158_;
v___y_2136_ = v___y_2173_;
v___y_2137_ = v___y_2161_;
v___y_2138_ = v___y_2162_;
v___y_2139_ = v___y_2163_;
v___y_2140_ = v___y_2176_;
v___y_2141_ = v___y_2177_;
v___y_2142_ = v___y_2171_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_inc_n(v___y_2161_, 3);
v___x_2192_ = lean_task_map(v___f_2100_, v___y_2156_, v___y_2161_, v___x_2098_);
lean_inc_n(v___y_2177_, 3);
lean_inc_n(v___y_2172_, 2);
lean_inc_n(v___y_2174_, 2);
v___x_2193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2193_, 0, v___y_2174_);
lean_ctor_set(v___x_2193_, 1, v___y_2172_);
lean_ctor_set(v___x_2193_, 2, v___y_2177_);
lean_ctor_set(v___x_2193_, 3, v___x_2192_);
v___x_2194_ = lean_task_map(v___f_2101_, v___y_2175_, v___y_2161_, v___x_2098_);
v___x_2195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2195_, 0, v___y_2174_);
lean_ctor_set(v___x_2195_, 1, v___y_2172_);
lean_ctor_set(v___x_2195_, 2, v___y_2177_);
lean_ctor_set(v___x_2195_, 3, v___x_2194_);
v___x_2196_ = lean_task_map(v___f_2102_, v___y_2159_, v___y_2161_, v___x_2098_);
v___x_2197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2174_);
lean_ctor_set(v___x_2197_, 1, v___y_2172_);
lean_ctor_set(v___x_2197_, 2, v___y_2177_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
v___x_2198_ = lean_unsigned_to_nat(3u);
v___x_2199_ = lean_mk_empty_array_with_capacity(v___x_2198_);
v___x_2200_ = lean_array_push(v___x_2199_, v___x_2193_);
v___x_2201_ = lean_array_push(v___x_2200_, v___x_2195_);
v___x_2202_ = lean_array_push(v___x_2201_, v___x_2197_);
v___x_2203_ = l_Array_append___redArg(v___x_2202_, v_snapshotTasks_2169_);
lean_inc_ref(v___y_2158_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___y_2158_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = lean_box_usize(v___y_2150_);
v___x_2206_ = lean_box(v___x_2098_);
v___x_2207_ = lean_box(v_val_2094_);
v___x_2208_ = lean_box(v___x_2191_);
lean_inc_ref(v___x_2204_);
lean_inc_ref(v___y_2151_);
lean_inc_ref(v_a_2095_);
v___f_2209_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2209_, 0, v_a_2095_);
lean_closure_set(v___f_2209_, 1, v_opts_2188_);
lean_closure_set(v___f_2209_, 2, v___x_2097_);
lean_closure_set(v___f_2209_, 3, v___y_2154_);
lean_closure_set(v___f_2209_, 4, v___y_2148_);
lean_closure_set(v___f_2209_, 5, v___x_2205_);
lean_closure_set(v___f_2209_, 6, v___x_2206_);
lean_closure_set(v___f_2209_, 7, v_env_2164_);
lean_closure_set(v___f_2209_, 8, v___y_2151_);
lean_closure_set(v___f_2209_, 9, v___x_2185_);
lean_closure_set(v___f_2209_, 10, v___y_2155_);
lean_closure_set(v___f_2209_, 11, v___x_2207_);
lean_closure_set(v___f_2209_, 12, v___x_2204_);
lean_closure_set(v___f_2209_, 13, v_pos_2103_);
lean_closure_set(v___f_2209_, 14, v___y_2152_);
lean_closure_set(v___f_2209_, 15, v___y_2153_);
lean_closure_set(v___f_2209_, 16, v___y_2149_);
lean_closure_set(v___f_2209_, 17, v___x_2208_);
v___x_2210_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2204_);
v___x_2211_ = lean_io_bind_task(v___x_2210_, v___f_2209_, v___y_2161_, v_val_2094_);
v___y_2116_ = v___y_2158_;
v___y_2117_ = v___y_2173_;
v___y_2118_ = v___y_2162_;
v___y_2119_ = v___y_2163_;
v_snapshotTasks_2120_ = v_snapshotTasks_2169_;
v___y_2121_ = v___y_2176_;
v___y_2122_ = v___y_2177_;
v___y_2123_ = v___y_2171_;
v_traceTask_2124_ = v___x_2211_;
goto v___jp_2115_;
}
}
}
v___jp_2212_:
{
lean_object* v_env_2238_; lean_object* v_messages_2239_; lean_object* v_scopes_2240_; lean_object* v_infoState_2241_; lean_object* v_traceState_2242_; lean_object* v_snapshotTasks_2243_; 
v_env_2238_ = lean_ctor_get(v___y_2228_, 0);
lean_inc_ref(v_env_2238_);
v_messages_2239_ = lean_ctor_get(v___y_2228_, 1);
lean_inc_ref(v_messages_2239_);
v_scopes_2240_ = lean_ctor_get(v___y_2228_, 2);
lean_inc(v_scopes_2240_);
v_infoState_2241_ = lean_ctor_get(v___y_2228_, 8);
lean_inc_ref(v_infoState_2241_);
v_traceState_2242_ = lean_ctor_get(v___y_2228_, 9);
lean_inc_ref(v_traceState_2242_);
v_snapshotTasks_2243_ = lean_ctor_get(v___y_2228_, 10);
lean_inc_ref(v_snapshotTasks_2243_);
v___y_2148_ = v___y_2213_;
v___y_2149_ = v___y_2215_;
v___y_2150_ = v___y_2214_;
v___y_2151_ = v___y_2216_;
v___y_2152_ = v___y_2217_;
v___y_2153_ = v___y_2218_;
v___y_2154_ = v___y_2219_;
v___y_2155_ = v___y_2220_;
v___y_2156_ = v___y_2221_;
v___y_2157_ = v___y_2222_;
v___y_2158_ = v___y_2223_;
v___y_2159_ = v___y_2224_;
v___y_2160_ = v___y_2225_;
v___y_2161_ = v___y_2226_;
v___y_2162_ = v___y_2227_;
v___y_2163_ = v___y_2228_;
v_env_2164_ = v_env_2238_;
v_messages_2165_ = v_messages_2239_;
v_scopes_2166_ = v_scopes_2240_;
v_infoState_2167_ = v_infoState_2241_;
v_traceState_2168_ = v_traceState_2242_;
v_snapshotTasks_2169_ = v_snapshotTasks_2243_;
v___y_2170_ = v___y_2229_;
v___y_2171_ = v___y_2230_;
v___y_2172_ = v___y_2231_;
v___y_2173_ = v___y_2232_;
v___y_2174_ = v___y_2233_;
v___y_2175_ = v___y_2234_;
v___y_2176_ = v___y_2235_;
v___y_2177_ = v___y_2236_;
v_reportedCmdState_2178_ = v_reportedCmdState_2237_;
goto v___jp_2147_;
}
v___jp_2245_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___f_2268_; uint8_t v___x_2269_; 
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___y_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2111_);
lean_inc_ref(v___y_2250_);
lean_inc_n(v_pos_2103_, 2);
lean_inc_ref(v_cmds_2091_);
lean_inc(v_fst_2092_);
v___x_2265_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2092_, v_cmds_2091_, v_cmdState_2104_, v_pos_2103_, v___x_2264_, v___y_2250_, v_a_2095_);
v___x_2266_ = lean_box(v_val_2094_);
v___x_2267_ = lean_box(v___x_2098_);
lean_inc_ref(v_a_2095_);
lean_inc(v___y_2246_);
lean_inc_ref(v___x_2099_);
lean_inc_ref(v___x_2265_);
lean_inc_ref(v___y_2249_);
lean_inc_ref(v___y_2252_);
v___f_2268_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2268_, 0, v___y_2252_);
lean_closure_set(v___f_2268_, 1, v___y_2249_);
lean_closure_set(v___f_2268_, 2, v___x_2266_);
lean_closure_set(v___f_2268_, 3, v___x_2113_);
lean_closure_set(v___f_2268_, 4, v___x_2265_);
lean_closure_set(v___f_2268_, 5, v___x_2099_);
lean_closure_set(v___f_2268_, 6, v___y_2246_);
lean_closure_set(v___f_2268_, 7, v___x_2267_);
lean_closure_set(v___f_2268_, 8, v_a_2095_);
lean_closure_set(v___f_2268_, 9, v_pos_2103_);
lean_closure_set(v___f_2268_, 10, v___x_2105_);
v___x_2269_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2106_, v___x_2244_);
if (v___x_2269_ == 0)
{
lean_inc_ref(v___x_2265_);
lean_inc(v___y_2255_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2246_);
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2252_;
v___y_2218_ = v___y_2253_;
v___y_2219_ = v___y_2254_;
v___y_2220_ = v___y_2255_;
v___y_2221_ = v___y_2251_;
v___y_2222_ = v___f_2268_;
v___y_2223_ = v___y_2248_;
v___y_2224_ = v___y_2258_;
v___y_2225_ = v___y_2253_;
v___y_2226_ = v___y_2246_;
v___y_2227_ = v___y_2259_;
v___y_2228_ = v___x_2265_;
v___y_2229_ = v___y_2252_;
v___y_2230_ = v___y_2260_;
v___y_2231_ = v___y_2257_;
v___y_2232_ = v___y_2250_;
v___y_2233_ = v___y_2256_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2255_;
v_reportedCmdState_2237_ = v___x_2265_;
goto v___jp_2212_;
}
else
{
uint8_t v___x_2270_; 
lean_inc(v_fst_2092_);
v___x_2270_ = l_Lean_Parser_isTerminalCommand(v_fst_2092_);
if (v___x_2270_ == 0)
{
if (v___x_2269_ == 0)
{
lean_inc_ref(v___x_2265_);
lean_inc(v___y_2255_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2246_);
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2252_;
v___y_2218_ = v___y_2253_;
v___y_2219_ = v___y_2254_;
v___y_2220_ = v___y_2255_;
v___y_2221_ = v___y_2251_;
v___y_2222_ = v___f_2268_;
v___y_2223_ = v___y_2248_;
v___y_2224_ = v___y_2258_;
v___y_2225_ = v___y_2253_;
v___y_2226_ = v___y_2246_;
v___y_2227_ = v___y_2259_;
v___y_2228_ = v___x_2265_;
v___y_2229_ = v___y_2252_;
v___y_2230_ = v___y_2260_;
v___y_2231_ = v___y_2257_;
v___y_2232_ = v___y_2250_;
v___y_2233_ = v___y_2256_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2255_;
v_reportedCmdState_2237_ = v___x_2265_;
goto v___jp_2212_;
}
else
{
lean_object* v_env_2271_; lean_object* v_messages_2272_; lean_object* v_scopes_2273_; lean_object* v_infoState_2274_; lean_object* v_traceState_2275_; lean_object* v_snapshotTasks_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_env_2271_ = lean_ctor_get(v___x_2265_, 0);
lean_inc_ref_n(v_env_2271_, 2);
v_messages_2272_ = lean_ctor_get(v___x_2265_, 1);
lean_inc_ref(v_messages_2272_);
v_scopes_2273_ = lean_ctor_get(v___x_2265_, 2);
lean_inc(v_scopes_2273_);
v_infoState_2274_ = lean_ctor_get(v___x_2265_, 8);
lean_inc_ref(v_infoState_2274_);
v_traceState_2275_ = lean_ctor_get(v___x_2265_, 9);
lean_inc_ref(v_traceState_2275_);
v_snapshotTasks_2276_ = lean_ctor_get(v___x_2265_, 10);
lean_inc_ref(v_snapshotTasks_2276_);
v___x_2277_ = lean_mk_empty_array_with_capacity(v___y_2254_);
lean_inc_ref(v___x_2277_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_inc_n(v___y_2246_, 4);
v___x_2279_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v___x_2277_);
lean_ctor_set(v___x_2279_, 2, v___y_2246_);
lean_ctor_set(v___x_2279_, 3, v___y_2246_);
lean_ctor_set_usize(v___x_2279_, 4, v___y_2247_);
v___x_2280_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2279_, 2);
v___x_2281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2279_);
lean_ctor_set(v___x_2281_, 2, v___x_2280_);
v___x_2282_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2283_ = l_Lean_Options_empty;
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_mk_empty_array_with_capacity(v___y_2246_);
lean_inc_ref_n(v___x_2285_, 3);
lean_inc_n(v___x_2097_, 2);
v___x_2286_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2286_, 0, v___x_2282_);
lean_ctor_set(v___x_2286_, 1, v___x_2283_);
lean_ctor_set(v___x_2286_, 2, v___x_2097_);
lean_ctor_set(v___x_2286_, 3, v___x_2284_);
lean_ctor_set(v___x_2286_, 4, v___x_2284_);
lean_ctor_set(v___x_2286_, 5, v___x_2285_);
lean_ctor_set(v___x_2286_, 6, v___x_2285_);
lean_ctor_set(v___x_2286_, 7, v___x_2284_);
lean_ctor_set(v___x_2286_, 8, v___x_2284_);
lean_ctor_set(v___x_2286_, 9, v___x_2284_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*10, v_val_2094_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*10 + 1, v_val_2094_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*10 + 2, v_val_2094_);
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___x_2284_);
v___x_2288_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2289_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2290_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2097_);
v___x_2291_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2292_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
lean_ctor_set(v___x_2292_, 2, v___x_2279_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*3, v___x_2098_);
v___x_2293_ = lean_box(0);
lean_inc_ref(v___y_2249_);
v___x_2294_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2294_, 0, v_env_2271_);
lean_ctor_set(v___x_2294_, 1, v___x_2281_);
lean_ctor_set(v___x_2294_, 2, v___x_2287_);
lean_ctor_set(v___x_2294_, 3, v___x_2280_);
lean_ctor_set(v___x_2294_, 4, v___x_2288_);
lean_ctor_set(v___x_2294_, 5, v___y_2246_);
lean_ctor_set(v___x_2294_, 6, v___x_2289_);
lean_ctor_set(v___x_2294_, 7, v___x_2290_);
lean_ctor_set(v___x_2294_, 8, v___x_2292_);
lean_ctor_set(v___x_2294_, 9, v___y_2249_);
lean_ctor_set(v___x_2294_, 10, v___x_2285_);
lean_ctor_set(v___x_2294_, 11, v___x_2293_);
lean_ctor_set(v___x_2294_, 12, v___x_2285_);
lean_inc(v___y_2255_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v___y_2248_);
v___y_2148_ = v___y_2246_;
v___y_2149_ = v___y_2248_;
v___y_2150_ = v___y_2247_;
v___y_2151_ = v___y_2249_;
v___y_2152_ = v___y_2252_;
v___y_2153_ = v___y_2253_;
v___y_2154_ = v___y_2254_;
v___y_2155_ = v___y_2255_;
v___y_2156_ = v___y_2251_;
v___y_2157_ = v___f_2268_;
v___y_2158_ = v___y_2248_;
v___y_2159_ = v___y_2258_;
v___y_2160_ = v___y_2253_;
v___y_2161_ = v___y_2246_;
v___y_2162_ = v___y_2259_;
v___y_2163_ = v___x_2265_;
v_env_2164_ = v_env_2271_;
v_messages_2165_ = v_messages_2272_;
v_scopes_2166_ = v_scopes_2273_;
v_infoState_2167_ = v_infoState_2274_;
v_traceState_2168_ = v_traceState_2275_;
v_snapshotTasks_2169_ = v_snapshotTasks_2276_;
v___y_2170_ = v___y_2252_;
v___y_2171_ = v___y_2260_;
v___y_2172_ = v___y_2257_;
v___y_2173_ = v___y_2250_;
v___y_2174_ = v___y_2256_;
v___y_2175_ = v___y_2261_;
v___y_2176_ = v___y_2262_;
v___y_2177_ = v___y_2255_;
v_reportedCmdState_2178_ = v___x_2294_;
goto v___jp_2147_;
}
}
else
{
lean_inc_ref(v___x_2265_);
lean_inc(v___y_2255_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2246_);
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2252_;
v___y_2218_ = v___y_2253_;
v___y_2219_ = v___y_2254_;
v___y_2220_ = v___y_2255_;
v___y_2221_ = v___y_2251_;
v___y_2222_ = v___f_2268_;
v___y_2223_ = v___y_2248_;
v___y_2224_ = v___y_2258_;
v___y_2225_ = v___y_2253_;
v___y_2226_ = v___y_2246_;
v___y_2227_ = v___y_2259_;
v___y_2228_ = v___x_2265_;
v___y_2229_ = v___y_2252_;
v___y_2230_ = v___y_2260_;
v___y_2231_ = v___y_2257_;
v___y_2232_ = v___y_2250_;
v___y_2233_ = v___y_2256_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2255_;
v_reportedCmdState_2237_ = v___x_2265_;
goto v___jp_2212_;
}
}
}
v___jp_2295_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2301_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2096_);
v___x_2302_ = l_IO_CancelToken_new();
v___x_2303_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2097_);
v___x_2304_ = l_Lean_Name_str___override(v___x_2097_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2306_ = l_Lean_Name_str___override(v___x_2304_, v___x_2305_);
v___x_2307_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2308_ = l_Lean_Name_str___override(v___x_2306_, v___x_2307_);
v___x_2309_ = l_Lean_Name_str___override(v___x_2308_, v___x_2305_);
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = l_Lean_Name_num___override(v___x_2309_, v___x_2310_);
v___x_2312_ = l_Lean_Name_str___override(v___x_2311_, v___x_2305_);
v___x_2313_ = l_Lean_Name_str___override(v___x_2312_, v___x_2307_);
v___x_2314_ = l_Lean_Name_str___override(v___x_2313_, v___x_2305_);
v___x_2315_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2316_ = l_Lean_Name_str___override(v___x_2314_, v___x_2315_);
v___x_2317_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2318_ = l_Lean_Name_str___override(v___x_2316_, v___x_2317_);
v___x_2319_ = l_Lean_Name_toString(v___x_2318_, v___x_2098_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_unsigned_to_nat(32u);
v___x_2322_ = lean_mk_empty_array_with_capacity(v___x_2321_);
lean_dec_ref(v___x_2322_);
v___x_2323_ = ((size_t)5ULL);
v___x_2324_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2319_, 2);
v___x_2325_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2325_, 0, v___x_2319_);
lean_ctor_set(v___x_2325_, 1, v___x_2301_);
lean_ctor_set(v___x_2325_, 2, v___x_2320_);
lean_ctor_set(v___x_2325_, 3, v___x_2324_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*4, v_val_2094_);
v___x_2326_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2327_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2327_, 0, v___x_2319_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
lean_ctor_set(v___x_2327_, 2, v___x_2320_);
lean_ctor_set(v___x_2327_, 3, v___x_2324_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*4, v_val_2094_);
lean_inc(v___y_2296_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___y_2296_);
v___x_2329_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2328_);
lean_inc_ref(v___x_2302_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2302_);
v___x_2331_ = l_IO_Promise_result_x21___redArg(v___x_2111_);
lean_inc_ref(v___x_2331_);
lean_inc(v___x_2329_);
lean_inc_ref_n(v___x_2328_, 3);
v___x_2332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2328_);
lean_ctor_set(v___x_2332_, 1, v___x_2329_);
lean_ctor_set(v___x_2332_, 2, v___x_2330_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
v___x_2333_ = l_IO_Promise_result_x21___redArg(v___x_2112_);
lean_inc_ref(v___x_2333_);
lean_inc_n(v___y_2297_, 3);
v___x_2334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2328_);
lean_ctor_set(v___x_2334_, 1, v___y_2297_);
lean_ctor_set(v___x_2334_, 2, v___x_2320_);
lean_ctor_set(v___x_2334_, 3, v___x_2333_);
v___x_2335_ = l_IO_Promise_result_x21___redArg(v___x_2113_);
lean_inc_ref(v___x_2335_);
v___x_2336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2328_);
lean_ctor_set(v___x_2336_, 1, v___y_2297_);
lean_ctor_set(v___x_2336_, 2, v___x_2320_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
v___x_2337_ = l_IO_Promise_result_x21___redArg(v___x_2114_);
v___x_2338_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2320_);
lean_ctor_set(v___x_2338_, 1, v___y_2297_);
lean_ctor_set(v___x_2338_, 2, v___x_2320_);
lean_ctor_set(v___x_2338_, 3, v___x_2337_);
lean_inc_ref(v___x_2327_);
v___x_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2327_);
lean_ctor_set(v___x_2339_, 1, v___x_2332_);
lean_ctor_set(v___x_2339_, 2, v___x_2334_);
lean_ctor_set(v___x_2339_, 3, v___x_2336_);
lean_ctor_set(v___x_2339_, 4, v___x_2338_);
v___x_2340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2325_);
lean_ctor_set(v___x_2340_, 1, v___y_2296_);
lean_ctor_set(v___x_2340_, 2, v___y_2299_);
lean_ctor_set(v___x_2340_, 3, v___x_2339_);
lean_ctor_set(v___x_2340_, 4, v___y_2300_);
v___x_2341_ = lean_io_promise_resolve(v___x_2340_, v_prom_2107_);
if (lean_obj_tag(v_old_x3f_2108_) == 0)
{
v___y_2246_ = v___x_2310_;
v___y_2247_ = v___x_2323_;
v___y_2248_ = v___x_2327_;
v___y_2249_ = v___x_2324_;
v___y_2250_ = v___x_2302_;
v___y_2251_ = v___x_2331_;
v___y_2252_ = v___x_2319_;
v___y_2253_ = v___x_2320_;
v___y_2254_ = v___x_2321_;
v___y_2255_ = v___x_2320_;
v___y_2256_ = v___x_2328_;
v___y_2257_ = v___x_2329_;
v___y_2258_ = v___x_2335_;
v___y_2259_ = v___x_2320_;
v___y_2260_ = v___y_2298_;
v___y_2261_ = v___x_2333_;
v___y_2262_ = v___y_2297_;
v___y_2263_ = v___x_2320_;
goto v___jp_2245_;
}
else
{
lean_object* v_val_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2353_; 
v_val_2342_ = lean_ctor_get(v_old_x3f_2108_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_old_x3f_2108_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2344_ = v_old_x3f_2108_;
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_val_2342_);
lean_dec(v_old_x3f_2108_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2353_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_elabSnap_2346_; lean_object* v_stx_2347_; lean_object* v_elabSnap_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v_elabSnap_2346_ = lean_ctor_get(v_val_2342_, 3);
lean_inc_ref(v_elabSnap_2346_);
v_stx_2347_ = lean_ctor_get(v_val_2342_, 1);
lean_inc(v_stx_2347_);
lean_dec(v_val_2342_);
v_elabSnap_2348_ = lean_ctor_get(v_elabSnap_2346_, 1);
lean_inc_ref(v_elabSnap_2348_);
lean_dec_ref(v_elabSnap_2346_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_stx_2347_);
lean_ctor_set(v___x_2349_, 1, v_elabSnap_2348_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2349_);
v___x_2351_ = v___x_2344_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
v___y_2246_ = v___x_2310_;
v___y_2247_ = v___x_2323_;
v___y_2248_ = v___x_2327_;
v___y_2249_ = v___x_2324_;
v___y_2250_ = v___x_2302_;
v___y_2251_ = v___x_2331_;
v___y_2252_ = v___x_2319_;
v___y_2253_ = v___x_2320_;
v___y_2254_ = v___x_2321_;
v___y_2255_ = v___x_2320_;
v___y_2256_ = v___x_2328_;
v___y_2257_ = v___x_2329_;
v___y_2258_ = v___x_2335_;
v___y_2259_ = v___x_2320_;
v___y_2260_ = v___y_2298_;
v___y_2261_ = v___x_2333_;
v___y_2262_ = v___y_2297_;
v___y_2263_ = v___x_2351_;
goto v___jp_2245_;
}
}
}
}
v___jp_2354_:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2357_);
lean_inc(v_fst_2092_);
v___x_2359_ = l_Lean_Parser_isTerminalCommand(v_fst_2092_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v_toProcessingContext_2361_; lean_object* v_pos_2362_; lean_object* v_endPos_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2360_ = lean_io_promise_new();
v_toProcessingContext_2361_ = lean_ctor_get(v_a_2095_, 0);
v_pos_2362_ = lean_ctor_get(v_fst_2093_, 0);
v_endPos_2363_ = lean_ctor_get(v_toProcessingContext_2361_, 3);
lean_inc(v___x_2360_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2360_);
v___x_2365_ = lean_box(0);
lean_inc(v_endPos_2363_);
lean_inc(v_pos_2362_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_pos_2362_);
lean_ctor_set(v___x_2366_, 1, v_endPos_2363_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_parseCancelTk_2109_);
v___x_2369_ = l_IO_Promise_result_x21___redArg(v___x_2360_);
lean_dec(v___x_2360_);
v___x_2370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2365_);
lean_ctor_set(v___x_2370_, 1, v___x_2367_);
lean_ctor_set(v___x_2370_, 2, v___x_2368_);
lean_ctor_set(v___x_2370_, 3, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
v___y_2296_ = v___y_2355_;
v___y_2297_ = v___x_2358_;
v___y_2298_ = v___x_2364_;
v___y_2299_ = v___y_2356_;
v___y_2300_ = v___x_2371_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2372_; 
lean_dec_ref(v_parseCancelTk_2109_);
v___x_2372_ = lean_box(0);
v___y_2296_ = v___y_2355_;
v___y_2297_ = v___x_2358_;
v___y_2298_ = v___x_2372_;
v___y_2299_ = v___y_2356_;
v___y_2300_ = v___x_2372_;
goto v___jp_2295_;
}
}
v___jp_2373_:
{
lean_object* v___x_2376_; 
lean_inc(v_fst_2092_);
v___x_2376_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2092_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_box(0);
v___y_2355_ = v_fst_2374_;
v___y_2356_ = v_snd_2375_;
v___y_2357_ = v___x_2377_;
goto v___jp_2354_;
}
else
{
lean_object* v_val_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2386_; 
v_val_2378_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2380_ = v___x_2376_;
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_val_2378_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_inc(v_val_2378_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_val_2378_);
lean_ctor_set(v___x_2382_, 1, v_val_2378_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2382_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v___y_2355_ = v_fst_2374_;
v___y_2356_ = v_snd_2375_;
v___y_2357_ = v___x_2384_;
goto v___jp_2354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_cmds_2391_ = _args[0];
lean_object* v_fst_2392_ = _args[1];
lean_object* v_fst_2393_ = _args[2];
lean_object* v_val_2394_ = _args[3];
lean_object* v_a_2395_ = _args[4];
lean_object* v_snd_2396_ = _args[5];
lean_object* v___x_2397_ = _args[6];
lean_object* v___x_2398_ = _args[7];
lean_object* v___x_2399_ = _args[8];
lean_object* v___f_2400_ = _args[9];
lean_object* v___f_2401_ = _args[10];
lean_object* v___f_2402_ = _args[11];
lean_object* v_pos_2403_ = _args[12];
lean_object* v_cmdState_2404_ = _args[13];
lean_object* v___x_2405_ = _args[14];
lean_object* v_opts_2406_ = _args[15];
lean_object* v_prom_2407_ = _args[16];
lean_object* v_old_x3f_2408_ = _args[17];
lean_object* v_parseCancelTk_2409_ = _args[18];
lean_object* v___y_2410_ = _args[19];
_start:
{
uint8_t v_val_36347__boxed_2411_; uint8_t v___x_36350__boxed_2412_; lean_object* v_res_2413_; 
v_val_36347__boxed_2411_ = lean_unbox(v_val_2394_);
v___x_36350__boxed_2412_ = lean_unbox(v___x_2398_);
v_res_2413_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_cmds_2391_, v_fst_2392_, v_fst_2393_, v_val_36347__boxed_2411_, v_a_2395_, v_snd_2396_, v___x_2397_, v___x_36350__boxed_2412_, v___x_2399_, v___f_2400_, v___f_2401_, v___f_2402_, v_pos_2403_, v_cmdState_2404_, v___x_2405_, v_opts_2406_, v_prom_2407_, v_old_x3f_2408_, v_parseCancelTk_2409_);
lean_dec(v_prom_2407_);
lean_dec_ref(v_opts_2406_);
lean_dec_ref(v_a_2395_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2416_, lean_object* v_parserState_2417_, lean_object* v_cmdState_2418_, lean_object* v_prom_2419_, uint8_t v_sync_2420_, lean_object* v_parseCancelTk_2421_, lean_object* v_cmds_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___y_2428_; lean_object* v_toSnapshot_2430_; lean_object* v_stx_2431_; lean_object* v_parserState_2432_; lean_object* v_elabSnap_2433_; lean_object* v_val_2434_; lean_object* v_newParserState_2435_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; uint8_t v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; uint8_t v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v_fst_2511_; lean_object* v_snd_2512_; lean_object* v___y_2525_; uint8_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2561_; uint8_t v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___x_2606_; 
v___f_2466_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2467_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2468_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2469_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2470_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2606_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
if (lean_obj_tag(v_old_x3f_2416_) == 1)
{
lean_object* v_val_2639_; lean_object* v_nextCmdSnap_x3f_2640_; 
v_val_2639_ = lean_ctor_get(v_old_x3f_2416_, 0);
v_nextCmdSnap_x3f_2640_ = lean_ctor_get(v_val_2639_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2640_) == 0)
{
goto v___jp_2607_;
}
else
{
lean_object* v_toSnapshot_2641_; lean_object* v_stx_2642_; lean_object* v_parserState_2643_; lean_object* v_elabSnap_2644_; lean_object* v_val_2645_; lean_object* v___x_2646_; 
v_toSnapshot_2641_ = lean_ctor_get(v_val_2639_, 0);
v_stx_2642_ = lean_ctor_get(v_val_2639_, 1);
v_parserState_2643_ = lean_ctor_get(v_val_2639_, 2);
v_elabSnap_2644_ = lean_ctor_get(v_val_2639_, 3);
v_val_2645_ = lean_ctor_get(v_nextCmdSnap_x3f_2640_, 0);
lean_inc(v_val_2645_);
v___x_2646_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2645_);
if (lean_obj_tag(v___x_2646_) == 1)
{
lean_object* v_val_2647_; lean_object* v_nextCmdSnap_x3f_2648_; 
v_val_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_val_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v_nextCmdSnap_x3f_2648_ = lean_ctor_get(v_val_2647_, 4);
lean_inc(v_nextCmdSnap_x3f_2648_);
lean_dec(v_val_2647_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2648_) == 0)
{
goto v___jp_2607_;
}
else
{
lean_object* v_val_2649_; lean_object* v___x_2650_; 
v_val_2649_ = lean_ctor_get(v_nextCmdSnap_x3f_2648_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2648_, 1);
v___x_2650_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2649_);
if (lean_obj_tag(v___x_2650_) == 1)
{
lean_object* v_val_2651_; lean_object* v_parserState_2652_; lean_object* v_pos_2653_; uint8_t v___x_2654_; 
v_val_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_parserState_2652_ = lean_ctor_get(v_val_2651_, 2);
lean_inc_ref(v_parserState_2652_);
lean_dec(v_val_2651_);
v_pos_2653_ = lean_ctor_get(v_parserState_2652_, 0);
lean_inc(v_pos_2653_);
lean_dec_ref(v_parserState_2652_);
v___x_2654_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2653_, v_a_2423_);
lean_dec(v_pos_2653_);
if (v___x_2654_ == 0)
{
goto v___jp_2607_;
}
else
{
lean_inc(v_val_2645_);
lean_inc_ref(v_elabSnap_2644_);
lean_inc_ref_n(v_parserState_2643_, 2);
lean_inc(v_stx_2642_);
lean_inc_ref(v_toSnapshot_2641_);
lean_dec_ref_known(v_old_x3f_2416_, 1);
lean_dec_ref(v_parseCancelTk_2421_);
lean_dec_ref(v_cmdState_2418_);
lean_dec_ref(v_parserState_2417_);
v_toSnapshot_2430_ = v_toSnapshot_2641_;
v_stx_2431_ = v_stx_2642_;
v_parserState_2432_ = v_parserState_2643_;
v_elabSnap_2433_ = v_elabSnap_2644_;
v_val_2434_ = v_val_2645_;
v_newParserState_2435_ = v_parserState_2643_;
goto v___jp_2429_;
}
}
else
{
lean_dec(v___x_2650_);
goto v___jp_2607_;
}
}
}
else
{
lean_dec(v___x_2646_);
goto v___jp_2607_;
}
}
}
else
{
goto v___jp_2607_;
}
v___jp_2425_:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
v___jp_2427_:
{
goto v___jp_2425_;
}
v___jp_2429_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_resultSnap_2438_; lean_object* v_task_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2462_; 
v___x_2436_ = lean_io_promise_new();
v___x_2437_ = l_IO_CancelToken_new();
v_resultSnap_2438_ = lean_ctor_get(v_elabSnap_2433_, 2);
lean_inc_ref(v_resultSnap_2438_);
v_task_2439_ = lean_ctor_get(v_resultSnap_2438_, 3);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_resultSnap_2438_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; lean_object* v_unused_2464_; lean_object* v_unused_2465_; 
v_unused_2463_ = lean_ctor_get(v_resultSnap_2438_, 2);
lean_dec(v_unused_2463_);
v_unused_2464_ = lean_ctor_get(v_resultSnap_2438_, 1);
lean_dec(v_unused_2464_);
v_unused_2465_ = lean_ctor_get(v_resultSnap_2438_, 0);
lean_dec(v_unused_2465_);
v___x_2441_ = v_resultSnap_2438_;
v_isShared_2442_ = v_isSharedCheck_2462_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_task_2439_);
lean_dec(v_resultSnap_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2462_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v_toProcessingContext_2448_; lean_object* v_pos_2449_; lean_object* v_endPos_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2443_ = lean_box(v_sync_2420_);
lean_inc_ref(v_a_2423_);
lean_inc_ref(v___x_2437_);
lean_inc(v___x_2436_);
lean_inc_ref(v_newParserState_2435_);
lean_inc(v_stx_2431_);
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2444_, 0, v_val_2434_);
lean_closure_set(v___f_2444_, 1, v_cmds_2422_);
lean_closure_set(v___f_2444_, 2, v_stx_2431_);
lean_closure_set(v___f_2444_, 3, v_newParserState_2435_);
lean_closure_set(v___f_2444_, 4, v___x_2436_);
lean_closure_set(v___f_2444_, 5, v___x_2443_);
lean_closure_set(v___f_2444_, 6, v___x_2437_);
lean_closure_set(v___f_2444_, 7, v_a_2423_);
v___x_2445_ = lean_unsigned_to_nat(0u);
v___x_2446_ = 1;
v___x_2447_ = l_BaseIO_chainTask___redArg(v_task_2439_, v___f_2444_, v___x_2445_, v___x_2446_);
v_toProcessingContext_2448_ = lean_ctor_get(v_a_2423_, 0);
v_pos_2449_ = lean_ctor_get(v_newParserState_2435_, 0);
lean_inc(v_pos_2449_);
lean_dec_ref(v_newParserState_2435_);
v_endPos_2450_ = lean_ctor_get(v_toProcessingContext_2448_, 3);
v___x_2451_ = lean_box(0);
lean_inc(v_endPos_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_pos_2449_);
lean_ctor_set(v___x_2452_, 1, v_endPos_2450_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2437_);
v___x_2455_ = l_IO_Promise_result_x21___redArg(v___x_2436_);
lean_dec(v___x_2436_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 3, v___x_2455_);
lean_ctor_set(v___x_2441_, 2, v___x_2454_);
lean_ctor_set(v___x_2441_, 1, v___x_2453_);
lean_ctor_set(v___x_2441_, 0, v___x_2451_);
v___x_2457_ = v___x_2441_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v___x_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2459_, 0, v_toSnapshot_2430_);
lean_ctor_set(v___x_2459_, 1, v_stx_2431_);
lean_ctor_set(v___x_2459_, 2, v_parserState_2432_);
lean_ctor_set(v___x_2459_, 3, v_elabSnap_2433_);
lean_ctor_set(v___x_2459_, 4, v___x_2458_);
v___x_2460_ = lean_io_promise_resolve(v___x_2459_, v_prom_2419_);
lean_dec(v_prom_2419_);
return v___x_2460_;
}
}
}
v___jp_2471_:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2488_);
v___x_2490_ = l_Lean_Parser_isTerminalCommand(v___y_2483_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_io_promise_new();
v___x_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
v___x_2493_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2489_, v___y_2481_, v_cmds_2422_, v___y_2473_, v___y_2472_, v___y_2479_, v_a_2423_, v___y_2480_, v___y_2486_, v___y_2475_, v___y_2477_, v___y_2487_, v___y_2482_, v___x_2469_, v___f_2468_, v___f_2467_, v___f_2466_, v___y_2476_, v_cmdState_2418_, v___y_2474_, v___x_2470_, v___y_2484_, v___y_2485_, v___y_2478_, v_prom_2419_, v_old_x3f_2416_, v_parseCancelTk_2421_, v___x_2492_);
lean_dec(v_prom_2419_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
v___y_2428_ = v___x_2493_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_box(0);
v___x_2495_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2489_, v___y_2481_, v_cmds_2422_, v___y_2473_, v___y_2472_, v___y_2479_, v_a_2423_, v___y_2480_, v___y_2486_, v___y_2475_, v___y_2477_, v___y_2487_, v___y_2482_, v___x_2469_, v___f_2468_, v___f_2467_, v___f_2466_, v___y_2476_, v_cmdState_2418_, v___y_2474_, v___x_2470_, v___y_2484_, v___y_2485_, v___y_2478_, v_prom_2419_, v_old_x3f_2416_, v_parseCancelTk_2421_, v___x_2494_);
lean_dec(v_prom_2419_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
v___y_2428_ = v___x_2495_;
goto v___jp_2427_;
}
}
v___jp_2496_:
{
lean_object* v___x_2513_; 
lean_inc(v___y_2510_);
v___x_2513_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2510_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_box(0);
v___y_2472_ = v___y_2497_;
v___y_2473_ = v___y_2498_;
v___y_2474_ = v___y_2499_;
v___y_2475_ = v___y_2500_;
v___y_2476_ = v___y_2501_;
v___y_2477_ = v_fst_2511_;
v___y_2478_ = v_snd_2512_;
v___y_2479_ = v___y_2502_;
v___y_2480_ = v___y_2503_;
v___y_2481_ = v___y_2504_;
v___y_2482_ = v___y_2505_;
v___y_2483_ = v___y_2510_;
v___y_2484_ = v___y_2506_;
v___y_2485_ = v___y_2507_;
v___y_2486_ = v___y_2508_;
v___y_2487_ = v___y_2509_;
v___y_2488_ = v___x_2514_;
goto v___jp_2471_;
}
else
{
lean_object* v_val_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2523_; 
v_val_2515_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2517_ = v___x_2513_;
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_val_2515_);
lean_dec(v___x_2513_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc(v_val_2515_);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_val_2515_);
lean_ctor_set(v___x_2519_, 1, v_val_2515_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
v___y_2472_ = v___y_2497_;
v___y_2473_ = v___y_2498_;
v___y_2474_ = v___y_2499_;
v___y_2475_ = v___y_2500_;
v___y_2476_ = v___y_2501_;
v___y_2477_ = v_fst_2511_;
v___y_2478_ = v_snd_2512_;
v___y_2479_ = v___y_2502_;
v___y_2480_ = v___y_2503_;
v___y_2481_ = v___y_2504_;
v___y_2482_ = v___y_2505_;
v___y_2483_ = v___y_2510_;
v___y_2484_ = v___y_2506_;
v___y_2485_ = v___y_2507_;
v___y_2486_ = v___y_2508_;
v___y_2487_ = v___y_2509_;
v___y_2488_ = v___x_2521_;
goto v___jp_2471_;
}
}
}
}
v___jp_2524_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2529_ = l_Lean_Name_str___override(v___y_2527_, v___x_2528_);
v___x_2530_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2531_ = l_Lean_Name_str___override(v___x_2529_, v___x_2530_);
v___x_2532_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2533_ = l_Lean_Name_str___override(v___x_2531_, v___x_2532_);
v___x_2534_ = l_Lean_Name_str___override(v___x_2533_, v___x_2530_);
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = l_Lean_Name_num___override(v___x_2534_, v___x_2535_);
v___x_2537_ = l_Lean_Name_str___override(v___x_2536_, v___x_2530_);
v___x_2538_ = l_Lean_Name_str___override(v___x_2537_, v___x_2532_);
v___x_2539_ = l_Lean_Name_str___override(v___x_2538_, v___x_2530_);
v___x_2540_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2541_ = l_Lean_Name_str___override(v___x_2539_, v___x_2540_);
v___x_2542_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4));
v___x_2543_ = l_Lean_Name_str___override(v___x_2541_, v___x_2542_);
v___x_2544_ = l_Lean_Name_toString(v___x_2543_, v___y_2526_);
v___x_2545_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2548_ = 0;
v___x_2549_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2549_, 0, v___x_2544_);
lean_ctor_set(v___x_2549_, 1, v___x_2545_);
lean_ctor_set(v___x_2549_, 2, v___x_2546_);
lean_ctor_set(v___x_2549_, 3, v___x_2547_);
lean_ctor_set_uint8(v___x_2549_, sizeof(void*)*4, v___x_2548_);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
lean_inc_ref_n(v___x_2549_, 3);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2549_);
lean_ctor_set(v___x_2552_, 1, v_cmdState_2418_);
v___x_2553_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2546_, v___x_2552_);
v___x_2554_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2546_, v___x_2549_);
v___x_2555_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4);
v___x_2556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2549_);
lean_ctor_set(v___x_2556_, 1, v___x_2551_);
lean_ctor_set(v___x_2556_, 2, v___x_2553_);
lean_ctor_set(v___x_2556_, 3, v___x_2554_);
lean_ctor_set(v___x_2556_, 4, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2549_);
lean_ctor_set(v___x_2557_, 1, v___x_2550_);
lean_ctor_set(v___x_2557_, 2, v___y_2525_);
lean_ctor_set(v___x_2557_, 3, v___x_2556_);
lean_ctor_set(v___x_2557_, 4, v___x_2546_);
v___x_2558_ = lean_io_promise_resolve(v___x_2557_, v_prom_2419_);
lean_dec(v_prom_2419_);
v___x_2559_ = lean_box(0);
return v___x_2559_;
}
v___jp_2560_:
{
v___y_2525_ = v___y_2561_;
v___y_2526_ = v___y_2562_;
v___y_2527_ = v___y_2563_;
goto v___jp_2524_;
}
v___jp_2565_:
{
uint8_t v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = l_IO_CancelToken_isSet(v_parseCancelTk_2421_);
v___x_2577_ = 1;
if (v___x_2576_ == 0)
{
lean_dec(v___y_2575_);
if (v_sync_2420_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2578_ = lean_io_promise_new();
v___x_2579_ = lean_io_promise_new();
v___x_2580_ = lean_io_promise_new();
v___x_2581_ = lean_io_promise_new();
v___x_2582_ = l_Lean_internal_cmdlineSnapshots;
v___x_2583_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2574_, v___x_2582_);
lean_dec_ref(v___y_2574_);
if (v___x_2583_ == 0)
{
lean_inc(v___y_2573_);
v___y_2497_ = v___y_2566_;
v___y_2498_ = v___y_2567_;
v___y_2499_ = v___x_2580_;
v___y_2500_ = v___x_2577_;
v___y_2501_ = v___y_2570_;
v___y_2502_ = v___x_2576_;
v___y_2503_ = v___y_2571_;
v___y_2504_ = v___x_2581_;
v___y_2505_ = v___x_2579_;
v___y_2506_ = v___y_2568_;
v___y_2507_ = v___x_2582_;
v___y_2508_ = v___y_2569_;
v___y_2509_ = v___x_2578_;
v___y_2510_ = v___y_2573_;
v_fst_2511_ = v___y_2573_;
v_snd_2512_ = v___y_2572_;
goto v___jp_2496_;
}
else
{
uint8_t v___x_2584_; 
lean_inc(v___y_2573_);
v___x_2584_ = l_Lean_Parser_isTerminalCommand(v___y_2573_);
if (v___x_2584_ == 0)
{
if (v___x_2583_ == 0)
{
lean_inc(v___y_2573_);
v___y_2497_ = v___y_2566_;
v___y_2498_ = v___y_2567_;
v___y_2499_ = v___x_2580_;
v___y_2500_ = v___x_2577_;
v___y_2501_ = v___y_2570_;
v___y_2502_ = v___x_2576_;
v___y_2503_ = v___y_2571_;
v___y_2504_ = v___x_2581_;
v___y_2505_ = v___x_2579_;
v___y_2506_ = v___y_2568_;
v___y_2507_ = v___x_2582_;
v___y_2508_ = v___y_2569_;
v___y_2509_ = v___x_2578_;
v___y_2510_ = v___y_2573_;
v_fst_2511_ = v___y_2573_;
v_snd_2512_ = v___y_2572_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec_ref(v___y_2572_);
v___x_2585_ = lean_box(0);
v___x_2586_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2497_ = v___y_2566_;
v___y_2498_ = v___y_2567_;
v___y_2499_ = v___x_2580_;
v___y_2500_ = v___x_2577_;
v___y_2501_ = v___y_2570_;
v___y_2502_ = v___x_2576_;
v___y_2503_ = v___y_2571_;
v___y_2504_ = v___x_2581_;
v___y_2505_ = v___x_2579_;
v___y_2506_ = v___y_2568_;
v___y_2507_ = v___x_2582_;
v___y_2508_ = v___y_2569_;
v___y_2509_ = v___x_2578_;
v___y_2510_ = v___y_2573_;
v_fst_2511_ = v___x_2585_;
v_snd_2512_ = v___x_2586_;
goto v___jp_2496_;
}
}
else
{
lean_inc(v___y_2573_);
v___y_2497_ = v___y_2566_;
v___y_2498_ = v___y_2567_;
v___y_2499_ = v___x_2580_;
v___y_2500_ = v___x_2577_;
v___y_2501_ = v___y_2570_;
v___y_2502_ = v___x_2576_;
v___y_2503_ = v___y_2571_;
v___y_2504_ = v___x_2581_;
v___y_2505_ = v___x_2579_;
v___y_2506_ = v___y_2568_;
v___y_2507_ = v___x_2582_;
v___y_2508_ = v___y_2569_;
v___y_2509_ = v___x_2578_;
v___y_2510_ = v___y_2573_;
v_fst_2511_ = v___y_2573_;
v_snd_2512_ = v___y_2572_;
goto v___jp_2496_;
}
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
v___x_2587_ = lean_box(v___x_2576_);
v___x_2588_ = lean_box(v___x_2577_);
lean_inc_ref(v_a_2423_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2589_, 0, v_cmds_2422_);
lean_closure_set(v___f_2589_, 1, v___y_2567_);
lean_closure_set(v___f_2589_, 2, v___y_2566_);
lean_closure_set(v___f_2589_, 3, v___x_2587_);
lean_closure_set(v___f_2589_, 4, v_a_2423_);
lean_closure_set(v___f_2589_, 5, v___y_2571_);
lean_closure_set(v___f_2589_, 6, v___y_2569_);
lean_closure_set(v___f_2589_, 7, v___x_2588_);
lean_closure_set(v___f_2589_, 8, v___x_2469_);
lean_closure_set(v___f_2589_, 9, v___f_2468_);
lean_closure_set(v___f_2589_, 10, v___f_2467_);
lean_closure_set(v___f_2589_, 11, v___f_2466_);
lean_closure_set(v___f_2589_, 12, v___y_2570_);
lean_closure_set(v___f_2589_, 13, v_cmdState_2418_);
lean_closure_set(v___f_2589_, 14, v___x_2470_);
lean_closure_set(v___f_2589_, 15, v___y_2568_);
lean_closure_set(v___f_2589_, 16, v_prom_2419_);
lean_closure_set(v___f_2589_, 17, v_old_x3f_2416_);
lean_closure_set(v___f_2589_, 18, v_parseCancelTk_2421_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_io_as_task(v___f_2589_, v___x_2590_);
lean_dec_ref(v___x_2591_);
goto v___jp_2425_;
}
}
else
{
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec_ref(v_cmds_2422_);
lean_dec_ref(v_parseCancelTk_2421_);
if (lean_obj_tag(v_old_x3f_2416_) == 1)
{
lean_object* v_val_2592_; lean_object* v___x_2593_; lean_object* v_children_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_val_2592_ = lean_ctor_get(v_old_x3f_2416_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v_old_x3f_2416_, 1);
v___x_2593_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2592_);
v_children_2594_ = lean_ctor_get(v___x_2593_, 1);
lean_inc_ref(v_children_2594_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = lean_array_get_size(v_children_2594_);
v___x_2597_ = lean_nat_dec_lt(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_dec_ref(v_children_2594_);
v___y_2525_ = v___y_2572_;
v___y_2526_ = v___x_2577_;
v___y_2527_ = v___y_2575_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_nat_dec_le(v___x_2596_, v___x_2596_);
if (v___x_2599_ == 0)
{
if (v___x_2597_ == 0)
{
lean_dec_ref(v_children_2594_);
v___y_2525_ = v___y_2572_;
v___y_2526_ = v___x_2577_;
v___y_2527_ = v___y_2575_;
goto v___jp_2524_;
}
else
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((size_t)0ULL);
v___x_2601_ = lean_usize_of_nat(v___x_2596_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2594_, v___x_2600_, v___x_2601_, v___x_2598_);
lean_dec_ref(v_children_2594_);
v___y_2561_ = v___y_2572_;
v___y_2562_ = v___x_2577_;
v___y_2563_ = v___y_2575_;
v___y_2564_ = v___x_2602_;
goto v___jp_2560_;
}
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = lean_usize_of_nat(v___x_2596_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2594_, v___x_2603_, v___x_2604_, v___x_2598_);
lean_dec_ref(v_children_2594_);
v___y_2561_ = v___y_2572_;
v___y_2562_ = v___x_2577_;
v___y_2563_ = v___y_2575_;
v___y_2564_ = v___x_2605_;
goto v___jp_2560_;
}
}
}
else
{
lean_dec(v_old_x3f_2416_);
v___y_2525_ = v___y_2572_;
v___y_2526_ = v___x_2577_;
v___y_2527_ = v___y_2575_;
goto v___jp_2524_;
}
}
}
v___jp_2607_:
{
lean_object* v_env_2608_; lean_object* v_scopes_2609_; lean_object* v___x_2610_; lean_object* v_opts_2611_; lean_object* v_currNamespace_2612_; lean_object* v_openDecls_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_snd_2619_; 
v_env_2608_ = lean_ctor_get(v_cmdState_2418_, 0);
v_scopes_2609_ = lean_ctor_get(v_cmdState_2418_, 2);
v___x_2610_ = l_List_head_x21___redArg(v___x_2469_, v_scopes_2609_);
v_opts_2611_ = lean_ctor_get(v___x_2610_, 1);
lean_inc_ref_n(v_opts_2611_, 2);
v_currNamespace_2612_ = lean_ctor_get(v___x_2610_, 2);
lean_inc(v_currNamespace_2612_);
v_openDecls_2613_ = lean_ctor_get(v___x_2610_, 3);
lean_inc(v_openDecls_2613_);
lean_dec(v___x_2610_);
lean_inc_ref(v_env_2608_);
v___x_2614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2614_, 0, v_env_2608_);
lean_ctor_set(v___x_2614_, 1, v_opts_2611_);
lean_ctor_set(v___x_2614_, 2, v_currNamespace_2612_);
lean_ctor_set(v___x_2614_, 3, v_openDecls_2613_);
lean_inc_ref(v_parserState_2417_);
lean_inc_ref(v_a_2423_);
v___f_2615_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2615_, 0, v_a_2423_);
lean_closure_set(v___f_2615_, 1, v___x_2614_);
lean_closure_set(v___f_2615_, 2, v_parserState_2417_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_profileit(v___x_2616_, v_opts_2611_, v___f_2615_, v___x_2617_);
v_snd_2619_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_snd_2619_);
if (lean_obj_tag(v_old_x3f_2416_) == 1)
{
lean_object* v_val_2620_; lean_object* v_fst_2621_; lean_object* v_fst_2622_; lean_object* v_snd_2623_; lean_object* v_pos_2624_; lean_object* v_toSnapshot_2625_; lean_object* v_stx_2626_; lean_object* v_parserState_2627_; lean_object* v_elabSnap_2628_; lean_object* v_nextCmdSnap_x3f_2629_; uint8_t v___x_2630_; 
v_val_2620_ = lean_ctor_get(v_old_x3f_2416_, 0);
v_fst_2621_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_n(v_fst_2621_, 2);
lean_dec(v___x_2618_);
v_fst_2622_ = lean_ctor_get(v_snd_2619_, 0);
lean_inc(v_fst_2622_);
v_snd_2623_ = lean_ctor_get(v_snd_2619_, 1);
lean_inc(v_snd_2623_);
lean_dec(v_snd_2619_);
v_pos_2624_ = lean_ctor_get(v_parserState_2417_, 0);
lean_inc(v_pos_2624_);
lean_dec_ref(v_parserState_2417_);
v_toSnapshot_2625_ = lean_ctor_get(v_val_2620_, 0);
v_stx_2626_ = lean_ctor_get(v_val_2620_, 1);
v_parserState_2627_ = lean_ctor_get(v_val_2620_, 2);
v_elabSnap_2628_ = lean_ctor_get(v_val_2620_, 3);
v_nextCmdSnap_x3f_2629_ = lean_ctor_get(v_val_2620_, 4);
lean_inc(v_stx_2626_);
v___x_2630_ = l_Lean_Syntax_eqWithInfo(v_fst_2621_, v_stx_2626_);
if (v___x_2630_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2629_) == 0)
{
lean_inc_ref(v_opts_2611_);
lean_inc(v_fst_2621_);
lean_inc(v_fst_2622_);
v___y_2566_ = v_fst_2622_;
v___y_2567_ = v_fst_2621_;
v___y_2568_ = v_opts_2611_;
v___y_2569_ = v___x_2617_;
v___y_2570_ = v_pos_2624_;
v___y_2571_ = v_snd_2623_;
v___y_2572_ = v_fst_2622_;
v___y_2573_ = v_fst_2621_;
v___y_2574_ = v_opts_2611_;
v___y_2575_ = v___x_2617_;
goto v___jp_2565_;
}
else
{
lean_object* v_val_2631_; lean_object* v___x_2632_; 
v_val_2631_ = lean_ctor_get(v_nextCmdSnap_x3f_2629_, 0);
lean_inc(v_val_2631_);
v___x_2632_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2606_, v_val_2631_);
lean_inc_ref(v_opts_2611_);
lean_inc(v_fst_2621_);
lean_inc(v_fst_2622_);
v___y_2566_ = v_fst_2622_;
v___y_2567_ = v_fst_2621_;
v___y_2568_ = v_opts_2611_;
v___y_2569_ = v___x_2617_;
v___y_2570_ = v_pos_2624_;
v___y_2571_ = v_snd_2623_;
v___y_2572_ = v_fst_2622_;
v___y_2573_ = v_fst_2621_;
v___y_2574_ = v_opts_2611_;
v___y_2575_ = v___x_2617_;
goto v___jp_2565_;
}
}
else
{
lean_inc(v_val_2620_);
lean_dec(v_pos_2624_);
lean_dec(v_snd_2623_);
lean_dec(v_fst_2621_);
lean_dec_ref_known(v_old_x3f_2416_, 1);
lean_dec_ref(v_opts_2611_);
lean_dec_ref(v_parseCancelTk_2421_);
lean_dec_ref(v_cmdState_2418_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2629_) == 1)
{
lean_object* v_val_2633_; 
lean_inc_ref(v_nextCmdSnap_x3f_2629_);
lean_inc_ref(v_elabSnap_2628_);
lean_inc_ref(v_parserState_2627_);
lean_inc(v_stx_2626_);
lean_inc_ref(v_toSnapshot_2625_);
lean_dec(v_val_2620_);
v_val_2633_ = lean_ctor_get(v_nextCmdSnap_x3f_2629_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2629_, 1);
v_toSnapshot_2430_ = v_toSnapshot_2625_;
v_stx_2431_ = v_stx_2626_;
v_parserState_2432_ = v_parserState_2627_;
v_elabSnap_2433_ = v_elabSnap_2628_;
v_val_2434_ = v_val_2633_;
v_newParserState_2435_ = v_fst_2622_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2634_; 
lean_dec(v_fst_2622_);
lean_dec_ref(v_cmds_2422_);
v___x_2634_ = lean_io_promise_resolve(v_val_2620_, v_prom_2419_);
lean_dec(v_prom_2419_);
return v___x_2634_;
}
}
}
else
{
lean_object* v_fst_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v_pos_2638_; 
v_fst_2635_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_n(v_fst_2635_, 2);
lean_dec(v___x_2618_);
v_fst_2636_ = lean_ctor_get(v_snd_2619_, 0);
lean_inc_n(v_fst_2636_, 2);
v_snd_2637_ = lean_ctor_get(v_snd_2619_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_snd_2619_);
v_pos_2638_ = lean_ctor_get(v_parserState_2417_, 0);
lean_inc(v_pos_2638_);
lean_dec_ref(v_parserState_2417_);
lean_inc_ref(v_opts_2611_);
v___y_2566_ = v_fst_2636_;
v___y_2567_ = v_fst_2635_;
v___y_2568_ = v_opts_2611_;
v___y_2569_ = v___x_2617_;
v___y_2570_ = v_pos_2638_;
v___y_2571_ = v_snd_2637_;
v___y_2572_ = v_fst_2636_;
v___y_2573_ = v_fst_2635_;
v___y_2574_ = v_opts_2611_;
v___y_2575_ = v___x_2617_;
goto v___jp_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2655_, lean_object* v_cmds_2656_, lean_object* v_stx_2657_, lean_object* v_newParserState_2658_, lean_object* v_val_2659_, uint8_t v_sync_2660_, lean_object* v_val_2661_, lean_object* v_a_2662_, lean_object* v_oldNext_2663_){
_start:
{
lean_object* v_cmdState_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_cmdState_2665_ = lean_ctor_get(v_oldResult_2655_, 1);
lean_inc_ref(v_cmdState_2665_);
lean_dec_ref(v_oldResult_2655_);
v___x_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_oldNext_2663_);
v___x_2667_ = lean_array_push(v_cmds_2656_, v_stx_2657_);
v___x_2668_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2666_, v_newParserState_2658_, v_cmdState_2665_, v_val_2659_, v_sync_2660_, v_val_2661_, v___x_2667_, v_a_2662_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2669_ = _args[0];
lean_object* v_val_2670_ = _args[1];
lean_object* v_cmds_2671_ = _args[2];
lean_object* v_fst_2672_ = _args[3];
lean_object* v_fst_2673_ = _args[4];
lean_object* v_val_2674_ = _args[5];
lean_object* v_a_2675_ = _args[6];
lean_object* v_snd_2676_ = _args[7];
lean_object* v___x_2677_ = _args[8];
lean_object* v___x_2678_ = _args[9];
lean_object* v_fst_2679_ = _args[10];
lean_object* v_val_2680_ = _args[11];
lean_object* v_val_2681_ = _args[12];
lean_object* v___x_2682_ = _args[13];
lean_object* v___f_2683_ = _args[14];
lean_object* v___f_2684_ = _args[15];
lean_object* v___f_2685_ = _args[16];
lean_object* v_pos_2686_ = _args[17];
lean_object* v_cmdState_2687_ = _args[18];
lean_object* v_val_2688_ = _args[19];
lean_object* v___x_2689_ = _args[20];
lean_object* v_opts_2690_ = _args[21];
lean_object* v___x_2691_ = _args[22];
lean_object* v_snd_2692_ = _args[23];
lean_object* v_prom_2693_ = _args[24];
lean_object* v_old_x3f_2694_ = _args[25];
lean_object* v_parseCancelTk_2695_ = _args[26];
lean_object* v_next_x3f_2696_ = _args[27];
lean_object* v___y_2697_ = _args[28];
_start:
{
uint8_t v_val_36137__boxed_2698_; uint8_t v___x_36140__boxed_2699_; lean_object* v_res_2700_; 
v_val_36137__boxed_2698_ = lean_unbox(v_val_2674_);
v___x_36140__boxed_2699_ = lean_unbox(v___x_2678_);
v_res_2700_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2669_, v_val_2670_, v_cmds_2671_, v_fst_2672_, v_fst_2673_, v_val_36137__boxed_2698_, v_a_2675_, v_snd_2676_, v___x_2677_, v___x_36140__boxed_2699_, v_fst_2679_, v_val_2680_, v_val_2681_, v___x_2682_, v___f_2683_, v___f_2684_, v___f_2685_, v_pos_2686_, v_cmdState_2687_, v_val_2688_, v___x_2689_, v_opts_2690_, v___x_2691_, v_snd_2692_, v_prom_2693_, v_old_x3f_2694_, v_parseCancelTk_2695_, v_next_x3f_2696_);
lean_dec(v_prom_2693_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_opts_2690_);
lean_dec(v_val_2681_);
lean_dec_ref(v_a_2675_);
lean_dec(v_val_2670_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2701_, lean_object* v_parserState_2702_, lean_object* v_cmdState_2703_, lean_object* v_prom_2704_, lean_object* v_sync_2705_, lean_object* v_parseCancelTk_2706_, lean_object* v_cmds_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
uint8_t v_sync_boxed_2710_; lean_object* v_res_2711_; 
v_sync_boxed_2710_ = lean_unbox(v_sync_2705_);
v_res_2711_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2701_, v_parserState_2702_, v_cmdState_2703_, v_prom_2704_, v_sync_boxed_2710_, v_parseCancelTk_2706_, v_cmds_2707_, v_a_2708_);
lean_dec_ref(v_a_2708_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2712_, size_t v_i_2713_, size_t v_stop_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2712_, v_i_2713_, v_stop_2714_, v_b_2715_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2719_, lean_object* v_i_2720_, lean_object* v_stop_2721_, lean_object* v_b_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
size_t v_i_boxed_2725_; size_t v_stop_boxed_2726_; lean_object* v_res_2727_; 
v_i_boxed_2725_ = lean_unbox_usize(v_i_2720_);
lean_dec(v_i_2720_);
v_stop_boxed_2726_ = lean_unbox_usize(v_stop_2721_);
lean_dec(v_stop_2721_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2719_, v_i_boxed_2725_, v_stop_boxed_2726_, v_b_2722_, v___y_2723_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v_as_2719_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2728_, lean_object* v_opt_2729_){
_start:
{
lean_object* v_name_2730_; lean_object* v_map_2731_; lean_object* v___x_2732_; 
v_name_2730_ = lean_ctor_get(v_opt_2729_, 0);
v_map_2731_ = lean_ctor_get(v_opts_2728_, 0);
v___x_2732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2731_, v_name_2730_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_box(0);
return v___x_2733_;
}
else
{
lean_object* v_val_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2743_; 
v_val_2734_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2736_ = v___x_2732_;
v_isShared_2737_ = v_isSharedCheck_2743_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_val_2734_);
lean_dec(v___x_2732_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2743_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
if (lean_obj_tag(v_val_2734_) == 0)
{
lean_object* v_v_2738_; lean_object* v___x_2740_; 
v_v_2738_ = lean_ctor_get(v_val_2734_, 0);
lean_inc_ref(v_v_2738_);
lean_dec_ref_known(v_val_2734_, 1);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v_v_2738_);
v___x_2740_ = v___x_2736_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_v_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
lean_object* v___x_2742_; 
lean_del_object(v___x_2736_);
lean_dec(v_val_2734_);
v___x_2742_ = lean_box(0);
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2744_, lean_object* v_opt_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2744_, v_opt_2745_);
lean_dec_ref(v_opt_2745_);
lean_dec_ref(v_opts_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2747_, lean_object* v_x_2748_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2747_);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2751_, 0, v_x_2748_);
lean_ctor_set(v___x_2751_, 1, v___x_2749_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2758_ = l_Lean_Array_toPArray_x27___redArg(v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
if (lean_obj_tag(v_a_2759_) == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_List_reverse___redArg(v_a_2760_);
return v___x_2761_;
}
else
{
lean_object* v_head_2762_; lean_object* v_tail_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2776_; 
v_head_2762_ = lean_ctor_get(v_a_2759_, 0);
v_tail_2763_ = lean_ctor_get(v_a_2759_, 1);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_a_2759_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2765_ = v_a_2759_;
v_isShared_2766_ = v_isSharedCheck_2776_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_tail_2763_);
lean_inc(v_head_2762_);
lean_dec(v_a_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2776_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2767_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v_head_2762_);
v___x_2769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
v___x_2770_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v_a_2760_);
lean_ctor_set(v___x_2765_, 0, v___x_2771_);
v___x_2773_ = v___x_2765_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_a_2760_);
v___x_2773_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v_a_2759_ = v_tail_2763_;
v_a_2760_ = v___x_2773_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2777_; double v___x_2778_; 
v___x_2777_ = lean_unsigned_to_nat(1000000000u);
v___x_2778_ = lean_float_of_nat(v___x_2777_);
return v___x_2778_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2796_ = l_Lean_MessageData_ofFormat(v___x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2797_, lean_object* v_stx_2798_, lean_object* v_origStx_2799_, lean_object* v_toProcessingContext_2800_, lean_object* v___x_2801_, lean_object* v_fileMap_2802_, lean_object* v_parserState_2803_, lean_object* v_a_2804_, lean_object* v___x_2805_, lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_toProcessingContext_2810_; lean_object* v___x_2811_; 
v_toProcessingContext_2810_ = lean_ctor_get(v___y_2808_, 0);
lean_inc_ref(v_toProcessingContext_2810_);
lean_inc(v_stx_2798_);
v___x_2811_ = lean_apply_3(v_setupImports_2797_, v_stx_2798_, v_toProcessingContext_2810_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_3025_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_3025_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_3025_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_a_2812_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; 
lean_dec_ref(v___x_2807_);
lean_dec(v___x_2805_);
lean_dec_ref(v_parserState_2803_);
lean_dec_ref(v_fileMap_2802_);
lean_dec(v___x_2801_);
lean_dec_ref(v_toProcessingContext_2800_);
lean_dec(v_origStx_2799_);
lean_dec(v_stx_2798_);
v_a_2816_ = lean_ctor_get(v_a_2812_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v_a_2812_, 1);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_a_2816_);
v___x_2818_ = v___x_2814_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_3024_; 
v_a_2820_ = lean_ctor_get(v_a_2812_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2822_ = v_a_2812_;
v_isShared_2823_ = v_isSharedCheck_3024_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v_a_2812_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_3024_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v_mainModuleName_2825_; lean_object* v_package_x3f_2826_; uint8_t v_isModule_2827_; lean_object* v_imports_2828_; lean_object* v_opts_2829_; uint32_t v_trustLevel_2830_; lean_object* v_importArts_2831_; lean_object* v_plugins_2832_; double v___x_2833_; double v___x_2834_; double v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2840_; 
v___x_2824_ = lean_io_mono_nanos_now();
v_mainModuleName_2825_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_mainModuleName_2825_);
v_package_x3f_2826_ = lean_ctor_get(v_a_2820_, 1);
lean_inc(v_package_x3f_2826_);
v_isModule_2827_ = lean_ctor_get_uint8(v_a_2820_, sizeof(void*)*6 + 4);
v_imports_2828_ = lean_ctor_get(v_a_2820_, 2);
lean_inc_ref(v_imports_2828_);
v_opts_2829_ = lean_ctor_get(v_a_2820_, 3);
lean_inc_ref(v_opts_2829_);
v_trustLevel_2830_ = lean_ctor_get_uint32(v_a_2820_, sizeof(void*)*6);
v_importArts_2831_ = lean_ctor_get(v_a_2820_, 4);
lean_inc(v_importArts_2831_);
v_plugins_2832_ = lean_ctor_get(v_a_2820_, 5);
lean_inc_ref(v_plugins_2832_);
lean_dec(v_a_2820_);
v___x_2833_ = lean_float_of_nat(v___x_2824_);
v___x_2834_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__0);
v___x_2835_ = lean_float_div(v___x_2833_, v___x_2834_);
v___x_2836_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2798_);
v___x_2837_ = l_Lean_MessageLog_empty;
v___x_2838_ = 1;
lean_inc(v_stx_2798_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_stx_2798_);
v___x_2840_ = v___x_2822_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_stx_2798_);
v___x_2840_ = v_reuseFailAlloc_3023_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_origStx_2799_);
lean_inc_ref(v___x_2840_);
lean_inc_ref(v_opts_2829_);
v___x_2842_ = l_Lean_Elab_processHeaderCore(v___x_2836_, v_imports_2828_, v_isModule_2827_, v_opts_2829_, v___x_2837_, v_toProcessingContext_2800_, v_trustLevel_2830_, v_plugins_2832_, v___x_2838_, v_mainModuleName_2825_, v_package_x3f_2826_, v_importArts_2831_, v___x_2840_, v___x_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_3014_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_3014_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_3014_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_3013_; 
v_fst_2847_ = lean_ctor_get(v_a_2843_, 0);
v_snd_2848_ = lean_ctor_get(v_a_2843_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_a_2843_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2850_ = v_a_2843_;
v_isShared_2851_ = v_isSharedCheck_3013_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_snd_2848_);
lean_inc(v_fst_2847_);
lean_dec(v_a_2843_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_3013_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; double v___x_2853_; double v___x_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v_traceState_2872_; 
v___x_2852_ = lean_io_mono_nanos_now();
v___x_2853_ = lean_float_of_nat(v___x_2852_);
v___x_2854_ = lean_float_div(v___x_2853_, v___x_2834_);
lean_inc(v_snd_2848_);
v___x_2855_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2848_);
v___x_2856_ = l_Lean_MessageLog_hasErrors(v_snd_2848_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_del_object(v___x_2814_);
lean_dec_ref(v___x_2807_);
v___x_2982_ = l_Lean_trace_profiler_output;
v___x_2983_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2829_, v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2984_ = l_Lean_trace_profiler_serve;
v___x_2985_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2829_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2872_ = v___x_2986_;
goto v___jp_2871_;
}
else
{
goto v___jp_2966_;
}
}
else
{
lean_dec_ref_known(v___x_2983_, 1);
goto v___jp_2966_;
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint64_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; size_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_del_object(v___x_2850_);
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
lean_del_object(v___x_2845_);
lean_dec_ref(v___x_2840_);
lean_dec_ref(v_opts_2829_);
lean_dec(v___x_2805_);
lean_dec_ref(v_parserState_2803_);
lean_dec_ref(v_fileMap_2802_);
lean_dec(v_stx_2798_);
v___x_2987_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2988_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2989_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2801_, 2);
v___x_2990_ = l_Lean_Name_num___override(v___x_2989_, v___x_2801_);
v___x_2991_ = l_Lean_Name_str___override(v___x_2990_, v___x_2987_);
v___x_2992_ = l_Lean_Name_str___override(v___x_2991_, v___x_2988_);
v___x_2993_ = l_Lean_Name_str___override(v___x_2992_, v___x_2987_);
v___x_2994_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2995_ = l_Lean_Name_str___override(v___x_2993_, v___x_2994_);
v___x_2996_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2997_ = l_Lean_Name_str___override(v___x_2995_, v___x_2996_);
v___x_2998_ = l_Lean_Name_toString(v___x_2997_, v___x_2838_);
v___x_2999_ = lean_box(0);
v___x_3000_ = 0ULL;
v___x_3001_ = lean_unsigned_to_nat(32u);
v___x_3002_ = lean_mk_empty_array_with_capacity(v___x_3001_);
v___x_3003_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3004_ = ((size_t)5ULL);
v___x_3005_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3002_);
lean_ctor_set(v___x_3005_, 2, v___x_2801_);
lean_ctor_set(v___x_3005_, 3, v___x_2801_);
lean_ctor_set_usize(v___x_3005_, 4, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
lean_ctor_set_uint64(v___x_3006_, sizeof(void*)*1, v___x_3000_);
v___x_3007_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3007_, 0, v___x_2998_);
lean_ctor_set(v___x_3007_, 1, v___x_2855_);
lean_ctor_set(v___x_3007_, 2, v___x_2999_);
lean_ctor_set(v___x_3007_, 3, v___x_3006_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*4, v___x_2856_);
v___x_3008_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2807_);
v___x_3009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
lean_ctor_set(v___x_3009_, 2, v___x_2999_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_3009_);
v___x_3011_ = v___x_2814_;
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
v___jp_2857_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___y_2863_);
v___x_2865_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2865_, 0, v___y_2859_);
lean_ctor_set(v___x_2865_, 1, v___x_2855_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
lean_ctor_set(v___x_2865_, 3, v___y_2858_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*4, v___x_2856_);
v___x_2866_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2862_, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2867_, 0, v___y_2860_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
lean_ctor_set(v___x_2867_, 2, v___y_2861_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2867_);
v___x_2869_ = v___x_2845_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
v___jp_2871_:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Language_Lean_reparseOptions(v_opts_2829_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v_env_2876_; lean_object* v_messages_2877_; lean_object* v_scopes_2878_; lean_object* v_usedQuotCtxts_2879_; lean_object* v_nextMacroScope_2880_; lean_object* v_maxRecDepth_2881_; lean_object* v_ngen_2882_; lean_object* v_auxDeclNGen_2883_; lean_object* v_snapshotTasks_2884_; lean_object* v_prevLinterStates_2885_; lean_object* v_codeQualityEntryTasks_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2955_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
lean_inc(v_fst_2847_);
v___x_2875_ = l_Lean_Elab_Command_mkState(v_fst_2847_, v_snd_2848_, v_a_2874_);
v_env_2876_ = lean_ctor_get(v___x_2875_, 0);
v_messages_2877_ = lean_ctor_get(v___x_2875_, 1);
v_scopes_2878_ = lean_ctor_get(v___x_2875_, 2);
v_usedQuotCtxts_2879_ = lean_ctor_get(v___x_2875_, 3);
v_nextMacroScope_2880_ = lean_ctor_get(v___x_2875_, 4);
v_maxRecDepth_2881_ = lean_ctor_get(v___x_2875_, 5);
v_ngen_2882_ = lean_ctor_get(v___x_2875_, 6);
v_auxDeclNGen_2883_ = lean_ctor_get(v___x_2875_, 7);
v_snapshotTasks_2884_ = lean_ctor_get(v___x_2875_, 10);
v_prevLinterStates_2885_ = lean_ctor_get(v___x_2875_, 11);
v_codeQualityEntryTasks_2886_ = lean_ctor_get(v___x_2875_, 12);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; lean_object* v_unused_2957_; 
v_unused_2956_ = lean_ctor_get(v___x_2875_, 9);
lean_dec(v_unused_2956_);
v_unused_2957_ = lean_ctor_get(v___x_2875_, 8);
lean_dec(v_unused_2957_);
v___x_2888_ = v___x_2875_;
v_isShared_2889_ = v_isSharedCheck_2955_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2886_);
lean_inc(v_prevLinterStates_2885_);
lean_inc(v_snapshotTasks_2884_);
lean_inc(v_auxDeclNGen_2883_);
lean_inc(v_ngen_2882_);
lean_inc(v_maxRecDepth_2881_);
lean_inc(v_nextMacroScope_2880_);
lean_inc(v_usedQuotCtxts_2879_);
lean_inc(v_scopes_2878_);
lean_inc(v_messages_2877_);
lean_inc(v_env_2876_);
lean_dec(v___x_2875_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2955_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_2891_ = lean_box(0);
lean_inc_n(v___x_2801_, 4);
v___x_2892_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2801_);
lean_ctor_set(v___x_2892_, 1, v___x_2801_);
lean_ctor_set(v___x_2892_, 2, v___x_2801_);
lean_ctor_set(v___x_2892_, 3, v___x_2801_);
lean_ctor_set(v___x_2892_, 4, v___x_2890_);
lean_ctor_set(v___x_2892_, 5, v___x_2890_);
lean_ctor_set(v___x_2892_, 6, v___x_2890_);
lean_ctor_set(v___x_2892_, 7, v___x_2890_);
lean_ctor_set(v___x_2892_, 8, v___x_2890_);
lean_ctor_set(v___x_2892_, 9, v___x_2890_);
lean_ctor_set(v___x_2892_, 10, v___x_2890_);
v___x_2893_ = l_Lean_Options_empty;
v___x_2894_ = lean_box(0);
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__3));
v___x_2898_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2898_, 0, v_fst_2847_);
lean_ctor_set(v___x_2898_, 1, v___x_2891_);
lean_ctor_set(v___x_2898_, 2, v_fileMap_2802_);
lean_ctor_set(v___x_2898_, 3, v___x_2892_);
lean_ctor_set(v___x_2898_, 4, v___x_2893_);
lean_ctor_set(v___x_2898_, 5, v___x_2894_);
lean_ctor_set(v___x_2898_, 6, v___x_2895_);
lean_ctor_set(v___x_2898_, 7, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
v___x_2900_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
lean_inc(v_stx_2798_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 1, v_stx_2798_);
lean_ctor_set(v___x_2850_, 0, v___x_2900_);
v___x_2902_ = v___x_2850_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_stx_2798_);
v___x_2902_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
v___x_2904_ = lean_unsigned_to_nat(2u);
v___x_2905_ = l_Lean_Syntax_getArg(v_stx_2798_, v___x_2904_);
lean_dec(v_stx_2798_);
v___x_2906_ = l_Lean_Syntax_getArgs(v___x_2905_);
lean_dec(v___x_2905_);
v___x_2907_ = lean_array_to_list(v___x_2906_);
v___x_2908_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2907_, v___x_2895_);
v___x_2909_ = l_Lean_List_toPArray_x27___redArg(v___x_2908_);
v___x_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2903_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2899_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_mk_empty_array_with_capacity(v___x_2896_);
v___x_2913_ = lean_array_push(v___x_2912_, v___x_2911_);
v___x_2914_ = l_Lean_Array_toPArray_x27___redArg(v___x_2913_);
lean_dec_ref(v___x_2913_);
lean_inc_ref(v___x_2914_);
v___x_2915_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2915_, 0, v___x_2890_);
lean_ctor_set(v___x_2915_, 1, v___x_2890_);
lean_ctor_set(v___x_2915_, 2, v___x_2914_);
lean_ctor_set_uint8(v___x_2915_, sizeof(void*)*3, v___x_2838_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 9, v_traceState_2872_);
lean_ctor_set(v___x_2888_, 8, v___x_2915_);
v___x_2917_ = v___x_2888_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_env_2876_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_messages_2877_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_scopes_2878_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_usedQuotCtxts_2879_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_nextMacroScope_2880_);
lean_ctor_set(v_reuseFailAlloc_2953_, 5, v_maxRecDepth_2881_);
lean_ctor_set(v_reuseFailAlloc_2953_, 6, v_ngen_2882_);
lean_ctor_set(v_reuseFailAlloc_2953_, 7, v_auxDeclNGen_2883_);
lean_ctor_set(v_reuseFailAlloc_2953_, 8, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2953_, 9, v_traceState_2872_);
lean_ctor_set(v_reuseFailAlloc_2953_, 10, v_snapshotTasks_2884_);
lean_ctor_set(v_reuseFailAlloc_2953_, 11, v_prevLinterStates_2885_);
lean_ctor_set(v_reuseFailAlloc_2953_, 12, v_codeQualityEntryTasks_2886_);
v___x_2917_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; lean_object* v_size_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; uint64_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2918_ = lean_io_promise_new();
v___x_2919_ = l_IO_CancelToken_new();
v___x_2920_ = lean_mk_empty_array_with_capacity(v___x_2801_);
lean_inc_ref(v___x_2919_);
lean_inc(v___x_2918_);
lean_inc_ref(v___x_2917_);
v___x_2921_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2891_, v_parserState_2803_, v___x_2917_, v___x_2918_, v___x_2838_, v___x_2919_, v___x_2920_, v_a_2804_);
v___x_2922_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2923_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2924_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2801_, 3);
v___x_2925_ = l_Lean_Name_num___override(v___x_2924_, v___x_2801_);
v___x_2926_ = lean_unsigned_to_nat(32u);
v___x_2927_ = lean_mk_empty_array_with_capacity(v___x_2926_);
v___x_2928_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2929_ = ((size_t)5ULL);
v___x_2930_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2927_);
lean_ctor_set(v___x_2930_, 2, v___x_2801_);
lean_ctor_set(v___x_2930_, 3, v___x_2801_);
lean_ctor_set_usize(v___x_2930_, 4, v___x_2929_);
v_size_2931_ = lean_ctor_get(v___x_2914_, 2);
lean_inc(v_size_2931_);
v___x_2932_ = l_Lean_Name_str___override(v___x_2925_, v___x_2922_);
v___x_2933_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2805_);
v___x_2934_ = l_Lean_Name_str___override(v___x_2932_, v___x_2923_);
v___x_2935_ = l_Lean_Name_str___override(v___x_2934_, v___x_2922_);
v___x_2936_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2937_ = l_Lean_Name_str___override(v___x_2935_, v___x_2936_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6));
v___x_2939_ = l_Lean_Name_str___override(v___x_2937_, v___x_2938_);
v___x_2940_ = l_Lean_Name_toString(v___x_2939_, v___x_2838_);
v___x_2941_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2942_ = 0ULL;
v___x_2943_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2943_, 0, v___x_2930_);
lean_ctor_set_uint64(v___x_2943_, sizeof(void*)*1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2919_);
v___x_2945_ = l_IO_Promise_result_x21___redArg(v___x_2918_);
lean_dec(v___x_2918_);
v___x_2946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2805_);
lean_ctor_set(v___x_2946_, 1, v___x_2933_);
lean_ctor_set(v___x_2946_, 2, v___x_2944_);
lean_ctor_set(v___x_2946_, 3, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2917_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_inc_ref(v___x_2943_);
lean_inc_ref(v___x_2940_);
v___x_2949_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2949_, 0, v___x_2940_);
lean_ctor_set(v___x_2949_, 1, v___x_2941_);
lean_ctor_set(v___x_2949_, 2, v___x_2891_);
lean_ctor_set(v___x_2949_, 3, v___x_2943_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*4, v___x_2856_);
v___x_2950_ = lean_nat_dec_lt(v___x_2801_, v_size_2931_);
lean_dec(v_size_2931_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2801_);
v___x_2951_ = l_outOfBounds___redArg(v___x_2806_);
v___y_2858_ = v___x_2943_;
v___y_2859_ = v___x_2940_;
v___y_2860_ = v___x_2949_;
v___y_2861_ = v___x_2948_;
v___y_2862_ = v___x_2840_;
v___y_2863_ = v___x_2951_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2806_, v___x_2914_, v___x_2801_);
lean_dec(v___x_2801_);
lean_dec_ref(v___x_2914_);
v___y_2858_ = v___x_2943_;
v___y_2859_ = v___x_2940_;
v___y_2860_ = v___x_2949_;
v___y_2861_ = v___x_2948_;
v___y_2862_ = v___x_2840_;
v___y_2863_ = v___x_2952_;
goto v___jp_2857_;
}
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec_ref(v_traceState_2872_);
lean_dec_ref(v___x_2855_);
lean_del_object(v___x_2850_);
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
lean_del_object(v___x_2845_);
lean_dec_ref(v___x_2840_);
lean_dec(v___x_2805_);
lean_dec_ref(v_parserState_2803_);
lean_dec_ref(v_fileMap_2802_);
lean_dec(v___x_2801_);
lean_dec(v_stx_2798_);
v_a_2958_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2873_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2873_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
v___jp_2966_:
{
uint64_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2967_ = 0ULL;
v___x_2968_ = lean_box(0);
v___x_2969_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2970_ = lean_box(0);
v___x_2971_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2972_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2972_, 0, v___x_2969_);
lean_ctor_set(v___x_2972_, 1, v___x_2970_);
lean_ctor_set(v___x_2972_, 2, v___x_2971_);
lean_ctor_set_float(v___x_2972_, sizeof(void*)*3, v___x_2835_);
lean_ctor_set_float(v___x_2972_, sizeof(void*)*3 + 8, v___x_2854_);
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*3 + 16, v___x_2838_);
v___x_2973_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2974_ = lean_mk_empty_array_with_capacity(v___x_2801_);
v___x_2975_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2972_);
lean_ctor_set(v___x_2975_, 1, v___x_2973_);
lean_ctor_set(v___x_2975_, 2, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2968_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = lean_unsigned_to_nat(1u);
v___x_2978_ = lean_mk_empty_array_with_capacity(v___x_2977_);
v___x_2979_ = lean_array_push(v___x_2978_, v___x_2976_);
v___x_2980_ = l_Lean_Array_toPArray_x27___redArg(v___x_2979_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set_uint64(v___x_2981_, sizeof(void*)*1, v___x_2967_);
v_traceState_2872_ = v___x_2981_;
goto v___jp_2871_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v___x_2840_);
lean_dec_ref(v_opts_2829_);
lean_del_object(v___x_2814_);
lean_dec_ref(v___x_2807_);
lean_dec(v___x_2805_);
lean_dec_ref(v_parserState_2803_);
lean_dec_ref(v_fileMap_2802_);
lean_dec(v___x_2801_);
lean_dec(v_stx_2798_);
v_a_3015_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2842_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2842_);
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
lean_dec_ref(v___x_2807_);
lean_dec(v___x_2805_);
lean_dec_ref(v_parserState_2803_);
lean_dec_ref(v_fileMap_2802_);
lean_dec(v___x_2801_);
lean_dec_ref(v_toProcessingContext_2800_);
lean_dec(v_origStx_2799_);
lean_dec(v_stx_2798_);
v_a_3026_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2811_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2811_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3034_, lean_object* v_stx_3035_, lean_object* v_origStx_3036_, lean_object* v_toProcessingContext_3037_, lean_object* v___x_3038_, lean_object* v_fileMap_3039_, lean_object* v_parserState_3040_, lean_object* v_a_3041_, lean_object* v___x_3042_, lean_object* v___x_3043_, lean_object* v___x_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3034_, v_stx_3035_, v_origStx_3036_, v_toProcessingContext_3037_, v___x_3038_, v_fileMap_3039_, v_parserState_3040_, v_a_3041_, v___x_3042_, v___x_3043_, v___x_3044_, v___y_3045_);
lean_dec_ref(v___y_3045_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_a_3041_);
return v_res_3047_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___f_3049_; 
v___x_3048_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3049_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3049_, 0, v___x_3048_);
return v___f_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3050_, lean_object* v_stx_3051_, lean_object* v_origStx_3052_, lean_object* v_parserState_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_toProcessingContext_3056_; lean_object* v_fileMap_3057_; lean_object* v_endPos_3058_; lean_object* v___x_3059_; lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_toProcessingContext_3056_ = lean_ctor_get(v_a_3054_, 0);
v_fileMap_3057_ = lean_ctor_get(v_toProcessingContext_3056_, 2);
v_endPos_3058_ = lean_ctor_get(v_toProcessingContext_3056_, 3);
v___x_3059_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3060_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3061_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3062_ = lean_box(0);
v___x_3063_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3054_, 2);
lean_inc_ref(v_fileMap_3057_);
lean_inc_ref(v_toProcessingContext_3056_);
v___f_3064_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3064_, 0, v_setupImports_3050_);
lean_closure_set(v___f_3064_, 1, v_stx_3051_);
lean_closure_set(v___f_3064_, 2, v_origStx_3052_);
lean_closure_set(v___f_3064_, 3, v_toProcessingContext_3056_);
lean_closure_set(v___f_3064_, 4, v___x_3063_);
lean_closure_set(v___f_3064_, 5, v_fileMap_3057_);
lean_closure_set(v___f_3064_, 6, v_parserState_3053_);
lean_closure_set(v___f_3064_, 7, v_a_3054_);
lean_closure_set(v___f_3064_, 8, v___x_3062_);
lean_closure_set(v___f_3064_, 9, v___x_3061_);
lean_closure_set(v___f_3064_, 10, v___x_3059_);
lean_inc(v_endPos_3058_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v_endPos_3058_);
v___x_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
v___x_3067_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3067_, 0, lean_box(0));
lean_closure_set(v___x_3067_, 1, v___f_3060_);
lean_closure_set(v___x_3067_, 2, v___f_3064_);
lean_closure_set(v___x_3067_, 3, v_a_3054_);
v___x_3068_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3062_, v___x_3062_, v___x_3066_, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3069_, lean_object* v_stx_3070_, lean_object* v_origStx_3071_, lean_object* v_parserState_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3069_, v_stx_3070_, v_origStx_3071_, v_parserState_3072_, v_a_3073_);
lean_dec_ref(v_a_3073_);
return v_res_3075_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_box(0);
v___x_3079_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = 1;
v___x_3085_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3086_ = l_Lean_Name_toString(v___x_3085_, v___x_3084_);
return v___x_3086_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3087_ = 0;
v___x_3088_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3089_ = lean_box(0);
v___x_3090_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3091_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3092_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
lean_ctor_set(v___x_3092_, 3, v___x_3088_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*4, v___x_3087_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3093_, lean_object* v_cmdState_3094_, lean_object* v_a_3095_, lean_object* v_toSnapshot_3096_, lean_object* v_newStx_3097_, lean_object* v_oldCmd_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_diagnostics_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3128_; 
v___x_3100_ = lean_io_promise_new();
v___x_3101_ = l_IO_CancelToken_new();
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_oldCmd_3098_);
v___x_3103_ = 1;
v___x_3104_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3101_);
lean_inc(v___x_3100_);
lean_inc_ref(v_cmdState_3094_);
v___x_3105_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3102_, v_newParserState_3093_, v_cmdState_3094_, v___x_3100_, v___x_3103_, v___x_3101_, v___x_3104_, v_a_3095_);
v_diagnostics_3106_ = lean_ctor_get(v_toSnapshot_3096_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_toSnapshot_3096_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; 
v_unused_3129_ = lean_ctor_get(v_toSnapshot_3096_, 3);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_toSnapshot_3096_, 2);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_toSnapshot_3096_, 0);
lean_dec(v_unused_3131_);
v___x_3108_ = v_toSnapshot_3096_;
v_isShared_3109_ = v_isSharedCheck_3128_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_diagnostics_3106_);
lean_dec(v_toSnapshot_3096_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3128_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3112_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3113_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3101_);
v___x_3115_ = l_IO_Promise_result_x21___redArg(v___x_3100_);
lean_dec(v___x_3100_);
v___x_3116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3110_);
lean_ctor_set(v___x_3116_, 1, v___x_3111_);
lean_ctor_set(v___x_3116_, 2, v___x_3114_);
lean_ctor_set(v___x_3116_, 3, v___x_3115_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_cmdState_3094_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
v___x_3119_ = 0;
v___x_3120_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_newStx_3097_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 3, v___x_3113_);
lean_ctor_set(v___x_3108_, 2, v___x_3110_);
lean_ctor_set(v___x_3108_, 0, v___x_3112_);
v___x_3123_ = v___x_3108_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_diagnostics_3106_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v___x_3113_);
v___x_3123_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_ctor_set_uint8(v___x_3123_, sizeof(void*)*4, v___x_3119_);
v___x_3124_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3121_, v___x_3123_);
v___x_3125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3120_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
lean_ctor_set(v___x_3125_, 2, v___x_3118_);
v___x_3126_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3110_, v___x_3125_);
return v___x_3126_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3132_, lean_object* v_cmdState_3133_, lean_object* v_a_3134_, lean_object* v_toSnapshot_3135_, lean_object* v_newStx_3136_, lean_object* v_oldCmd_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3132_, v_cmdState_3133_, v_a_3134_, v_toSnapshot_3135_, v_newStx_3136_, v_oldCmd_3137_);
lean_dec_ref(v_a_3134_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3140_, lean_object* v_a_3141_, lean_object* v_newStx_3142_, lean_object* v___x_3143_, lean_object* v_oldProcessed_3144_){
_start:
{
lean_object* v_result_x3f_3146_; 
v_result_x3f_3146_ = lean_ctor_get(v_oldProcessed_3144_, 2);
if (lean_obj_tag(v_result_x3f_3146_) == 1)
{
lean_object* v_val_3147_; lean_object* v_firstCmdSnap_3148_; lean_object* v_toSnapshot_3149_; lean_object* v_cmdState_3150_; lean_object* v_stx_x3f_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; 
v_val_3147_ = lean_ctor_get(v_result_x3f_3146_, 0);
lean_inc(v_val_3147_);
v_firstCmdSnap_3148_ = lean_ctor_get(v_val_3147_, 1);
lean_inc_ref(v_firstCmdSnap_3148_);
v_toSnapshot_3149_ = lean_ctor_get(v_oldProcessed_3144_, 0);
lean_inc_ref(v_toSnapshot_3149_);
lean_dec_ref(v_oldProcessed_3144_);
v_cmdState_3150_ = lean_ctor_get(v_val_3147_, 0);
lean_inc_ref(v_cmdState_3150_);
lean_dec(v_val_3147_);
v_stx_x3f_3151_ = lean_ctor_get(v_firstCmdSnap_3148_, 0);
lean_inc(v_stx_x3f_3151_);
lean_inc_ref(v_a_3141_);
v___f_3152_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3152_, 0, v_newParserState_3140_);
lean_closure_set(v___f_3152_, 1, v_cmdState_3150_);
lean_closure_set(v___f_3152_, 2, v_a_3141_);
lean_closure_set(v___f_3152_, 3, v_toSnapshot_3149_);
lean_closure_set(v___f_3152_, 4, v_newStx_3142_);
v___x_3153_ = lean_box(0);
v___x_3154_ = 1;
v___x_3155_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3148_, v___f_3152_, v_stx_x3f_3151_, v___x_3143_, v___x_3153_, v___x_3154_);
return v___x_3155_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec(v___x_3143_);
lean_dec_ref(v_newParserState_3140_);
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_newStx_3142_);
v___x_3157_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3156_, v_oldProcessed_3144_);
return v___x_3157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3158_, lean_object* v_a_3159_, lean_object* v_newStx_3160_, lean_object* v___x_3161_, lean_object* v_oldProcessed_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3158_, v_a_3159_, v_newStx_3160_, v___x_3161_, v_oldProcessed_3162_);
lean_dec_ref(v_a_3159_);
return v_res_3164_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3165_ = 0;
v___x_3166_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3167_ = lean_box(0);
v___x_3168_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3169_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3170_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
lean_ctor_set(v___x_3170_, 2, v___x_3167_);
lean_ctor_set(v___x_3170_, 3, v___x_3166_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*4, v___x_3165_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3171_, lean_object* v_a_3172_, lean_object* v_old_3173_, lean_object* v_newStx_3174_, lean_object* v_newParserState_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_result_x3f_3178_; 
v_result_x3f_3178_ = lean_ctor_get(v_old_3173_, 4);
lean_inc(v_result_x3f_3178_);
if (lean_obj_tag(v_result_x3f_3178_) == 1)
{
lean_object* v_val_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3233_; 
v_val_3179_ = lean_ctor_get(v_result_x3f_3178_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_result_x3f_3178_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3181_ = v_result_x3f_3178_;
v_isShared_3182_ = v_isSharedCheck_3233_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_val_3179_);
lean_dec(v_result_x3f_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3233_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_processedSnap_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3231_; 
v_processedSnap_3183_ = lean_ctor_get(v_val_3179_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_val_3179_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v_val_3179_, 0);
lean_dec(v_unused_3232_);
v___x_3185_ = v_val_3179_;
v_isShared_3186_ = v_isSharedCheck_3231_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_processedSnap_3183_);
lean_dec(v_val_3179_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3231_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_toSnapshot_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3226_; 
v_toSnapshot_3187_ = lean_ctor_get(v_old_3173_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_old_3173_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; lean_object* v_unused_3228_; lean_object* v_unused_3229_; lean_object* v_unused_3230_; 
v_unused_3227_ = lean_ctor_get(v_old_3173_, 4);
lean_dec(v_unused_3227_);
v_unused_3228_ = lean_ctor_get(v_old_3173_, 3);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_old_3173_, 2);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v_old_3173_, 1);
lean_dec(v_unused_3230_);
v___x_3189_ = v_old_3173_;
v_isShared_3190_ = v_isSharedCheck_3226_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_toSnapshot_3187_);
lean_dec(v_old_3173_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3226_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_pos_3191_; lean_object* v_endPos_3192_; lean_object* v_stx_x3f_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; lean_object* v___x_3199_; lean_object* v_diagnostics_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3222_; 
v_pos_3191_ = lean_ctor_get(v_newParserState_3175_, 0);
v_endPos_3192_ = lean_ctor_get(v_toProcessingContext_3171_, 3);
v_stx_x3f_3193_ = lean_ctor_get(v_processedSnap_3183_, 0);
lean_inc(v_stx_x3f_3193_);
lean_inc(v_endPos_3192_);
lean_inc(v_pos_3191_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_pos_3191_);
lean_ctor_set(v___x_3194_, 1, v_endPos_3192_);
v___x_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_inc_ref(v___x_3195_);
lean_inc(v_newStx_3174_);
lean_inc_ref(v_a_3172_);
lean_inc_ref(v_newParserState_3175_);
v___f_3196_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3196_, 0, v_newParserState_3175_);
lean_closure_set(v___f_3196_, 1, v_a_3172_);
lean_closure_set(v___f_3196_, 2, v_newStx_3174_);
lean_closure_set(v___f_3196_, 3, v___x_3195_);
v___x_3197_ = lean_box(0);
v___x_3198_ = 1;
v___x_3199_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3183_, v___f_3196_, v_stx_x3f_3193_, v___x_3195_, v___x_3197_, v___x_3198_);
v_diagnostics_3200_ = lean_ctor_get(v_toSnapshot_3187_, 1);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_toSnapshot_3187_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; 
v_unused_3223_ = lean_ctor_get(v_toSnapshot_3187_, 3);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_toSnapshot_3187_, 2);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_toSnapshot_3187_, 0);
lean_dec(v_unused_3225_);
v___x_3202_ = v_toSnapshot_3187_;
v_isShared_3203_ = v_isSharedCheck_3222_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_diagnostics_3200_);
lean_dec(v_toSnapshot_3187_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3222_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3204_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3205_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v___x_3199_);
lean_ctor_set(v___x_3185_, 0, v_newParserState_3175_);
v___x_3207_ = v___x_3185_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_newParserState_3175_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3199_);
v___x_3207_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3207_);
v___x_3209_ = v___x_3181_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
uint8_t v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3210_ = 0;
v___x_3211_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3174_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_newStx_3174_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 3, v___x_3205_);
lean_ctor_set(v___x_3202_, 2, v___x_3197_);
lean_ctor_set(v___x_3202_, 0, v___x_3204_);
v___x_3214_ = v___x_3202_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_diagnostics_3200_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v___x_3205_);
v___x_3214_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_ctor_set_uint8(v___x_3214_, sizeof(void*)*4, v___x_3210_);
v___x_3215_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3212_, v___x_3214_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 4, v___x_3209_);
lean_ctor_set(v___x_3189_, 3, v_newStx_3174_);
lean_ctor_set(v___x_3189_, 2, v_toProcessingContext_3171_);
lean_ctor_set(v___x_3189_, 1, v___x_3215_);
lean_ctor_set(v___x_3189_, 0, v___x_3211_);
v___x_3217_ = v___x_3189_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_toProcessingContext_3171_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_newStx_3174_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v___x_3209_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
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
lean_dec(v_result_x3f_3178_);
lean_dec_ref(v_newParserState_3175_);
lean_dec(v_newStx_3174_);
lean_dec_ref(v_toProcessingContext_3171_);
return v_old_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3234_, lean_object* v_a_3235_, lean_object* v_old_3236_, lean_object* v_newStx_3237_, lean_object* v_newParserState_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3234_, v_a_3235_, v_old_3236_, v_newStx_3237_, v_newParserState_3238_, v___y_3239_);
lean_dec_ref(v___y_3239_);
lean_dec_ref(v_a_3235_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3242_, lean_object* v_setupImports_3243_, lean_object* v_old_x3f_3244_, lean_object* v___x_3245_, lean_object* v___f_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
lean_inc_ref(v_toProcessingContext_3242_);
v___x_3249_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3242_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3318_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3318_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3318_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v_snd_3254_; lean_object* v_fst_3255_; lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3317_; 
v_snd_3254_ = lean_ctor_get(v_a_3250_, 1);
lean_inc(v_snd_3254_);
v_fst_3255_ = lean_ctor_get(v_a_3250_, 0);
lean_inc(v_fst_3255_);
lean_dec(v_a_3250_);
v_fst_3256_ = lean_ctor_get(v_snd_3254_, 0);
v_snd_3257_ = lean_ctor_get(v_snd_3254_, 1);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_snd_3254_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3259_ = v_snd_3254_;
v_isShared_3260_ = v_isSharedCheck_3317_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_snd_3257_);
lean_inc(v_fst_3256_);
lean_dec(v_snd_3254_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3317_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_MessageLog_hasErrors(v_snd_3257_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; lean_object* v___y_3264_; 
lean_inc(v_fst_3255_);
v___x_3262_ = l_Lean_Syntax_unsetTrailing(v_fst_3255_);
if (lean_obj_tag(v_old_x3f_3244_) == 1)
{
lean_object* v_val_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3300_; 
v_val_3285_ = lean_ctor_get(v_old_x3f_3244_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_old_x3f_3244_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3287_ = v_old_x3f_3244_;
v_isShared_3288_ = v_isSharedCheck_3300_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_val_3285_);
lean_dec(v_old_x3f_3244_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3300_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v_stx_3289_; lean_object* v_result_x3f_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v_stx_3289_ = lean_ctor_get(v_val_3285_, 3);
v_result_x3f_3290_ = lean_ctor_get(v_val_3285_, 4);
lean_inc(v_stx_3289_);
v___x_3291_ = l_Lean_Syntax_unsetTrailing(v_stx_3289_);
lean_inc(v___x_3262_);
v___x_3292_ = l_Lean_Syntax_eqWithInfo(v___x_3262_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_inc(v_result_x3f_3290_);
lean_del_object(v___x_3287_);
lean_dec(v_val_3285_);
lean_dec_ref(v___f_3246_);
if (lean_obj_tag(v_result_x3f_3290_) == 0)
{
lean_dec_ref(v___x_3245_);
v___y_3264_ = v___y_3247_;
goto v___jp_3263_;
}
else
{
lean_object* v_val_3293_; lean_object* v_processedSnap_3294_; lean_object* v___x_3295_; 
v_val_3293_ = lean_ctor_get(v_result_x3f_3290_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v_result_x3f_3290_, 1);
v_processedSnap_3294_ = lean_ctor_get(v_val_3293_, 1);
lean_inc_ref(v_processedSnap_3294_);
lean_dec(v_val_3293_);
v___x_3295_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3245_, v_processedSnap_3294_);
v___y_3264_ = v___y_3247_;
goto v___jp_3263_;
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3298_; 
lean_dec(v___x_3262_);
lean_del_object(v___x_3259_);
lean_dec(v_snd_3257_);
lean_del_object(v___x_3252_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_setupImports_3243_);
lean_dec_ref(v_toProcessingContext_3242_);
lean_inc_ref(v___y_3247_);
v___x_3296_ = lean_apply_5(v___f_3246_, v_val_3285_, v_fst_3255_, v_fst_3256_, v___y_3247_, lean_box(0));
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3296_);
v___x_3298_ = v___x_3287_;
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
else
{
lean_dec_ref(v___f_3246_);
lean_dec_ref(v___x_3245_);
lean_dec(v_old_x3f_3244_);
v___y_3264_ = v___y_3247_;
goto v___jp_3263_;
}
v___jp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3265_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3257_);
lean_inc(v_fst_3256_);
lean_inc(v_fst_3255_);
v___x_3266_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3243_, v___x_3262_, v_fst_3255_, v_fst_3256_, v___y_3264_);
v___x_3267_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3268_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3269_ = lean_box(0);
v___x_3270_ = lean_unsigned_to_nat(32u);
v___x_3271_ = lean_mk_empty_array_with_capacity(v___x_3270_);
lean_dec_ref(v___x_3271_);
v___x_3272_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 1, v___x_3266_);
v___x_3274_ = v___x_3259_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_fst_3256_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v___x_3266_);
v___x_3274_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3276_, 0, v___x_3267_);
lean_ctor_set(v___x_3276_, 1, v___x_3268_);
lean_ctor_set(v___x_3276_, 2, v___x_3269_);
lean_ctor_set(v___x_3276_, 3, v___x_3272_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*4, v___x_3261_);
lean_inc(v_fst_3255_);
v___x_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3277_, 0, v_fst_3255_);
v___x_3278_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3278_, 0, v___x_3267_);
lean_ctor_set(v___x_3278_, 1, v___x_3265_);
lean_ctor_set(v___x_3278_, 2, v___x_3269_);
lean_ctor_set(v___x_3278_, 3, v___x_3272_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*4, v___x_3261_);
v___x_3279_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3277_, v___x_3278_);
v___x_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3276_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
lean_ctor_set(v___x_3280_, 2, v_toProcessingContext_3242_);
lean_ctor_set(v___x_3280_, 3, v_fst_3255_);
lean_ctor_set(v___x_3280_, 4, v___x_3275_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3280_);
v___x_3282_ = v___x_3252_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
lean_del_object(v___x_3259_);
lean_dec(v_fst_3256_);
lean_dec_ref(v___f_3246_);
lean_dec_ref(v___x_3245_);
lean_dec(v_old_x3f_3244_);
lean_dec_ref(v_setupImports_3243_);
v___x_3301_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3257_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3303_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_unsigned_to_nat(32u);
v___x_3306_ = lean_mk_empty_array_with_capacity(v___x_3305_);
lean_dec_ref(v___x_3306_);
v___x_3307_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3308_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3308_, 0, v___x_3302_);
lean_ctor_set(v___x_3308_, 1, v___x_3303_);
lean_ctor_set(v___x_3308_, 2, v___x_3304_);
lean_ctor_set(v___x_3308_, 3, v___x_3307_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*4, v___x_3261_);
lean_inc(v_fst_3255_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v_fst_3255_);
v___x_3310_ = 0;
v___x_3311_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3311_, 0, v___x_3302_);
lean_ctor_set(v___x_3311_, 1, v___x_3301_);
lean_ctor_set(v___x_3311_, 2, v___x_3304_);
lean_ctor_set(v___x_3311_, 3, v___x_3307_);
lean_ctor_set_uint8(v___x_3311_, sizeof(void*)*4, v___x_3310_);
v___x_3312_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3309_, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3308_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
lean_ctor_set(v___x_3313_, 2, v_toProcessingContext_3242_);
lean_ctor_set(v___x_3313_, 3, v_fst_3255_);
lean_ctor_set(v___x_3313_, 4, v___x_3304_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3313_);
v___x_3315_ = v___x_3252_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref(v___f_3246_);
lean_dec_ref(v___x_3245_);
lean_dec(v_old_x3f_3244_);
lean_dec_ref(v_setupImports_3243_);
lean_dec_ref(v_toProcessingContext_3242_);
v_a_3319_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3249_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3249_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3327_, lean_object* v_setupImports_3328_, lean_object* v_old_x3f_3329_, lean_object* v___x_3330_, lean_object* v___f_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3327_, v_setupImports_3328_, v_old_x3f_3329_, v___x_3330_, v___f_3331_, v___y_3332_);
lean_dec_ref(v___y_3332_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3335_, lean_object* v_toProcessingContext_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3338_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3335_);
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3341_, 0, v_x_3337_);
lean_ctor_set(v___x_3341_, 1, v___x_3338_);
lean_ctor_set(v___x_3341_, 2, v_toProcessingContext_3336_);
lean_ctor_set(v___x_3341_, 3, v___x_3339_);
lean_ctor_set(v___x_3341_, 4, v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3342_, lean_object* v_old_x3f_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_toProcessingContext_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___f_3351_; 
v_toProcessingContext_3346_ = lean_ctor_get(v_a_3344_, 0);
v___x_3347_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3348_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3344_);
lean_inc_ref_n(v_toProcessingContext_3346_, 3);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3349_, 0, v_toProcessingContext_3346_);
lean_closure_set(v___f_3349_, 1, v_a_3344_);
lean_inc(v_old_x3f_3343_);
v___f_3350_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3350_, 0, v_toProcessingContext_3346_);
lean_closure_set(v___f_3350_, 1, v_setupImports_3342_);
lean_closure_set(v___f_3350_, 2, v_old_x3f_3343_);
lean_closure_set(v___f_3350_, 3, v___x_3348_);
lean_closure_set(v___f_3350_, 4, v___f_3349_);
v___f_3351_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3351_, 0, v___x_3347_);
lean_closure_set(v___f_3351_, 1, v_toProcessingContext_3346_);
if (lean_obj_tag(v_old_x3f_3343_) == 1)
{
lean_object* v_val_3352_; lean_object* v_result_x3f_3353_; 
v_val_3352_ = lean_ctor_get(v_old_x3f_3343_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v_old_x3f_3343_, 1);
v_result_x3f_3353_ = lean_ctor_get(v_val_3352_, 4);
if (lean_obj_tag(v_result_x3f_3353_) == 1)
{
lean_object* v_stx_3354_; lean_object* v_val_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_stx_3354_ = lean_ctor_get(v_val_3352_, 3);
lean_inc(v_stx_3354_);
v_val_3355_ = lean_ctor_get(v_result_x3f_3353_, 0);
lean_inc(v_val_3352_);
v___x_3356_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3352_);
v___x_3357_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3356_);
if (lean_obj_tag(v___x_3357_) == 1)
{
lean_object* v_val_3358_; 
v_val_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___x_3357_, 1);
if (lean_obj_tag(v_val_3358_) == 1)
{
lean_object* v_val_3359_; lean_object* v_firstCmdSnap_3360_; lean_object* v___x_3361_; 
v_val_3359_ = lean_ctor_get(v_val_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v_val_3358_, 1);
v_firstCmdSnap_3360_ = lean_ctor_get(v_val_3359_, 1);
lean_inc_ref(v_firstCmdSnap_3360_);
lean_dec(v_val_3359_);
v___x_3361_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3360_);
if (lean_obj_tag(v___x_3361_) == 1)
{
lean_object* v_val_3362_; lean_object* v_nextCmdSnap_x3f_3363_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v_nextCmdSnap_x3f_3363_ = lean_ctor_get(v_val_3362_, 4);
lean_inc(v_nextCmdSnap_x3f_3363_);
lean_dec(v_val_3362_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3363_) == 0)
{
lean_object* v___x_3364_; 
lean_dec(v_stx_3354_);
lean_dec(v_val_3352_);
v___x_3364_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3364_;
}
else
{
lean_object* v_val_3365_; lean_object* v___x_3366_; 
v_val_3365_ = lean_ctor_get(v_nextCmdSnap_x3f_3363_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3363_, 1);
v___x_3366_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3365_);
if (lean_obj_tag(v___x_3366_) == 1)
{
lean_object* v_val_3367_; lean_object* v_parserState_3368_; lean_object* v_pos_3369_; uint8_t v___x_3370_; 
v_val_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v_parserState_3368_ = lean_ctor_get(v_val_3367_, 2);
lean_inc_ref(v_parserState_3368_);
lean_dec(v_val_3367_);
v_pos_3369_ = lean_ctor_get(v_parserState_3368_, 0);
lean_inc(v_pos_3369_);
lean_dec_ref(v_parserState_3368_);
v___x_3370_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3369_, v_a_3344_);
lean_dec(v_pos_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_dec(v_stx_3354_);
lean_dec(v_val_3352_);
v___x_3371_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3371_;
}
else
{
lean_object* v_parserState_3372_; lean_object* v___x_3373_; 
lean_dec_ref(v___f_3351_);
lean_dec_ref(v___f_3350_);
v_parserState_3372_ = lean_ctor_get(v_val_3355_, 0);
lean_inc_ref(v_parserState_3372_);
lean_inc_ref(v_toProcessingContext_3346_);
v___x_3373_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3346_, v_a_3344_, v_val_3352_, v_stx_3354_, v_parserState_3372_, v_a_3344_);
return v___x_3373_;
}
}
else
{
lean_object* v___x_3374_; 
lean_dec(v___x_3366_);
lean_dec(v_stx_3354_);
lean_dec(v_val_3352_);
v___x_3374_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3374_;
}
}
}
else
{
lean_object* v___x_3375_; 
lean_dec(v___x_3361_);
lean_dec(v_stx_3354_);
lean_dec(v_val_3352_);
v___x_3375_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3375_;
}
}
else
{
lean_object* v___x_3376_; 
lean_dec(v_val_3358_);
lean_dec(v_stx_3354_);
lean_dec(v_val_3352_);
v___x_3376_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3376_;
}
}
else
{
lean_object* v___x_3377_; 
lean_dec(v___x_3357_);
lean_dec(v_stx_3354_);
lean_dec(v_val_3352_);
v___x_3377_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3377_;
}
}
else
{
lean_object* v___x_3378_; 
lean_dec(v_val_3352_);
v___x_3378_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3378_;
}
}
else
{
lean_object* v___x_3379_; 
lean_dec(v_old_x3f_3343_);
v___x_3379_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3351_, v___f_3350_, v_a_3344_);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3380_, lean_object* v_old_x3f_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3380_, v_old_x3f_3381_, v_a_3382_);
lean_dec_ref(v_a_3382_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3385_, lean_object* v_old_x3f_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v___x_3389_; 
lean_inc(v_old_x3f_3386_);
v___x_3389_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3389_, 0, v_setupImports_3385_);
lean_closure_set(v___x_3389_, 1, v_old_x3f_3386_);
if (lean_obj_tag(v_old_x3f_3386_) == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_box(0);
v___x_3391_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3389_, v___x_3390_, v_a_3387_);
return v___x_3391_;
}
else
{
lean_object* v_val_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3401_; 
v_val_3392_ = lean_ctor_get(v_old_x3f_3386_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_old_x3f_3386_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3394_ = v_old_x3f_3386_;
v_isShared_3395_ = v_isSharedCheck_3401_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_val_3392_);
lean_dec(v_old_x3f_3386_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3401_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_ictx_3396_; lean_object* v___x_3398_; 
v_ictx_3396_ = lean_ctor_get(v_val_3392_, 2);
lean_inc_ref(v_ictx_3396_);
lean_dec(v_val_3392_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v_ictx_3396_);
v___x_3398_ = v___x_3394_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_ictx_3396_);
v___x_3398_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3389_, v___x_3398_, v_a_3387_);
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3402_, lean_object* v_old_x3f_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_Language_Lean_process(v_setupImports_3402_, v_old_x3f_3403_, v_a_3404_);
lean_dec_ref(v_a_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3407_, lean_object* v_parserState_3408_, lean_object* v_commandState_3409_, lean_object* v_old_x3f_3410_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3420_; 
v___x_3412_ = lean_io_promise_new();
v___x_3413_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3410_) == 0)
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_box(0);
v___y_3420_ = v___x_3435_;
goto v___jp_3419_;
}
else
{
lean_object* v_val_3436_; lean_object* v_snd_3437_; lean_object* v___x_3438_; 
v_val_3436_ = lean_ctor_get(v_old_x3f_3410_, 0);
v_snd_3437_ = lean_ctor_get(v_val_3436_, 1);
lean_inc(v_snd_3437_);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v_snd_3437_);
v___y_3420_ = v___x_3438_;
goto v___jp_3419_;
}
v___jp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3415_, v___y_3416_, v_inputCtx_3407_);
lean_dec(v___x_3417_);
v___x_3418_ = l_IO_Promise_result_x21___redArg(v___x_3412_);
lean_dec(v___x_3412_);
return v___x_3418_;
}
v___jp_3419_:
{
uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3421_ = 1;
v___x_3422_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
v___x_3423_ = lean_box(v___x_3421_);
lean_inc(v___x_3412_);
v___x_3424_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3424_, 0, v___y_3420_);
lean_closure_set(v___x_3424_, 1, v_parserState_3408_);
lean_closure_set(v___x_3424_, 2, v_commandState_3409_);
lean_closure_set(v___x_3424_, 3, v___x_3412_);
lean_closure_set(v___x_3424_, 4, v___x_3423_);
lean_closure_set(v___x_3424_, 5, v___x_3413_);
lean_closure_set(v___x_3424_, 6, v___x_3422_);
if (lean_obj_tag(v_old_x3f_3410_) == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_box(0);
v___y_3415_ = v___x_3424_;
v___y_3416_ = v___x_3425_;
goto v___jp_3414_;
}
else
{
lean_object* v_val_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3434_; 
v_val_3426_ = lean_ctor_get(v_old_x3f_3410_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_old_x3f_3410_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3428_ = v_old_x3f_3410_;
v_isShared_3429_ = v_isSharedCheck_3434_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_val_3426_);
lean_dec(v_old_x3f_3410_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3434_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_fst_3430_; lean_object* v___x_3432_; 
v_fst_3430_ = lean_ctor_get(v_val_3426_, 0);
lean_inc(v_fst_3430_);
lean_dec(v_val_3426_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v_fst_3430_);
v___x_3432_ = v___x_3428_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_fst_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
v___y_3415_ = v___x_3424_;
v___y_3416_ = v___x_3432_;
goto v___jp_3414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3439_, lean_object* v_parserState_3440_, lean_object* v_commandState_3441_, lean_object* v_old_x3f_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3439_, v_parserState_3440_, v_commandState_3441_, v_old_x3f_3442_);
lean_dec_ref(v_inputCtx_3439_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3445_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3446_; 
v_nextCmdSnap_x3f_3446_ = lean_ctor_get(v_snap_3445_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3446_) == 1)
{
lean_object* v_val_3447_; lean_object* v___x_3448_; 
lean_inc_ref(v_nextCmdSnap_x3f_3446_);
lean_dec_ref(v_snap_3445_);
v_val_3447_ = lean_ctor_get(v_nextCmdSnap_x3f_3446_, 0);
lean_inc(v_val_3447_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3446_, 1);
v___x_3448_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3447_);
v_snap_3445_ = v___x_3448_;
goto _start;
}
else
{
lean_object* v_elabSnap_3450_; lean_object* v_resultSnap_3451_; lean_object* v___x_3452_; lean_object* v_cmdState_3453_; lean_object* v___x_3454_; 
v_elabSnap_3450_ = lean_ctor_get(v_snap_3445_, 3);
lean_inc_ref(v_elabSnap_3450_);
lean_dec_ref(v_snap_3445_);
v_resultSnap_3451_ = lean_ctor_get(v_elabSnap_3450_, 2);
lean_inc_ref(v_resultSnap_3451_);
lean_dec_ref(v_elabSnap_3450_);
v___x_3452_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3451_);
v_cmdState_3453_ = lean_ctor_get(v___x_3452_, 1);
lean_inc_ref(v_cmdState_3453_);
lean_dec(v___x_3452_);
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v_cmdState_3453_);
return v___x_3454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3455_){
_start:
{
lean_object* v_result_x3f_3456_; 
v_result_x3f_3456_ = lean_ctor_get(v_snap_3455_, 4);
lean_inc(v_result_x3f_3456_);
lean_dec_ref(v_snap_3455_);
if (lean_obj_tag(v_result_x3f_3456_) == 0)
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_box(0);
return v___x_3457_;
}
else
{
lean_object* v_val_3458_; lean_object* v_processedSnap_3459_; lean_object* v___x_3460_; lean_object* v_result_x3f_3461_; 
v_val_3458_ = lean_ctor_get(v_result_x3f_3456_, 0);
lean_inc(v_val_3458_);
lean_dec_ref_known(v_result_x3f_3456_, 1);
v_processedSnap_3459_ = lean_ctor_get(v_val_3458_, 1);
lean_inc_ref(v_processedSnap_3459_);
lean_dec(v_val_3458_);
v___x_3460_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3459_);
v_result_x3f_3461_ = lean_ctor_get(v___x_3460_, 2);
lean_inc(v_result_x3f_3461_);
lean_dec(v___x_3460_);
if (lean_obj_tag(v_result_x3f_3461_) == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_box(0);
return v___x_3462_;
}
else
{
lean_object* v_val_3463_; lean_object* v_firstCmdSnap_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_val_3463_ = lean_ctor_get(v_result_x3f_3461_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v_result_x3f_3461_, 1);
v_firstCmdSnap_3464_ = lean_ctor_get(v_val_3463_, 1);
lean_inc_ref(v_firstCmdSnap_3464_);
lean_dec(v_val_3463_);
v___x_3465_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3464_);
v___x_3466_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3465_);
return v___x_3466_;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = 1;
v___x_3473_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3474_ = l_Lean_Name_toString(v___x_3473_, v___x_3472_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3475_ = 0;
v___x_3476_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3477_ = lean_box(0);
v___x_3478_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3479_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3480_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v___x_3478_);
lean_ctor_set(v___x_3480_, 2, v___x_3477_);
lean_ctor_set(v___x_3480_, 3, v___x_3476_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*4, v___x_3475_);
return v___x_3480_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3482_ = lean_box(0);
v___x_3483_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3482_, v___x_3481_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3484_){
_start:
{
lean_object* v_result_x3f_3485_; 
v_result_x3f_3485_ = lean_ctor_get(v_snap_3484_, 4);
lean_inc(v_result_x3f_3485_);
if (lean_obj_tag(v_result_x3f_3485_) == 1)
{
lean_object* v_val_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3560_; 
v_val_3486_ = lean_ctor_get(v_result_x3f_3485_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_result_x3f_3485_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3488_ = v_result_x3f_3485_;
v_isShared_3489_ = v_isSharedCheck_3560_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_val_3486_);
lean_dec(v_result_x3f_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3560_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_toSnapshot_3490_; lean_object* v_metaSnap_3491_; lean_object* v_ictx_3492_; lean_object* v_stx_3493_; lean_object* v_parserState_3494_; lean_object* v_processedSnap_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3559_; 
v_toSnapshot_3490_ = lean_ctor_get(v_snap_3484_, 0);
v_metaSnap_3491_ = lean_ctor_get(v_snap_3484_, 1);
v_ictx_3492_ = lean_ctor_get(v_snap_3484_, 2);
v_stx_3493_ = lean_ctor_get(v_snap_3484_, 3);
v_parserState_3494_ = lean_ctor_get(v_val_3486_, 0);
v_processedSnap_3495_ = lean_ctor_get(v_val_3486_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_val_3486_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3497_ = v_val_3486_;
v_isShared_3498_ = v_isSharedCheck_3559_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_processedSnap_3495_);
lean_inc(v_parserState_3494_);
lean_dec(v_val_3486_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3559_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v_processed_3499_; lean_object* v_result_x3f_3500_; 
v_processed_3499_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3495_);
v_result_x3f_3500_ = lean_ctor_get(v_processed_3499_, 2);
lean_inc(v_result_x3f_3500_);
if (lean_obj_tag(v_result_x3f_3500_) == 1)
{
lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3553_; 
lean_inc(v_stx_3493_);
lean_inc_ref(v_ictx_3492_);
lean_inc_ref(v_metaSnap_3491_);
lean_inc_ref(v_toSnapshot_3490_);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_snap_3484_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; lean_object* v_unused_3555_; lean_object* v_unused_3556_; lean_object* v_unused_3557_; lean_object* v_unused_3558_; 
v_unused_3554_ = lean_ctor_get(v_snap_3484_, 4);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_snap_3484_, 3);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_snap_3484_, 2);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_snap_3484_, 1);
lean_dec(v_unused_3557_);
v_unused_3558_ = lean_ctor_get(v_snap_3484_, 0);
lean_dec(v_unused_3558_);
v___x_3502_ = v_snap_3484_;
v_isShared_3503_ = v_isSharedCheck_3553_;
goto v_resetjp_3501_;
}
else
{
lean_dec(v_snap_3484_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3553_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_val_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3552_; 
v_val_3504_ = lean_ctor_get(v_result_x3f_3500_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_result_x3f_3500_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3506_ = v_result_x3f_3500_;
v_isShared_3507_ = v_isSharedCheck_3552_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_val_3504_);
lean_dec(v_result_x3f_3500_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3552_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_toSnapshot_3508_; lean_object* v_metaSnap_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3550_; 
v_toSnapshot_3508_ = lean_ctor_get(v_processed_3499_, 0);
v_metaSnap_3509_ = lean_ctor_get(v_processed_3499_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_processed_3499_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; 
v_unused_3551_ = lean_ctor_get(v_processed_3499_, 2);
lean_dec(v_unused_3551_);
v___x_3511_ = v_processed_3499_;
v_isShared_3512_ = v_isSharedCheck_3550_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_metaSnap_3509_);
lean_inc(v_toSnapshot_3508_);
lean_dec(v_processed_3499_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3550_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_cmdState_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3548_; 
v_cmdState_3513_ = lean_ctor_get(v_val_3504_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_val_3504_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; 
v_unused_3549_ = lean_ctor_get(v_val_3504_, 1);
lean_dec(v_unused_3549_);
v___x_3515_ = v_val_3504_;
v_isShared_3516_ = v_isSharedCheck_3548_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_cmdState_3513_);
lean_dec(v_val_3504_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3548_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_resultSnap_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v_elabSnap_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_termCmd_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3517_ = lean_box(0);
v___x_3518_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
lean_inc_ref(v_cmdState_3513_);
v_resultSnap_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_resultSnap_3519_, 0, v___x_3518_);
lean_ctor_set(v_resultSnap_3519_, 1, v_cmdState_3513_);
v___x_3520_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3521_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3517_, v_resultSnap_3519_);
v___x_3522_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3523_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4);
v_elabSnap_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3524_, 0, v___x_3518_);
lean_ctor_set(v_elabSnap_3524_, 1, v___x_3520_);
lean_ctor_set(v_elabSnap_3524_, 2, v___x_3521_);
lean_ctor_set(v_elabSnap_3524_, 3, v___x_3522_);
lean_ctor_set(v_elabSnap_3524_, 4, v___x_3523_);
v___x_3525_ = lean_box(0);
v___x_3526_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3527_, 0, v___x_3518_);
lean_ctor_set(v_termCmd_3527_, 1, v___x_3525_);
lean_ctor_set(v_termCmd_3527_, 2, v___x_3526_);
lean_ctor_set(v_termCmd_3527_, 3, v_elabSnap_3524_);
lean_ctor_set(v_termCmd_3527_, 4, v___x_3517_);
v___x_3528_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3517_, v_termCmd_3527_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 1, v___x_3528_);
v___x_3530_ = v___x_3515_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_cmdState_3513_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3530_);
v___x_3532_ = v___x_3506_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v_newProcessed_3534_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 2, v___x_3532_);
v_newProcessed_3534_ = v___x_3511_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_toSnapshot_3508_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_metaSnap_3509_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v___x_3532_);
v_newProcessed_3534_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3517_, v_newProcessed_3534_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 1, v___x_3535_);
v___x_3537_ = v___x_3497_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_parserState_3494_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
lean_object* v___x_3539_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3537_);
v___x_3539_ = v___x_3488_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 4, v___x_3539_);
v___x_3541_ = v___x_3502_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_toSnapshot_3490_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_metaSnap_3491_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_ictx_3492_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v_stx_3493_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
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
lean_dec(v_result_x3f_3500_);
lean_dec(v_processed_3499_);
lean_del_object(v___x_3497_);
lean_dec_ref(v_parserState_3494_);
lean_del_object(v___x_3488_);
return v_snap_3484_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3485_);
return v_snap_3484_;
}
}
}
lean_object* runtime_initialize_Lean_Language_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
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

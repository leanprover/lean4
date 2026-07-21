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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
extern lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
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
lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*);
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
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
extern lean_object* l_Lean_internal_cmdlineSnapshots;
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
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_eqWithInfo(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
lean_object* l_Lean_List_toPArray_x27___redArg(lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler_output;
extern lean_object* l_Lean_trace_profiler_serve;
extern lean_object* l_Lean_instInhabitedTraceState_default;
lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object*, lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parseCmd"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_value;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "snapshotTree"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 136, 72, 78, 187, 126, 217, 153)}};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3;
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object**);
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parsing"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5_value;
static const lean_closure_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_dec_ref_known(v___x_121_, 1);
return v_a_122_;
}
else
{
lean_object* v_a_123_; lean_object* v_toProcessingContext_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_123_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_121_, 1);
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
lean_dec_ref_known(v_defValue_227_, 0);
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
lean_dec_ref_known(v___x_247_, 3);
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
lean_dec_ref_known(v_x_317_, 5);
v___x_327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_315_, v_init_316_, v_l_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
if (lean_obj_tag(v_a_328_) == 0)
{
lean_object* v_a_329_; 
lean_dec_ref_known(v___x_327_, 1);
lean_dec(v_r_326_);
lean_dec(v_v_324_);
lean_dec(v_k_323_);
v_a_329_ = lean_ctor_get(v_a_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_a_328_, 1);
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
lean_dec_ref_known(v___x_327_, 1);
if (lean_obj_tag(v_v_324_) == 0)
{
lean_object* v_val_339_; lean_object* v_v_340_; lean_object* v___x_341_; 
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v___x_338_, 1);
v_v_340_ = lean_ctor_get(v_v_324_, 0);
lean_inc_ref(v_v_340_);
lean_dec_ref_known(v_v_324_, 1);
v___x_341_ = l_Lean_Language_Lean_setOption(v_a_330_, v_val_339_, v___x_337_, v_v_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
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
lean_dec_ref_known(v___x_338_, 1);
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
lean_dec_ref_known(v___x_327_, 1);
if (lean_obj_tag(v_a_377_) == 0)
{
lean_object* v_a_378_; 
lean_dec(v_r_326_);
v_a_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v_a_377_, 1);
v_d_320_ = v_a_378_;
goto v___jp_319_;
}
else
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v_a_377_, 1);
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
lean_dec_ref_known(v___x_391_, 1);
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
lean_object* v___x_510_; lean_object* v_infoState_511_; lean_object* v_trees_512_; lean_object* v___x_513_; lean_object* v_infoState_514_; lean_object* v_env_515_; lean_object* v_messages_516_; lean_object* v_scopes_517_; lean_object* v_usedQuotCtxts_518_; lean_object* v_nextMacroScope_519_; lean_object* v_maxRecDepth_520_; lean_object* v_ngen_521_; lean_object* v_auxDeclNGen_522_; lean_object* v_traceState_523_; lean_object* v_snapshotTasks_524_; lean_object* v_prevLinterStates_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_546_; 
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
v_prevLinterStates_525_ = lean_ctor_get(v___x_513_, 11);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_546_ == 0)
{
v___x_527_ = v___x_513_;
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_prevLinterStates_525_);
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
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_546_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v_enabled_529_; lean_object* v_assignment_530_; lean_object* v_lazyAssignment_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_544_; 
v_enabled_529_ = lean_ctor_get_uint8(v_infoState_514_, sizeof(void*)*3);
v_assignment_530_ = lean_ctor_get(v_infoState_514_, 0);
v_lazyAssignment_531_ = lean_ctor_get(v_infoState_514_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_infoState_514_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_infoState_514_, 2);
lean_dec(v_unused_545_);
v___x_533_ = v_infoState_514_;
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_lazyAssignment_531_);
lean_inc(v_assignment_530_);
lean_dec(v_infoState_514_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_544_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_assignment_530_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_lazyAssignment_531_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v___x_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_543_, sizeof(void*)*3, v_enabled_529_);
v___x_537_ = v_reuseFailAlloc_543_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 8, v___x_537_);
v___x_539_ = v___x_527_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_env_515_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_messages_516_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_scopes_517_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_usedQuotCtxts_518_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_542_, 5, v_maxRecDepth_520_);
lean_ctor_set(v_reuseFailAlloc_542_, 6, v_ngen_521_);
lean_ctor_set(v_reuseFailAlloc_542_, 7, v_auxDeclNGen_522_);
lean_ctor_set(v_reuseFailAlloc_542_, 8, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_542_, 9, v_traceState_523_);
lean_ctor_set(v_reuseFailAlloc_542_, 10, v_snapshotTasks_524_);
lean_ctor_set(v_reuseFailAlloc_542_, 11, v_prevLinterStates_525_);
v___x_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_st_ref_set(v___y_508_, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_trees_512_);
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_547_);
lean_dec(v___y_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_557_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_558_, lean_object* v_opt_559_){
_start:
{
lean_object* v_name_560_; lean_object* v_defValue_561_; lean_object* v_map_562_; lean_object* v___x_563_; 
v_name_560_ = lean_ctor_get(v_opt_559_, 0);
v_defValue_561_ = lean_ctor_get(v_opt_559_, 1);
v_map_562_ = lean_ctor_get(v_opts_558_, 0);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_562_, v_name_560_);
if (lean_obj_tag(v___x_563_) == 0)
{
uint8_t v___x_564_; 
v___x_564_ = lean_unbox(v_defValue_561_);
return v___x_564_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v___x_563_, 1);
if (lean_obj_tag(v_val_565_) == 1)
{
uint8_t v_v_566_; 
v_v_566_ = lean_ctor_get_uint8(v_val_565_, 0);
lean_dec_ref_known(v_val_565_, 0);
return v_v_566_;
}
else
{
uint8_t v___x_567_; 
lean_dec(v_val_565_);
v___x_567_ = lean_unbox(v_defValue_561_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_568_, lean_object* v_opt_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_568_, v_opt_569_);
lean_dec_ref(v_opt_569_);
lean_dec_ref(v_opts_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = l_Lean_Language_Snapshot_transform(v_val_574_, v___y_575_);
v___x_577_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_579_, v___y_580_);
lean_dec_ref(v___y_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_582_, lean_object* v_val_583_){
_start:
{
lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_inc_ref(v_val_583_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_584_, 0, v_val_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_inst_582_);
lean_ctor_set(v___x_585_, 1, v_val_583_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___f_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_587_, lean_object* v_cmds_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_590_);
lean_dec_ref(v___x_592_);
v___x_593_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_587_, v_cmds_588_, v___y_589_, v___y_590_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_594_, lean_object* v_cmds_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_594_, v_cmds_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_600_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_ctor_set(v___x_605_, 2, v___x_604_);
lean_ctor_set(v___x_605_, 3, v___x_604_);
lean_ctor_set(v___x_605_, 4, v___x_603_);
lean_ctor_set(v___x_605_, 5, v___x_603_);
lean_ctor_set(v___x_605_, 6, v___x_603_);
lean_ctor_set(v___x_605_, 7, v___x_603_);
lean_ctor_set(v___x_605_, 8, v___x_603_);
lean_ctor_set(v___x_605_, 9, v___x_603_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_unsigned_to_nat(32u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_609_ = ((size_t)5ULL);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_unsigned_to_nat(32u);
v___x_612_ = lean_mk_empty_array_with_capacity(v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_614_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_610_);
lean_ctor_set(v___x_614_, 3, v___x_610_);
lean_ctor_set_usize(v___x_614_, 4, v___x_609_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_box(1);
v___x_616_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_617_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
lean_ctor_set(v___x_618_, 2, v___x_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_env_623_; lean_object* v___x_624_; lean_object* v_scopes_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_opts_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_622_ = lean_st_ref_get(v___y_620_);
v_env_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_622_);
v___x_624_ = lean_st_ref_get(v___y_620_);
v_scopes_625_ = lean_ctor_get(v___x_624_, 2);
lean_inc(v_scopes_625_);
lean_dec(v___x_624_);
v___x_626_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_627_ = l_List_head_x21___redArg(v___x_626_, v_scopes_625_);
lean_dec(v_scopes_625_);
v_opts_628_ = lean_ctor_get(v___x_627_, 1);
lean_inc_ref(v_opts_628_);
lean_dec(v___x_627_);
v___x_629_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_630_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_631_, 0, v_env_623_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
lean_ctor_set(v___x_631_, 3, v_opts_628_);
v___x_632_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v_msgData_619_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_634_, v___y_635_);
lean_dec(v___y_635_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_638_, uint8_t v_suppressElabErrors_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 1)
{
lean_object* v_pre_641_; 
v_pre_641_ = lean_ctor_get(v_x_640_, 0);
if (lean_obj_tag(v_pre_641_) == 0)
{
lean_object* v_str_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_str_642_ = lean_ctor_get(v_x_640_, 1);
v___x_643_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_644_ = lean_string_dec_eq(v_str_642_, v___x_643_);
if (v___x_644_ == 0)
{
return v___y_638_;
}
else
{
return v_suppressElabErrors_639_;
}
}
else
{
return v___y_638_;
}
}
else
{
return v___y_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_645_, lean_object* v_suppressElabErrors_646_, lean_object* v_x_647_){
_start:
{
uint8_t v___y_9217__boxed_648_; uint8_t v_suppressElabErrors_boxed_649_; uint8_t v_res_650_; lean_object* v_r_651_; 
v___y_9217__boxed_648_ = lean_unbox(v___y_645_);
v_suppressElabErrors_boxed_649_ = lean_unbox(v_suppressElabErrors_646_);
v_res_650_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9217__boxed_648_, v_suppressElabErrors_boxed_649_, v_x_647_);
lean_dec(v_x_647_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_653_, lean_object* v_msgData_654_, uint8_t v_severity_655_, uint8_t v_isSilent_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
uint8_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; uint8_t v___y_753_; uint8_t v___y_754_; uint8_t v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; uint8_t v___y_761_; uint8_t v___y_762_; uint8_t v___y_763_; uint8_t v___x_778_; uint8_t v___y_780_; uint8_t v___y_781_; uint8_t v___y_782_; uint8_t v___y_784_; uint8_t v___x_796_; 
v___x_778_ = 2;
v___x_796_ = l_Lean_instBEqMessageSeverity_beq(v_severity_655_, v___x_778_);
if (v___x_796_ == 0)
{
v___y_784_ = v___x_796_;
goto v___jp_783_;
}
else
{
uint8_t v___x_797_; 
lean_inc_ref(v_msgData_654_);
v___x_797_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_654_);
v___y_784_ = v___x_797_;
goto v___jp_783_;
}
v___jp_660_:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Elab_Command_getScope___redArg(v___y_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_Elab_Command_getScope___redArg(v___y_668_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_707_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_707_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_707_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_707_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v_currNamespace_677_; lean_object* v_openDecls_678_; lean_object* v_env_679_; lean_object* v_messages_680_; lean_object* v_scopes_681_; lean_object* v_usedQuotCtxts_682_; lean_object* v_nextMacroScope_683_; lean_object* v_maxRecDepth_684_; lean_object* v_ngen_685_; lean_object* v_auxDeclNGen_686_; lean_object* v_infoState_687_; lean_object* v_traceState_688_; lean_object* v_snapshotTasks_689_; lean_object* v_prevLinterStates_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_706_; 
v___x_676_ = lean_st_ref_take(v___y_668_);
v_currNamespace_677_ = lean_ctor_get(v_a_670_, 2);
lean_inc(v_currNamespace_677_);
lean_dec(v_a_670_);
v_openDecls_678_ = lean_ctor_get(v_a_672_, 3);
lean_inc(v_openDecls_678_);
lean_dec(v_a_672_);
v_env_679_ = lean_ctor_get(v___x_676_, 0);
v_messages_680_ = lean_ctor_get(v___x_676_, 1);
v_scopes_681_ = lean_ctor_get(v___x_676_, 2);
v_usedQuotCtxts_682_ = lean_ctor_get(v___x_676_, 3);
v_nextMacroScope_683_ = lean_ctor_get(v___x_676_, 4);
v_maxRecDepth_684_ = lean_ctor_get(v___x_676_, 5);
v_ngen_685_ = lean_ctor_get(v___x_676_, 6);
v_auxDeclNGen_686_ = lean_ctor_get(v___x_676_, 7);
v_infoState_687_ = lean_ctor_get(v___x_676_, 8);
v_traceState_688_ = lean_ctor_get(v___x_676_, 9);
v_snapshotTasks_689_ = lean_ctor_get(v___x_676_, 10);
v_prevLinterStates_690_ = lean_ctor_get(v___x_676_, 11);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_706_ == 0)
{
v___x_692_ = v___x_676_;
v_isShared_693_ = v_isSharedCheck_706_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_prevLinterStates_690_);
lean_inc(v_snapshotTasks_689_);
lean_inc(v_traceState_688_);
lean_inc(v_infoState_687_);
lean_inc(v_auxDeclNGen_686_);
lean_inc(v_ngen_685_);
lean_inc(v_maxRecDepth_684_);
lean_inc(v_nextMacroScope_683_);
lean_inc(v_usedQuotCtxts_682_);
lean_inc(v_scopes_681_);
lean_inc(v_messages_680_);
lean_inc(v_env_679_);
lean_dec(v___x_676_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_706_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_currNamespace_677_);
lean_ctor_set(v___x_694_, 1, v_openDecls_678_);
v___x_695_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___y_663_);
lean_inc_ref(v___y_662_);
lean_inc_ref(v___y_665_);
v___x_696_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_696_, 0, v___y_665_);
lean_ctor_set(v___x_696_, 1, v___y_667_);
lean_ctor_set(v___x_696_, 2, v___y_664_);
lean_ctor_set(v___x_696_, 3, v___y_662_);
lean_ctor_set(v___x_696_, 4, v___x_695_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*5, v___y_666_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*5 + 1, v___y_661_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*5 + 2, v_isSilent_656_);
v___x_697_ = l_Lean_MessageLog_add(v___x_696_, v_messages_680_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_697_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_env_679_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_scopes_681_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_usedQuotCtxts_682_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_nextMacroScope_683_);
lean_ctor_set(v_reuseFailAlloc_705_, 5, v_maxRecDepth_684_);
lean_ctor_set(v_reuseFailAlloc_705_, 6, v_ngen_685_);
lean_ctor_set(v_reuseFailAlloc_705_, 7, v_auxDeclNGen_686_);
lean_ctor_set(v_reuseFailAlloc_705_, 8, v_infoState_687_);
lean_ctor_set(v_reuseFailAlloc_705_, 9, v_traceState_688_);
lean_ctor_set(v_reuseFailAlloc_705_, 10, v_snapshotTasks_689_);
lean_ctor_set(v_reuseFailAlloc_705_, 11, v_prevLinterStates_690_);
v___x_699_ = v_reuseFailAlloc_705_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = lean_st_ref_set(v___y_668_, v___x_699_);
v___x_701_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_701_);
v___x_703_ = v___x_674_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_a_670_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
v_a_708_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_671_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_671_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___y_667_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
v_a_716_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_669_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_669_);
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
v___jp_724_:
{
lean_object* v_fileName_730_; lean_object* v_fileMap_731_; uint8_t v_suppressElabErrors_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_751_; 
v_fileName_730_ = lean_ctor_get(v___y_657_, 0);
v_fileMap_731_ = lean_ctor_get(v___y_657_, 1);
v_suppressElabErrors_732_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*10);
v___x_733_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_654_);
v___x_734_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_733_, v___y_658_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_751_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_751_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_751_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc_ref_n(v_fileMap_731_, 2);
v___x_739_ = l_Lean_FileMap_toPosition(v_fileMap_731_, v___y_726_);
lean_dec(v___y_726_);
v___x_740_ = l_Lean_FileMap_toPosition(v_fileMap_731_, v___y_729_);
lean_dec(v___y_729_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_732_ == 0)
{
lean_del_object(v___x_737_);
v___y_661_ = v___y_727_;
v___y_662_ = v___x_742_;
v___y_663_ = v_a_735_;
v___y_664_ = v___x_741_;
v___y_665_ = v_fileName_730_;
v___y_666_ = v___y_728_;
v___y_667_ = v___x_739_;
v___y_668_ = v___y_658_;
goto v___jp_660_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; uint8_t v___x_746_; 
v___x_743_ = lean_box(v___y_725_);
v___x_744_ = lean_box(v_suppressElabErrors_732_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_745_, 0, v___x_743_);
lean_closure_set(v___f_745_, 1, v___x_744_);
lean_inc(v_a_735_);
v___x_746_ = l_Lean_MessageData_hasTag(v___f_745_, v_a_735_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec_ref_known(v___x_741_, 1);
lean_dec_ref(v___x_739_);
lean_dec(v_a_735_);
v___x_747_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_747_);
v___x_749_ = v___x_737_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_del_object(v___x_737_);
v___y_661_ = v___y_727_;
v___y_662_ = v___x_742_;
v___y_663_ = v_a_735_;
v___y_664_ = v___x_741_;
v___y_665_ = v_fileName_730_;
v___y_666_ = v___y_728_;
v___y_667_ = v___x_739_;
v___y_668_ = v___y_658_;
goto v___jp_660_;
}
}
}
}
v___jp_752_:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Syntax_getTailPos_x3f(v___y_756_, v___y_755_);
lean_dec(v___y_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_inc(v___y_757_);
v___y_725_ = v___y_753_;
v___y_726_ = v___y_757_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_757_;
goto v___jp_724_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_758_, 1);
v___y_725_ = v___y_753_;
v___y_726_ = v___y_757_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v_val_759_;
goto v___jp_724_;
}
}
v___jp_760_:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Elab_Command_getRef___redArg(v___y_657_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_ref_766_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_ref_766_ = l_Lean_replaceRef(v_ref_653_, v_a_765_);
lean_dec(v_a_765_);
v___x_767_ = l_Lean_Syntax_getPos_x3f(v_ref_766_, v___y_762_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_768_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___y_753_ = v___y_761_;
v___y_754_ = v___y_763_;
v___y_755_ = v___y_762_;
v___y_756_ = v_ref_766_;
v___y_757_ = v___x_768_;
goto v___jp_752_;
}
else
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_767_, 1);
v___y_753_ = v___y_761_;
v___y_754_ = v___y_763_;
v___y_755_ = v___y_762_;
v___y_756_ = v_ref_766_;
v___y_757_ = v_val_769_;
goto v___jp_752_;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_msgData_654_);
v_a_770_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_764_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_764_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
v___jp_779_:
{
if (v___y_782_ == 0)
{
v___y_761_ = v___y_780_;
v___y_762_ = v___y_781_;
v___y_763_ = v_severity_655_;
goto v___jp_760_;
}
else
{
v___y_761_ = v___y_780_;
v___y_762_ = v___y_781_;
v___y_763_ = v___x_778_;
goto v___jp_760_;
}
}
v___jp_783_:
{
if (v___y_784_ == 0)
{
lean_object* v___x_785_; lean_object* v_scopes_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_opts_789_; uint8_t v___x_790_; uint8_t v___x_791_; 
v___x_785_ = lean_st_ref_get(v___y_658_);
v_scopes_786_ = lean_ctor_get(v___x_785_, 2);
lean_inc(v_scopes_786_);
lean_dec(v___x_785_);
v___x_787_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_788_ = l_List_head_x21___redArg(v___x_787_, v_scopes_786_);
lean_dec(v_scopes_786_);
v_opts_789_ = lean_ctor_get(v___x_788_, 1);
lean_inc_ref(v_opts_789_);
lean_dec(v___x_788_);
v___x_790_ = 1;
v___x_791_ = l_Lean_instBEqMessageSeverity_beq(v_severity_655_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec_ref(v_opts_789_);
v___y_780_ = v___y_784_;
v___y_781_ = v___y_784_;
v___y_782_ = v___x_791_;
goto v___jp_779_;
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = l_Lean_warningAsError;
v___x_793_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_789_, v___x_792_);
lean_dec_ref(v_opts_789_);
v___y_780_ = v___y_784_;
v___y_781_ = v___y_784_;
v___y_782_ = v___x_793_;
goto v___jp_779_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref(v_msgData_654_);
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_798_, lean_object* v_msgData_799_, lean_object* v_severity_800_, lean_object* v_isSilent_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
uint8_t v_severity_boxed_805_; uint8_t v_isSilent_boxed_806_; lean_object* v_res_807_; 
v_severity_boxed_805_ = lean_unbox(v_severity_800_);
v_isSilent_boxed_806_ = lean_unbox(v_isSilent_801_);
v_res_807_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_798_, v_msgData_799_, v_severity_boxed_805_, v_isSilent_boxed_806_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v_ref_798_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_808_, uint8_t v_severity_809_, uint8_t v_isSilent_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Elab_Command_getRef___redArg(v___y_811_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_815_, v_msgData_808_, v_severity_809_, v_isSilent_810_, v___y_811_, v___y_812_);
lean_dec(v_a_815_);
return v___x_816_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_msgData_808_);
v_a_817_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_814_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_825_, lean_object* v_severity_826_, lean_object* v_isSilent_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v_severity_boxed_831_; uint8_t v_isSilent_boxed_832_; lean_object* v_res_833_; 
v_severity_boxed_831_ = lean_unbox(v_severity_826_);
v_isSilent_boxed_832_ = lean_unbox(v_isSilent_827_);
v_res_833_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_825_, v_severity_boxed_831_, v_isSilent_boxed_832_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 2;
v___x_839_ = 0;
v___x_840_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_834_, v___x_838_, v___x_839_, v___y_835_, v___y_836_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_846_, lean_object* v_msgData_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v___x_851_; uint8_t v___x_852_; lean_object* v___x_853_; 
v___x_851_ = 2;
v___x_852_ = 0;
v___x_853_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_846_, v_msgData_847_, v___x_851_, v___x_852_, v___y_848_, v___y_849_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_854_, lean_object* v_msgData_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_854_, v_msgData_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v_ref_854_);
return v_res_859_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
if (lean_obj_tag(v_ex_863_) == 0)
{
lean_object* v_ref_867_; lean_object* v_msg_868_; lean_object* v___x_869_; 
v_ref_867_ = lean_ctor_get(v_ex_863_, 0);
lean_inc(v_ref_867_);
v_msg_868_ = lean_ctor_get(v_ex_863_, 1);
lean_inc_ref(v_msg_868_);
lean_dec_ref_known(v_ex_863_, 2);
v___x_869_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_867_, v_msg_868_, v___y_864_, v___y_865_);
lean_dec(v_ref_867_);
return v___x_869_;
}
else
{
lean_object* v_id_870_; uint8_t v___y_872_; uint8_t v___x_894_; 
v_id_870_ = lean_ctor_get(v_ex_863_, 0);
lean_inc(v_id_870_);
v___x_894_ = l_Lean_Elab_isAbortExceptionId(v_id_870_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_Exception_isInterrupt(v_ex_863_);
lean_dec_ref_known(v_ex_863_, 2);
v___y_872_ = v___x_895_;
goto v___jp_871_;
}
else
{
lean_dec_ref_known(v_ex_863_, 2);
v___y_872_ = v___x_894_;
goto v___jp_871_;
}
v___jp_871_:
{
if (v___y_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_InternalExceptionId_getName(v_id_870_);
lean_dec(v_id_870_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_876_ = l_Lean_MessageData_ofName(v_a_874_);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_877_, v___y_864_, v___y_865_);
return v___x_878_;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_a_879_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v___x_873_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_873_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_ref_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v_ref_883_ = lean_ctor_get(v___y_864_, 7);
v___x_884_ = lean_io_error_to_string(v_a_879_);
v___x_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
v___x_886_ = l_Lean_MessageData_ofFormat(v___x_885_);
lean_inc(v_ref_883_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_ref_883_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_887_);
v___x_889_ = v___x_881_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v_id_870_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
v___x_905_ = lean_apply_3(v_x_901_, v___y_902_, v___y_903_, lean_box(0));
if (lean_obj_tag(v___x_905_) == 0)
{
return v___x_905_;
}
else
{
lean_object* v_a_906_; uint8_t v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
v___x_907_ = l_Lean_Exception_isInterrupt(v_a_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec_ref_known(v___x_905_, 1);
v___x_908_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_906_, v___y_902_, v___y_903_);
return v___x_908_;
}
else
{
lean_dec(v_a_906_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_914_, lean_object* v___x_915_, lean_object* v_val_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_a_920_; lean_object* v___x_922_; 
v___x_922_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_914_, v___x_915_, v_val_916_);
if (lean_obj_tag(v___x_922_) == 0)
{
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v_a_920_ = v_a_923_;
goto v___jp_919_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v___x_932_; 
lean_dec_ref_known(v___x_922_, 1);
v___x_932_ = lean_box(0);
v_a_920_ = v___x_932_;
goto v___jp_919_;
}
v___jp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v_a_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_933_, lean_object* v___x_934_, lean_object* v_val_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_933_, v___x_934_, v_val_935_, v___y_936_);
lean_dec_ref(v___y_936_);
lean_dec(v_val_935_);
lean_dec_ref(v___x_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_939_, lean_object* v_x_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_get_set_stderr(v_h_939_);
lean_inc_ref(v___y_941_);
v___x_944_ = lean_apply_2(v_x_940_, v___y_941_, lean_box(0));
v___x_945_ = lean_get_set_stderr(v___x_943_);
lean_dec_ref(v___x_945_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_946_, lean_object* v_x_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_946_, v_x_947_, v___y_948_);
lean_dec_ref(v___y_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_951_, lean_object* v_h_952_, lean_object* v_x_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_952_, v_x_953_, v___y_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_957_, lean_object* v_h_958_, lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_957_, v_h_958_, v_x_959_, v___y_960_);
lean_dec_ref(v___y_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_963_, lean_object* v_x_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_get_set_stdin(v_h_963_);
lean_inc_ref(v___y_965_);
v___x_968_ = lean_apply_2(v_x_964_, v___y_965_, lean_box(0));
v___x_969_ = lean_get_set_stdin(v___x_967_);
lean_dec_ref(v___x_969_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_970_, lean_object* v_x_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_970_, v_x_971_, v___y_972_);
lean_dec_ref(v___y_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_977_ = lean_panic_fn_borrowed(v___x_976_, v_msg_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_978_, lean_object* v_x_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_get_set_stdout(v_h_978_);
lean_inc_ref(v___y_980_);
v___x_983_ = lean_apply_2(v_x_979_, v___y_980_, lean_box(0));
v___x_984_ = lean_get_set_stdout(v___x_982_);
lean_dec_ref(v___x_984_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_985_, v_x_986_, v___y_987_);
lean_dec_ref(v___y_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_990_, lean_object* v_h_991_, lean_object* v_x_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_991_, v_x_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_996_, lean_object* v_h_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_996_, v_h_997_, v_x_998_, v___y_999_);
lean_dec_ref(v___y_999_);
return v_res_1001_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = l_ByteArray_empty;
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1008_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1009_ = lean_unsigned_to_nat(46u);
v___x_1010_ = lean_unsigned_to_nat(193u);
v___x_1011_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1012_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1013_ = l_mkPanicMessageWithDecl(v___x_1012_, v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1014_, uint8_t v_isolateStderr_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___y_1028_; 
v___x_1022_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1023_ = lean_st_mk_ref(v___x_1022_);
v___x_1024_ = lean_st_mk_ref(v___x_1022_);
v___x_1025_ = l_IO_FS_Stream_ofBuffer(v___x_1023_);
lean_inc(v___x_1024_);
v___x_1026_ = l_IO_FS_Stream_ofBuffer(v___x_1024_);
if (v_isolateStderr_1015_ == 0)
{
v___y_1028_ = v_x_1014_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1037_; 
lean_inc_ref(v___x_1026_);
v___x_1037_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1037_, 0, lean_box(0));
lean_closure_set(v___x_1037_, 1, v___x_1026_);
lean_closure_set(v___x_1037_, 2, v_x_1014_);
v___y_1028_ = v___x_1037_;
goto v___jp_1027_;
}
v___jp_1018_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___y_1020_);
lean_ctor_set(v___x_1021_, 1, v___y_1019_);
return v___x_1021_;
}
v___jp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_data_1032_; uint8_t v___x_1033_; 
v___x_1029_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1029_, 0, lean_box(0));
lean_closure_set(v___x_1029_, 1, v___x_1026_);
lean_closure_set(v___x_1029_, 2, v___y_1028_);
v___x_1030_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1025_, v___x_1029_, v___y_1016_);
v___x_1031_ = lean_st_ref_get(v___x_1024_);
lean_dec(v___x_1024_);
v_data_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc_ref(v_data_1032_);
lean_dec(v___x_1031_);
v___x_1033_ = lean_string_validate_utf8(v_data_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref(v_data_1032_);
v___x_1034_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1035_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1034_);
v___y_1019_ = v___x_1030_;
v___y_1020_ = v___x_1035_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_string_from_utf8_unchecked(v_data_1032_);
v___y_1019_ = v___x_1030_;
v___y_1020_ = v___x_1036_;
goto v___jp_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1038_, lean_object* v_isolateStderr_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
uint8_t v_isolateStderr_boxed_1042_; lean_object* v_res_1043_; 
v_isolateStderr_boxed_1042_ = lean_unbox(v_isolateStderr_1039_);
v_res_1043_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1038_, v_isolateStderr_boxed_1042_, v___y_1040_);
lean_dec_ref(v___y_1040_);
return v_res_1043_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = 1;
v___x_1053_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1054_ = l_Lean_Name_toString(v___x_1053_, v___x_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1055_, lean_object* v_cmds_1056_, lean_object* v_cmdState_1057_, lean_object* v_beginPos_1058_, lean_object* v_snap_1059_, lean_object* v_cancelTk_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_env_1063_; lean_object* v_scopes_1064_; lean_object* v_usedQuotCtxts_1065_; lean_object* v_nextMacroScope_1066_; lean_object* v_maxRecDepth_1067_; lean_object* v_ngen_1068_; lean_object* v_auxDeclNGen_1069_; lean_object* v_infoState_1070_; lean_object* v_prevLinterStates_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1148_; 
v_env_1063_ = lean_ctor_get(v_cmdState_1057_, 0);
v_scopes_1064_ = lean_ctor_get(v_cmdState_1057_, 2);
v_usedQuotCtxts_1065_ = lean_ctor_get(v_cmdState_1057_, 3);
v_nextMacroScope_1066_ = lean_ctor_get(v_cmdState_1057_, 4);
v_maxRecDepth_1067_ = lean_ctor_get(v_cmdState_1057_, 5);
v_ngen_1068_ = lean_ctor_get(v_cmdState_1057_, 6);
v_auxDeclNGen_1069_ = lean_ctor_get(v_cmdState_1057_, 7);
v_infoState_1070_ = lean_ctor_get(v_cmdState_1057_, 8);
v_prevLinterStates_1071_ = lean_ctor_get(v_cmdState_1057_, 11);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_cmdState_1057_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1149_ = lean_ctor_get(v_cmdState_1057_, 10);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_cmdState_1057_, 9);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_cmdState_1057_, 1);
lean_dec(v_unused_1151_);
v___x_1073_ = v_cmdState_1057_;
v_isShared_1074_ = v_isSharedCheck_1148_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_prevLinterStates_1071_);
lean_inc(v_infoState_1070_);
lean_inc(v_auxDeclNGen_1069_);
lean_inc(v_ngen_1068_);
lean_inc(v_maxRecDepth_1067_);
lean_inc(v_nextMacroScope_1066_);
lean_inc(v_usedQuotCtxts_1065_);
lean_inc(v_scopes_1064_);
lean_inc(v_env_1063_);
lean_dec(v_cmdState_1057_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1148_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1075_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1076_ = l_List_head_x21___redArg(v___x_1075_, v_scopes_1064_);
v___x_1077_ = l_Lean_MessageLog_empty;
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1080_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 10, v___x_1080_);
lean_ctor_set(v___x_1073_, 9, v___x_1079_);
lean_ctor_set(v___x_1073_, 1, v___x_1077_);
v___x_1082_ = v___x_1073_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_env_1063_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_scopes_1064_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_usedQuotCtxts_1065_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_nextMacroScope_1066_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_maxRecDepth_1067_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v_ngen_1068_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_auxDeclNGen_1069_);
lean_ctor_set(v_reuseFailAlloc_1147_, 8, v_infoState_1070_);
lean_ctor_set(v_reuseFailAlloc_1147_, 9, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1147_, 10, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1147_, 11, v_prevLinterStates_1071_);
v___x_1082_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v_toProcessingContext_1084_; lean_object* v_fileName_1085_; lean_object* v_fileMap_1086_; lean_object* v_opts_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v_messages_1099_; lean_object* v___y_1126_; 
v___x_1083_ = lean_st_mk_ref(v___x_1082_);
v_toProcessingContext_1084_ = lean_ctor_get(v_a_1061_, 0);
v_fileName_1085_ = lean_ctor_get(v_toProcessingContext_1084_, 1);
v_fileMap_1086_ = lean_ctor_get(v_toProcessingContext_1084_, 2);
v_opts_1087_ = lean_ctor_get(v___x_1076_, 1);
lean_inc_ref(v_opts_1087_);
lean_dec(v___x_1076_);
v___f_1088_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1088_, 0, v_stx_1055_);
lean_closure_set(v___f_1088_, 1, v_cmds_1056_);
v___x_1089_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Lean_firstFrontendMacroScope;
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_internal_cmdlineSnapshots;
v___x_1095_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1087_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1146_; 
lean_inc_ref(v_snap_1059_);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_snap_1059_);
v___y_1126_ = v___x_1146_;
goto v___jp_1125_;
}
else
{
v___y_1126_ = v___x_1091_;
goto v___jp_1125_;
}
v___jp_1096_:
{
lean_object* v_new_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_env_1106_; lean_object* v_scopes_1107_; lean_object* v_usedQuotCtxts_1108_; lean_object* v_nextMacroScope_1109_; lean_object* v_maxRecDepth_1110_; lean_object* v_ngen_1111_; lean_object* v_auxDeclNGen_1112_; lean_object* v_infoState_1113_; lean_object* v_traceState_1114_; lean_object* v_snapshotTasks_1115_; lean_object* v_prevLinterStates_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_new_1100_ = lean_ctor_get(v_snap_1059_, 1);
lean_inc(v_new_1100_);
lean_dec_ref(v_snap_1059_);
v___x_1101_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1102_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1103_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
lean_ctor_set(v___x_1103_, 2, v___x_1091_);
lean_ctor_set(v___x_1103_, 3, v___x_1079_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*4, v___y_1098_);
v___x_1104_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1089_, v___x_1103_);
v___x_1105_ = lean_io_promise_resolve(v___x_1104_, v_new_1100_);
lean_dec(v_new_1100_);
v_env_1106_ = lean_ctor_get(v___y_1097_, 0);
v_scopes_1107_ = lean_ctor_get(v___y_1097_, 2);
v_usedQuotCtxts_1108_ = lean_ctor_get(v___y_1097_, 3);
v_nextMacroScope_1109_ = lean_ctor_get(v___y_1097_, 4);
v_maxRecDepth_1110_ = lean_ctor_get(v___y_1097_, 5);
v_ngen_1111_ = lean_ctor_get(v___y_1097_, 6);
v_auxDeclNGen_1112_ = lean_ctor_get(v___y_1097_, 7);
v_infoState_1113_ = lean_ctor_get(v___y_1097_, 8);
v_traceState_1114_ = lean_ctor_get(v___y_1097_, 9);
v_snapshotTasks_1115_ = lean_ctor_get(v___y_1097_, 10);
v_prevLinterStates_1116_ = lean_ctor_get(v___y_1097_, 11);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___y_1097_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___y_1097_, 1);
lean_dec(v_unused_1124_);
v___x_1118_ = v___y_1097_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_prevLinterStates_1116_);
lean_inc(v_snapshotTasks_1115_);
lean_inc(v_traceState_1114_);
lean_inc(v_infoState_1113_);
lean_inc(v_auxDeclNGen_1112_);
lean_inc(v_ngen_1111_);
lean_inc(v_maxRecDepth_1110_);
lean_inc(v_nextMacroScope_1109_);
lean_inc(v_usedQuotCtxts_1108_);
lean_inc(v_scopes_1107_);
lean_inc(v_env_1106_);
lean_dec(v___y_1097_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_messages_1099_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_env_1106_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_messages_1099_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_scopes_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_usedQuotCtxts_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_nextMacroScope_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 5, v_maxRecDepth_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 6, v_ngen_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 7, v_auxDeclNGen_1112_);
lean_ctor_set(v_reuseFailAlloc_1122_, 8, v_infoState_1113_);
lean_ctor_set(v_reuseFailAlloc_1122_, 9, v_traceState_1114_);
lean_ctor_set(v_reuseFailAlloc_1122_, 10, v_snapshotTasks_1115_);
lean_ctor_set(v_reuseFailAlloc_1122_, 11, v_prevLinterStates_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
v___jp_1125_:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v_fst_1134_; lean_object* v___x_1135_; lean_object* v_messages_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_cancelTk_1060_);
v___x_1128_ = 0;
lean_inc(v_beginPos_1058_);
lean_inc_ref(v_fileMap_1086_);
lean_inc_ref(v_fileName_1085_);
v___x_1129_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1129_, 0, v_fileName_1085_);
lean_ctor_set(v___x_1129_, 1, v_fileMap_1086_);
lean_ctor_set(v___x_1129_, 2, v___x_1078_);
lean_ctor_set(v___x_1129_, 3, v_beginPos_1058_);
lean_ctor_set(v___x_1129_, 4, v___x_1090_);
lean_ctor_set(v___x_1129_, 5, v___x_1091_);
lean_ctor_set(v___x_1129_, 6, v___x_1092_);
lean_ctor_set(v___x_1129_, 7, v___x_1093_);
lean_ctor_set(v___x_1129_, 8, v___y_1126_);
lean_ctor_set(v___x_1129_, 9, v___x_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*10, v___x_1128_);
lean_inc(v___x_1083_);
v___f_1130_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1130_, 0, v___f_1088_);
lean_closure_set(v___f_1130_, 1, v___x_1129_);
lean_closure_set(v___f_1130_, 2, v___x_1083_);
v___x_1131_ = l_Lean_Core_stderrAsMessages;
v___x_1132_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1087_, v___x_1131_);
lean_dec_ref(v_opts_1087_);
v___x_1133_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1130_, v___x_1132_, v_a_1061_);
v_fst_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_fst_1134_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = lean_st_ref_get(v___x_1083_);
lean_dec(v___x_1083_);
v_messages_1136_ = lean_ctor_get(v___x_1135_, 1);
lean_inc_ref(v_messages_1136_);
v___x_1137_ = lean_string_utf8_byte_size(v_fst_1134_);
v___x_1138_ = lean_nat_dec_eq(v___x_1137_, v___x_1078_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_inc_ref(v_fileMap_1086_);
v___x_1139_ = l_Lean_FileMap_toPosition(v_fileMap_1086_, v_beginPos_1058_);
lean_dec(v_beginPos_1058_);
v___x_1140_ = 0;
v___x_1141_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_fst_1134_);
v___x_1143_ = l_Lean_MessageData_ofFormat(v___x_1142_);
lean_inc_ref(v_fileName_1085_);
v___x_1144_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1144_, 0, v_fileName_1085_);
lean_ctor_set(v___x_1144_, 1, v___x_1139_);
lean_ctor_set(v___x_1144_, 2, v___x_1091_);
lean_ctor_set(v___x_1144_, 3, v___x_1141_);
lean_ctor_set(v___x_1144_, 4, v___x_1143_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*5, v___x_1128_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*5 + 1, v___x_1140_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*5 + 2, v___x_1128_);
v___x_1145_ = l_Lean_MessageLog_add(v___x_1144_, v_messages_1136_);
v___y_1097_ = v___x_1135_;
v___y_1098_ = v___x_1128_;
v_messages_1099_ = v___x_1145_;
goto v___jp_1096_;
}
else
{
lean_dec(v_fst_1134_);
lean_dec(v_beginPos_1058_);
v___y_1097_ = v___x_1135_;
v___y_1098_ = v___x_1128_;
v_messages_1099_ = v_messages_1136_;
goto v___jp_1096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1152_, lean_object* v_cmds_1153_, lean_object* v_cmdState_1154_, lean_object* v_beginPos_1155_, lean_object* v_snap_1156_, lean_object* v_cancelTk_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1152_, v_cmds_1153_, v_cmdState_1154_, v_beginPos_1155_, v_snap_1156_, v_cancelTk_1157_, v_a_1158_);
lean_dec_ref(v_a_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1161_, lean_object* v_h_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1162_, v_x_1163_, v___y_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_h_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1167_, v_h_1168_, v_x_1169_, v___y_1170_);
lean_dec_ref(v___y_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1173_, lean_object* v_x_1174_, uint8_t v_isolateStderr_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1174_, v_isolateStderr_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_x_1180_, lean_object* v_isolateStderr_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_isolateStderr_boxed_1184_; lean_object* v_res_1185_; 
v_isolateStderr_boxed_1184_ = lean_unbox(v_isolateStderr_1181_);
v_res_1185_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1179_, v_x_1180_, v_isolateStderr_boxed_1184_, v___y_1182_);
lean_dec_ref(v___y_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1186_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1196_){
_start:
{
lean_object* v_toSnapshotTreeM_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_toSnapshotTreeM_1197_ = lean_ctor_get(v_a_1196_, 1);
lean_inc_ref(v_toSnapshotTreeM_1197_);
lean_dec_ref(v_a_1196_);
v___x_1198_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1199_ = lean_apply_1(v_toSnapshotTreeM_1197_, v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1200_){
_start:
{
lean_object* v_toSnapshot_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1211_; 
v_toSnapshot_1201_ = lean_ctor_get(v_a_1200_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_a_1200_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_a_1200_, 1);
lean_dec(v_unused_1212_);
v___x_1203_ = v_a_1200_;
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_toSnapshot_1201_);
lean_dec(v_a_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1211_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1205_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1206_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1201_, v___x_1205_);
v___x_1207_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1207_);
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1215_ = l_Lean_Language_Snapshot_transform(v_a_1213_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1218_, lean_object* v_opt_1219_){
_start:
{
lean_object* v_name_1220_; lean_object* v_defValue_1221_; lean_object* v_map_1222_; lean_object* v___x_1223_; 
v_name_1220_ = lean_ctor_get(v_opt_1219_, 0);
v_defValue_1221_ = lean_ctor_get(v_opt_1219_, 1);
v_map_1222_ = lean_ctor_get(v_opts_1218_, 0);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1222_, v_name_1220_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_inc(v_defValue_1221_);
return v_defValue_1221_;
}
else
{
lean_object* v_val_1224_; 
v_val_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v___x_1223_, 1);
if (lean_obj_tag(v_val_1224_) == 3)
{
lean_object* v_v_1225_; 
v_v_1225_ = lean_ctor_get(v_val_1224_, 0);
lean_inc(v_v_1225_);
lean_dec_ref_known(v_val_1224_, 1);
return v_v_1225_;
}
else
{
lean_dec(v_val_1224_);
lean_inc(v_defValue_1221_);
return v_defValue_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1226_, lean_object* v_opt_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1226_, v_opt_1227_);
lean_dec_ref(v_opt_1227_);
lean_dec_ref(v_opts_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1231_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1229_, v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1238_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1239_ = l_Lean_Name_append(v___x_1238_, v___x_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1240_, lean_object* v___x_1241_, uint8_t v_val_1242_, lean_object* v_val_1243_, lean_object* v_val_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, uint8_t v___x_1247_, lean_object* v_a_1248_, lean_object* v_pos_1249_, lean_object* v_infoSt_1250_){
_start:
{
lean_object* v___y_1253_; lean_object* v_msgLog_1254_; lean_object* v___y_1260_; lean_object* v_trees_1292_; lean_object* v_size_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_trees_1292_ = lean_ctor_get(v_infoSt_1250_, 2);
v_size_1293_ = lean_ctor_get(v_trees_1292_, 2);
v___x_1294_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1295_ = lean_nat_dec_lt(v___x_1246_, v_size_1293_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = l_outOfBounds___redArg(v___x_1294_);
v___y_1260_ = v___x_1296_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1294_, v_trees_1292_, v___x_1246_);
v___y_1260_ = v___x_1297_;
goto v___jp_1259_;
}
v___jp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1254_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1253_);
v___x_1257_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1257_, 0, v___x_1240_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
lean_ctor_set(v___x_1257_, 3, v___x_1241_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*4, v_val_1242_);
v___x_1258_ = lean_io_promise_resolve(v___x_1257_, v_val_1243_);
return v___x_1258_;
}
v___jp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v_scopes_1263_; lean_object* v___x_1264_; lean_object* v_opts_1265_; uint8_t v_hasTrace_1266_; lean_object* v___x_1267_; 
v___x_1261_ = l_Lean_inheritedTraceOptions;
v___x_1262_ = lean_st_ref_get(v___x_1261_);
v_scopes_1263_ = lean_ctor_get(v_val_1244_, 2);
v___x_1264_ = l_List_head_x21___redArg(v___x_1245_, v_scopes_1263_);
v_opts_1265_ = lean_ctor_get(v___x_1264_, 1);
lean_inc_ref(v_opts_1265_);
lean_dec(v___x_1264_);
v_hasTrace_1266_ = lean_ctor_get_uint8(v_opts_1265_, sizeof(void*)*1);
v___x_1267_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1266_ == 0)
{
lean_dec_ref(v_opts_1265_);
lean_dec(v___x_1262_);
lean_dec(v___x_1246_);
v___y_1253_ = v___y_1260_;
v_msgLog_1254_ = v___x_1267_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1269_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1270_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1271_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1262_, v_opts_1265_, v___x_1270_);
lean_dec_ref(v_opts_1265_);
lean_dec(v___x_1262_);
if (v___x_1271_ == 0)
{
lean_dec(v___x_1246_);
v___y_1253_ = v___y_1260_;
v_msgLog_1254_ = v___x_1267_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_box(0);
lean_inc_ref(v___y_1260_);
v___x_1273_ = l_Lean_Elab_InfoTree_format(v___y_1260_, v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; double v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_toProcessingContext_1278_; lean_object* v_fileName_1279_; lean_object* v_fileMap_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = lean_float_of_nat(v___x_1246_);
v___x_1276_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1277_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1277_, 0, v___x_1268_);
lean_ctor_set(v___x_1277_, 1, v___x_1272_);
lean_ctor_set(v___x_1277_, 2, v___x_1276_);
lean_ctor_set_float(v___x_1277_, sizeof(void*)*3, v___x_1275_);
lean_ctor_set_float(v___x_1277_, sizeof(void*)*3 + 8, v___x_1275_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*3 + 16, v___x_1247_);
v_toProcessingContext_1278_ = lean_ctor_get(v_a_1248_, 0);
v_fileName_1279_ = lean_ctor_get(v_toProcessingContext_1278_, 1);
v_fileMap_1280_ = lean_ctor_get(v_toProcessingContext_1278_, 2);
v___x_1281_ = l_Lean_MessageData_nil;
v___x_1282_ = l_Lean_MessageData_ofFormat(v_a_1274_);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_mk_empty_array_with_capacity(v___x_1283_);
v___x_1285_ = lean_array_push(v___x_1284_, v___x_1282_);
v___x_1286_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1277_);
lean_ctor_set(v___x_1286_, 1, v___x_1281_);
lean_ctor_set(v___x_1286_, 2, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1269_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
lean_inc_ref(v_fileMap_1280_);
v___x_1288_ = l_Lean_FileMap_toPosition(v_fileMap_1280_, v_pos_1249_);
v___x_1289_ = 0;
lean_inc_ref(v_fileName_1279_);
v___x_1290_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1290_, 0, v_fileName_1279_);
lean_ctor_set(v___x_1290_, 1, v___x_1288_);
lean_ctor_set(v___x_1290_, 2, v___x_1272_);
lean_ctor_set(v___x_1290_, 3, v___x_1276_);
lean_ctor_set(v___x_1290_, 4, v___x_1287_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*5, v_val_1242_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*5 + 1, v___x_1289_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*5 + 2, v_val_1242_);
v___x_1291_ = l_Lean_MessageLog_add(v___x_1290_, v___x_1267_);
v___y_1253_ = v___y_1260_;
v_msgLog_1254_ = v___x_1291_;
goto v___jp_1252_;
}
else
{
lean_dec_ref_known(v___x_1273_, 1);
lean_dec(v___x_1246_);
v___y_1253_ = v___y_1260_;
v_msgLog_1254_ = v___x_1267_;
goto v___jp_1252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1298_, lean_object* v___x_1299_, lean_object* v_val_1300_, lean_object* v_val_1301_, lean_object* v_val_1302_, lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v_a_1306_, lean_object* v_pos_1307_, lean_object* v_infoSt_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_val_44422__boxed_1310_; uint8_t v___x_44427__boxed_1311_; lean_object* v_res_1312_; 
v_val_44422__boxed_1310_ = lean_unbox(v_val_1300_);
v___x_44427__boxed_1311_ = lean_unbox(v___x_1305_);
v_res_1312_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1298_, v___x_1299_, v_val_44422__boxed_1310_, v_val_1301_, v_val_1302_, v___x_1303_, v___x_1304_, v___x_44427__boxed_1311_, v_a_1306_, v_pos_1307_, v_infoSt_1308_);
lean_dec_ref(v_infoSt_1308_);
lean_dec(v_pos_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v_val_1302_);
lean_dec(v_val_1301_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v___x_1315_, uint8_t v_val_1316_, lean_object* v_as_1317_, size_t v_sz_1318_, size_t v_i_1319_, lean_object* v_b_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_lt(v_i_1319_, v_sz_1318_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v___x_1315_);
lean_dec_ref(v___x_1313_);
return v_b_1320_;
}
else
{
lean_object* v_snd_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1341_; 
v_snd_1323_ = lean_ctor_get(v_b_1320_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_b_1320_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_b_1320_, 0);
lean_dec(v_unused_1342_);
v___x_1325_ = v_b_1320_;
v_isShared_1326_ = v_isSharedCheck_1341_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_snd_1323_);
lean_dec(v_b_1320_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1341_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_a_1327_; lean_object* v_msg_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v_a_1327_ = lean_array_uget_borrowed(v_as_1317_, v_i_1319_);
v_msg_1328_ = lean_ctor_get(v_a_1327_, 1);
v___x_1329_ = lean_box(0);
lean_inc_ref(v___x_1313_);
v___x_1330_ = l_Lean_FileMap_toPosition(v___x_1313_, v___x_1314_);
v___x_1331_ = 0;
v___x_1332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1328_);
lean_inc_ref(v___x_1315_);
v___x_1333_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1333_, 0, v___x_1315_);
lean_ctor_set(v___x_1333_, 1, v___x_1330_);
lean_ctor_set(v___x_1333_, 2, v___x_1329_);
lean_ctor_set(v___x_1333_, 3, v___x_1332_);
lean_ctor_set(v___x_1333_, 4, v_msg_1328_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*5, v_val_1316_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*5 + 1, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*5 + 2, v_val_1316_);
v___x_1334_ = l_Lean_MessageLog_add(v___x_1333_, v_snd_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v___x_1334_);
lean_ctor_set(v___x_1325_, 0, v___x_1329_);
v___x_1336_ = v___x_1325_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
size_t v___x_1337_; size_t v___x_1338_; 
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1319_, v___x_1337_);
v_i_1319_ = v___x_1338_;
v_b_1320_ = v___x_1336_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_val_1346_, lean_object* v_as_1347_, lean_object* v_sz_1348_, lean_object* v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v_val_44534__boxed_1352_; size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_val_44534__boxed_1352_ = lean_unbox(v_val_1346_);
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1348_);
lean_dec(v_sz_1348_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1343_, v___x_1344_, v___x_1345_, v_val_44534__boxed_1352_, v_as_1347_, v_sz_boxed_1353_, v_i_boxed_1354_, v_b_1350_);
lean_dec_ref(v_as_1347_);
lean_dec(v___x_1344_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, uint8_t v_val_1359_, lean_object* v_as_1360_, size_t v_sz_1361_, size_t v_i_1362_, lean_object* v_b_1363_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_usize_dec_lt(v_i_1362_, v_sz_1361_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1356_);
return v_b_1363_;
}
else
{
lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1384_; 
v_snd_1366_ = lean_ctor_get(v_b_1363_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_b_1363_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v_b_1363_, 0);
lean_dec(v_unused_1385_);
v___x_1368_ = v_b_1363_;
v_isShared_1369_ = v_isSharedCheck_1384_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_dec(v_b_1363_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1384_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_a_1370_; lean_object* v_msg_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v_a_1370_ = lean_array_uget_borrowed(v_as_1360_, v_i_1362_);
v_msg_1371_ = lean_ctor_get(v_a_1370_, 1);
v___x_1372_ = lean_box(0);
lean_inc_ref(v___x_1356_);
v___x_1373_ = l_Lean_FileMap_toPosition(v___x_1356_, v___x_1357_);
v___x_1374_ = 0;
v___x_1375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1371_);
lean_inc_ref(v___x_1358_);
v___x_1376_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1376_, 0, v___x_1358_);
lean_ctor_set(v___x_1376_, 1, v___x_1373_);
lean_ctor_set(v___x_1376_, 2, v___x_1372_);
lean_ctor_set(v___x_1376_, 3, v___x_1375_);
lean_ctor_set(v___x_1376_, 4, v_msg_1371_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5, v_val_1359_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5 + 1, v___x_1374_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5 + 2, v_val_1359_);
v___x_1377_ = l_Lean_MessageLog_add(v___x_1376_, v_snd_1366_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1377_);
lean_ctor_set(v___x_1368_, 0, v___x_1372_);
v___x_1379_ = v___x_1368_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1362_, v___x_1380_);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1356_, v___x_1357_, v___x_1358_, v_val_1359_, v_as_1360_, v_sz_1361_, v___x_1381_, v___x_1379_);
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1386_, lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v_val_1389_, lean_object* v_as_1390_, lean_object* v_sz_1391_, lean_object* v_i_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_val_44586__boxed_1395_; size_t v_sz_boxed_1396_; size_t v_i_boxed_1397_; lean_object* v_res_1398_; 
v_val_44586__boxed_1395_ = lean_unbox(v_val_1389_);
v_sz_boxed_1396_ = lean_unbox_usize(v_sz_1391_);
lean_dec(v_sz_1391_);
v_i_boxed_1397_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_res_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1386_, v___x_1387_, v___x_1388_, v_val_44586__boxed_1395_, v_as_1390_, v_sz_boxed_1396_, v_i_boxed_1397_, v_b_1393_);
lean_dec_ref(v_as_1390_);
lean_dec(v___x_1387_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___x_1402_, uint8_t v_val_1403_, lean_object* v_n_1404_, lean_object* v_b_1405_){
_start:
{
if (lean_obj_tag(v_n_1404_) == 0)
{
lean_object* v_cs_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; size_t v_sz_1410_; size_t v___x_1411_; lean_object* v___x_1412_; lean_object* v_fst_1413_; 
v_cs_1407_ = lean_ctor_get(v_n_1404_, 0);
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_b_1405_);
v_sz_1410_ = lean_array_size(v_cs_1407_);
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1399_, v___x_1400_, v___x_1401_, v___x_1402_, v_val_1403_, v_cs_1407_, v_sz_1410_, v___x_1411_, v___x_1409_);
v_fst_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_fst_1413_);
if (lean_obj_tag(v_fst_1413_) == 0)
{
lean_object* v_snd_1414_; lean_object* v___x_1415_; 
v_snd_1414_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_snd_1414_);
lean_dec_ref(v___x_1412_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_snd_1414_);
return v___x_1415_;
}
else
{
lean_object* v_val_1416_; 
lean_dec_ref(v___x_1412_);
v_val_1416_ = lean_ctor_get(v_fst_1413_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v_fst_1413_, 1);
return v_val_1416_;
}
}
else
{
lean_object* v_vs_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v_fst_1423_; 
v_vs_1417_ = lean_ctor_get(v_n_1404_, 0);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_b_1405_);
v_sz_1420_ = lean_array_size(v_vs_1417_);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1400_, v___x_1401_, v___x_1402_, v_val_1403_, v_vs_1417_, v_sz_1420_, v___x_1421_, v___x_1419_);
v_fst_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_fst_1423_);
if (lean_obj_tag(v_fst_1423_) == 0)
{
lean_object* v_snd_1424_; lean_object* v___x_1425_; 
v_snd_1424_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_snd_1424_);
lean_dec_ref(v___x_1422_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_snd_1424_);
return v___x_1425_;
}
else
{
lean_object* v_val_1426_; 
lean_dec_ref(v___x_1422_);
v_val_1426_ = lean_ctor_get(v_fst_1423_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v_fst_1423_, 1);
return v_val_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, uint8_t v_val_1431_, lean_object* v_as_1432_, size_t v_sz_1433_, size_t v_i_1434_, lean_object* v_b_1435_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_usize_dec_lt(v_i_1434_, v_sz_1433_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v___x_1430_);
lean_dec_ref(v___x_1428_);
return v_b_1435_;
}
else
{
lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1456_; 
v_snd_1438_ = lean_ctor_get(v_b_1435_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_b_1435_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_b_1435_, 0);
lean_dec(v_unused_1457_);
v___x_1440_ = v_b_1435_;
v_isShared_1441_ = v_isSharedCheck_1456_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_dec(v_b_1435_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1456_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_a_1442_; lean_object* v___x_1443_; 
v_a_1442_ = lean_array_uget_borrowed(v_as_1432_, v_i_1434_);
lean_inc(v_snd_1438_);
lean_inc_ref(v___x_1430_);
lean_inc_ref(v___x_1428_);
v___x_1443_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1427_, v___x_1428_, v___x_1429_, v___x_1430_, v_val_1431_, v_a_1442_, v_snd_1438_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref(v___x_1430_);
lean_dec_ref(v___x_1428_);
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1444_);
v___x_1446_ = v___x_1440_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_snd_1438_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec(v_snd_1438_);
v_a_1448_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1443_, 1);
v___x_1449_ = lean_box(0);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v_a_1448_);
lean_ctor_set(v___x_1440_, 0, v___x_1449_);
v___x_1451_ = v___x_1440_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_a_1448_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
size_t v___x_1452_; size_t v___x_1453_; 
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1434_, v___x_1452_);
v_i_1434_ = v___x_1453_;
v_b_1435_ = v___x_1451_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1458_, lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v___x_1461_, lean_object* v_val_1462_, lean_object* v_as_1463_, lean_object* v_sz_1464_, lean_object* v_i_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_val_44637__boxed_1468_; size_t v_sz_boxed_1469_; size_t v_i_boxed_1470_; lean_object* v_res_1471_; 
v_val_44637__boxed_1468_ = lean_unbox(v_val_1462_);
v_sz_boxed_1469_ = lean_unbox_usize(v_sz_1464_);
lean_dec(v_sz_1464_);
v_i_boxed_1470_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1458_, v___x_1459_, v___x_1460_, v___x_1461_, v_val_44637__boxed_1468_, v_as_1463_, v_sz_boxed_1469_, v_i_boxed_1470_, v_b_1466_);
lean_dec_ref(v_as_1463_);
lean_dec(v___x_1460_);
lean_dec_ref(v_init_1458_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v_val_1476_, lean_object* v_n_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v_val_44653__boxed_1480_; lean_object* v_res_1481_; 
v_val_44653__boxed_1480_ = lean_unbox(v_val_1476_);
v_res_1481_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1472_, v___x_1473_, v___x_1474_, v___x_1475_, v_val_44653__boxed_1480_, v_n_1477_, v_b_1478_);
lean_dec_ref(v_n_1477_);
lean_dec(v___x_1474_);
lean_dec_ref(v_init_1472_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, uint8_t v_val_1485_, lean_object* v_as_1486_, size_t v_sz_1487_, size_t v_i_1488_, lean_object* v_b_1489_){
_start:
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_usize_dec_lt(v_i_1488_, v_sz_1487_);
if (v___x_1491_ == 0)
{
lean_dec_ref(v___x_1484_);
lean_dec_ref(v___x_1482_);
return v_b_1489_;
}
else
{
lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1510_; 
v_snd_1492_ = lean_ctor_get(v_b_1489_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_b_1489_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_b_1489_, 0);
lean_dec(v_unused_1511_);
v___x_1494_ = v_b_1489_;
v_isShared_1495_ = v_isSharedCheck_1510_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_dec(v_b_1489_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1510_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_a_1496_; lean_object* v_msg_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v_a_1496_ = lean_array_uget_borrowed(v_as_1486_, v_i_1488_);
v_msg_1497_ = lean_ctor_get(v_a_1496_, 1);
v___x_1498_ = lean_box(0);
lean_inc_ref(v___x_1482_);
v___x_1499_ = l_Lean_FileMap_toPosition(v___x_1482_, v___x_1483_);
v___x_1500_ = 0;
v___x_1501_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1497_);
lean_inc_ref(v___x_1484_);
v___x_1502_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1502_, 0, v___x_1484_);
lean_ctor_set(v___x_1502_, 1, v___x_1499_);
lean_ctor_set(v___x_1502_, 2, v___x_1498_);
lean_ctor_set(v___x_1502_, 3, v___x_1501_);
lean_ctor_set(v___x_1502_, 4, v_msg_1497_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*5, v_val_1485_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*5 + 1, v___x_1500_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*5 + 2, v_val_1485_);
v___x_1503_ = l_Lean_MessageLog_add(v___x_1502_, v_snd_1492_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1503_);
lean_ctor_set(v___x_1494_, 0, v___x_1498_);
v___x_1505_ = v___x_1494_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
size_t v___x_1506_; size_t v___x_1507_; 
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1488_, v___x_1506_);
v_i_1488_ = v___x_1507_;
v_b_1489_ = v___x_1505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1512_, lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v_val_1515_, lean_object* v_as_1516_, lean_object* v_sz_1517_, lean_object* v_i_1518_, lean_object* v_b_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v_val_44735__boxed_1521_; size_t v_sz_boxed_1522_; size_t v_i_boxed_1523_; lean_object* v_res_1524_; 
v_val_44735__boxed_1521_ = lean_unbox(v_val_1515_);
v_sz_boxed_1522_ = lean_unbox_usize(v_sz_1517_);
lean_dec(v_sz_1517_);
v_i_boxed_1523_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1512_, v___x_1513_, v___x_1514_, v_val_44735__boxed_1521_, v_as_1516_, v_sz_boxed_1522_, v_i_boxed_1523_, v_b_1519_);
lean_dec_ref(v_as_1516_);
lean_dec(v___x_1513_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, uint8_t v_val_1528_, lean_object* v_as_1529_, size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_b_1532_){
_start:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v___x_1527_);
lean_dec_ref(v___x_1525_);
return v_b_1532_;
}
else
{
lean_object* v_snd_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1553_; 
v_snd_1535_ = lean_ctor_get(v_b_1532_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_b_1532_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_b_1532_, 0);
lean_dec(v_unused_1554_);
v___x_1537_ = v_b_1532_;
v_isShared_1538_ = v_isSharedCheck_1553_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snd_1535_);
lean_dec(v_b_1532_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1553_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_a_1539_; lean_object* v_msg_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v_a_1539_ = lean_array_uget_borrowed(v_as_1529_, v_i_1531_);
v_msg_1540_ = lean_ctor_get(v_a_1539_, 1);
v___x_1541_ = lean_box(0);
lean_inc_ref(v___x_1525_);
v___x_1542_ = l_Lean_FileMap_toPosition(v___x_1525_, v___x_1526_);
v___x_1543_ = 0;
v___x_1544_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1540_);
lean_inc_ref(v___x_1527_);
v___x_1545_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1545_, 0, v___x_1527_);
lean_ctor_set(v___x_1545_, 1, v___x_1542_);
lean_ctor_set(v___x_1545_, 2, v___x_1541_);
lean_ctor_set(v___x_1545_, 3, v___x_1544_);
lean_ctor_set(v___x_1545_, 4, v_msg_1540_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*5, v_val_1528_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*5 + 1, v___x_1543_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*5 + 2, v_val_1528_);
v___x_1546_ = l_Lean_MessageLog_add(v___x_1545_, v_snd_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v___x_1546_);
lean_ctor_set(v___x_1537_, 0, v___x_1541_);
v___x_1548_ = v___x_1537_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1531_, v___x_1549_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1525_, v___x_1526_, v___x_1527_, v_val_1528_, v_as_1529_, v_sz_1530_, v___x_1550_, v___x_1548_);
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1555_, lean_object* v___x_1556_, lean_object* v___x_1557_, lean_object* v_val_1558_, lean_object* v_as_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_){
_start:
{
uint8_t v_val_44787__boxed_1564_; size_t v_sz_boxed_1565_; size_t v_i_boxed_1566_; lean_object* v_res_1567_; 
v_val_44787__boxed_1564_ = lean_unbox(v_val_1558_);
v_sz_boxed_1565_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1566_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1555_, v___x_1556_, v___x_1557_, v_val_44787__boxed_1564_, v_as_1559_, v_sz_boxed_1565_, v_i_boxed_1566_, v_b_1562_);
lean_dec_ref(v_as_1559_);
lean_dec(v___x_1556_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v___x_1570_, uint8_t v_val_1571_, lean_object* v_t_1572_, lean_object* v_init_1573_){
_start:
{
lean_object* v_root_1575_; lean_object* v_tail_1576_; lean_object* v___x_1577_; 
v_root_1575_ = lean_ctor_get(v_t_1572_, 0);
v_tail_1576_ = lean_ctor_get(v_t_1572_, 1);
lean_inc_ref(v___x_1570_);
lean_inc_ref(v___x_1568_);
lean_inc_ref(v_init_1573_);
v___x_1577_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1573_, v___x_1568_, v___x_1569_, v___x_1570_, v_val_1571_, v_root_1575_, v_init_1573_);
lean_dec_ref(v_init_1573_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; 
lean_dec_ref(v___x_1570_);
lean_dec_ref(v___x_1568_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
return v_a_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; size_t v_sz_1582_; size_t v___x_1583_; lean_object* v___x_1584_; lean_object* v_fst_1585_; 
v_a_1579_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_a_1579_);
v_sz_1582_ = lean_array_size(v_tail_1576_);
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1568_, v___x_1569_, v___x_1570_, v_val_1571_, v_tail_1576_, v_sz_1582_, v___x_1583_, v___x_1581_);
v_fst_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_fst_1585_);
if (lean_obj_tag(v_fst_1585_) == 0)
{
lean_object* v_snd_1586_; 
v_snd_1586_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_snd_1586_);
lean_dec_ref(v___x_1584_);
return v_snd_1586_;
}
else
{
lean_object* v_val_1587_; 
lean_dec_ref(v___x_1584_);
v_val_1587_ = lean_ctor_get(v_fst_1585_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_fst_1585_, 1);
return v_val_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v_val_1591_, lean_object* v_t_1592_, lean_object* v_init_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v_val_44838__boxed_1595_; lean_object* v_res_1596_; 
v_val_44838__boxed_1595_ = lean_unbox(v_val_1591_);
v_res_1596_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1588_, v___x_1589_, v___x_1590_, v_val_44838__boxed_1595_, v_t_1592_, v_init_1593_);
lean_dec_ref(v_t_1592_);
lean_dec(v___x_1589_);
return v_res_1596_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = l_Lean_firstFrontendMacroScope;
v___x_1599_ = lean_nat_add(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1606_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v___x_1611_, lean_object* v___x_1612_, lean_object* v___x_1613_, size_t v___x_1614_, uint8_t v___x_1615_, lean_object* v_env_1616_, lean_object* v___x_1617_, lean_object* v___x_1618_, lean_object* v_a_1619_, lean_object* v_opts_1620_, lean_object* v___x_1621_, lean_object* v_pos_1622_, uint8_t v_val_1623_, lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v___x_1627_, uint8_t v___x_1628_, lean_object* v_x_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_toProcessingContext_1650_; lean_object* v_fileName_1651_; lean_object* v_fileMap_1652_; lean_object* v_env_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v_fileName_1659_; lean_object* v_fileMap_1660_; lean_object* v_currRecDepth_1661_; lean_object* v_ref_1662_; lean_object* v_currNamespace_1663_; lean_object* v_openDecls_1664_; lean_object* v_initHeartbeats_1665_; lean_object* v_maxHeartbeats_1666_; lean_object* v_quotContext_1667_; lean_object* v_currMacroScope_1668_; lean_object* v_cancelTk_x3f_1669_; uint8_t v_suppressElabErrors_1670_; lean_object* v_inheritedTraceOptions_1671_; lean_object* v___y_1672_; uint8_t v___y_1689_; uint8_t v___x_1709_; 
v___x_1631_ = l_Lean_firstFrontendMacroScope;
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1634_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_1635_ = lean_box(0);
lean_inc(v___x_1611_);
v___x_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1611_);
lean_ctor_set(v___x_1636_, 1, v___x_1632_);
lean_ctor_set(v___x_1636_, 2, v___x_1635_);
v___x_1637_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1638_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6);
v___x_1639_ = lean_mk_empty_array_with_capacity(v___x_1612_);
lean_inc_ref(v___x_1639_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_inc_n(v___x_1613_, 2);
v___x_1641_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1639_);
lean_ctor_set(v___x_1641_, 2, v___x_1613_);
lean_ctor_set(v___x_1641_, 3, v___x_1613_);
lean_ctor_set_usize(v___x_1641_, 4, v___x_1614_);
v___x_1642_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1641_, 2);
v___x_1643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1641_);
lean_ctor_set(v___x_1643_, 2, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1637_);
lean_ctor_set(v___x_1644_, 1, v___x_1637_);
lean_ctor_set(v___x_1644_, 2, v___x_1641_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*3, v___x_1615_);
v___x_1645_ = lean_mk_empty_array_with_capacity(v___x_1613_);
lean_inc_ref(v___x_1645_);
lean_inc_ref(v___x_1617_);
v___x_1646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1646_, 0, v_env_1616_);
lean_ctor_set(v___x_1646_, 1, v___x_1633_);
lean_ctor_set(v___x_1646_, 2, v___x_1634_);
lean_ctor_set(v___x_1646_, 3, v___x_1636_);
lean_ctor_set(v___x_1646_, 4, v___x_1617_);
lean_ctor_set(v___x_1646_, 5, v___x_1638_);
lean_ctor_set(v___x_1646_, 6, v___x_1643_);
lean_ctor_set(v___x_1646_, 7, v___x_1644_);
lean_ctor_set(v___x_1646_, 8, v___x_1645_);
v___x_1647_ = lean_st_mk_ref(v___x_1646_);
v___x_1648_ = lean_st_ref_get(v___x_1618_);
v___x_1649_ = lean_st_ref_get(v___x_1647_);
v_toProcessingContext_1650_ = lean_ctor_get(v_a_1619_, 0);
v_fileName_1651_ = lean_ctor_get(v_toProcessingContext_1650_, 1);
v_fileMap_1652_ = lean_ctor_get(v_toProcessingContext_1650_, 2);
v_env_1653_ = lean_ctor_get(v___x_1649_, 0);
lean_inc_ref(v_env_1653_);
lean_dec(v___x_1649_);
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_Core_getMaxHeartbeats(v_opts_1620_);
v___x_1656_ = l_Lean_diagnostics;
v___x_1657_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1620_, v___x_1656_);
v___x_1709_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1653_);
lean_dec_ref(v_env_1653_);
if (v___x_1709_ == 0)
{
if (v___x_1657_ == 0)
{
v___y_1689_ = v___x_1628_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v___x_1709_;
goto v___jp_1688_;
}
}
else
{
v___y_1689_ = v___x_1657_;
goto v___jp_1688_;
}
v___jp_1658_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = l_Lean_maxRecDepth;
v___x_1674_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1620_, v___x_1673_);
lean_inc(v_currMacroScope_1668_);
lean_inc(v_openDecls_1664_);
lean_inc(v_ref_1662_);
v___x_1675_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1675_, 0, v_fileName_1659_);
lean_ctor_set(v___x_1675_, 1, v_fileMap_1660_);
lean_ctor_set(v___x_1675_, 2, v_opts_1620_);
lean_ctor_set(v___x_1675_, 3, v_currRecDepth_1661_);
lean_ctor_set(v___x_1675_, 4, v___x_1674_);
lean_ctor_set(v___x_1675_, 5, v_ref_1662_);
lean_ctor_set(v___x_1675_, 6, v_currNamespace_1663_);
lean_ctor_set(v___x_1675_, 7, v_openDecls_1664_);
lean_ctor_set(v___x_1675_, 8, v_initHeartbeats_1665_);
lean_ctor_set(v___x_1675_, 9, v_maxHeartbeats_1666_);
lean_ctor_set(v___x_1675_, 10, v_quotContext_1667_);
lean_ctor_set(v___x_1675_, 11, v_currMacroScope_1668_);
lean_ctor_set(v___x_1675_, 12, v_cancelTk_x3f_1669_);
lean_ctor_set(v___x_1675_, 13, v_inheritedTraceOptions_1671_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*14, v___x_1657_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*14 + 1, v_suppressElabErrors_1670_);
v___x_1676_ = l_Lean_Language_SnapshotTree_trace(v___x_1621_, v___x_1675_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref_known(v___x_1675_, 14);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; lean_object* v_traceState_1678_; lean_object* v_traces_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref_known(v___x_1676_, 1);
lean_dec_ref(v___x_1626_);
v___x_1677_ = lean_st_ref_get(v___x_1647_);
lean_dec(v___x_1647_);
v_traceState_1678_ = lean_ctor_get(v___x_1677_, 4);
lean_inc_ref(v_traceState_1678_);
lean_dec(v___x_1677_);
v_traces_1679_ = lean_ctor_get(v_traceState_1678_, 0);
lean_inc_ref(v_traces_1679_);
lean_dec_ref(v_traceState_1678_);
v___x_1680_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1651_);
lean_inc_ref(v_fileMap_1652_);
v___x_1681_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1652_, v_pos_1622_, v_fileName_1651_, v_val_1623_, v_traces_1679_, v___x_1680_);
lean_dec_ref(v_traces_1679_);
v___x_1682_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1624_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_ctor_set(v___x_1683_, 2, v___x_1625_);
lean_ctor_set(v___x_1683_, 3, v___x_1617_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*4, v_val_1623_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v___x_1645_);
v___x_1685_ = lean_task_pure(v___x_1684_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1676_, 1);
lean_dec(v___x_1647_);
lean_dec(v___x_1625_);
lean_dec_ref(v___x_1624_);
lean_dec_ref(v___x_1617_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1626_);
lean_ctor_set(v___x_1686_, 1, v___x_1645_);
v___x_1687_ = lean_task_pure(v___x_1686_);
return v___x_1687_;
}
}
v___jp_1688_:
{
if (v___y_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v_env_1691_; lean_object* v_nextMacroScope_1692_; lean_object* v_ngen_1693_; lean_object* v_auxDeclNGen_1694_; lean_object* v_traceState_1695_; lean_object* v_messages_1696_; lean_object* v_infoState_1697_; lean_object* v_snapshotTasks_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1707_; 
v___x_1690_ = lean_st_ref_take(v___x_1647_);
v_env_1691_ = lean_ctor_get(v___x_1690_, 0);
v_nextMacroScope_1692_ = lean_ctor_get(v___x_1690_, 1);
v_ngen_1693_ = lean_ctor_get(v___x_1690_, 2);
v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1690_, 3);
v_traceState_1695_ = lean_ctor_get(v___x_1690_, 4);
v_messages_1696_ = lean_ctor_get(v___x_1690_, 6);
v_infoState_1697_ = lean_ctor_get(v___x_1690_, 7);
v_snapshotTasks_1698_ = lean_ctor_get(v___x_1690_, 8);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___x_1690_, 5);
lean_dec(v_unused_1708_);
v___x_1700_ = v___x_1690_;
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snapshotTasks_1698_);
lean_inc(v_infoState_1697_);
lean_inc(v_messages_1696_);
lean_inc(v_traceState_1695_);
lean_inc(v_auxDeclNGen_1694_);
lean_inc(v_ngen_1693_);
lean_inc(v_nextMacroScope_1692_);
lean_inc(v_env_1691_);
lean_dec(v___x_1690_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l_Lean_Kernel_enableDiag(v_env_1691_, v___x_1657_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 5, v___x_1638_);
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_nextMacroScope_1692_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_ngen_1693_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_auxDeclNGen_1694_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_traceState_1695_);
lean_ctor_set(v_reuseFailAlloc_1706_, 5, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1706_, 6, v_messages_1696_);
lean_ctor_set(v_reuseFailAlloc_1706_, 7, v_infoState_1697_);
lean_ctor_set(v_reuseFailAlloc_1706_, 8, v_snapshotTasks_1698_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_st_ref_set(v___x_1647_, v___x_1704_);
lean_inc(v___x_1647_);
lean_inc(v___x_1611_);
lean_inc(v___x_1613_);
lean_inc_ref(v_fileMap_1652_);
lean_inc_ref(v_fileName_1651_);
v_fileName_1659_ = v_fileName_1651_;
v_fileMap_1660_ = v_fileMap_1652_;
v_currRecDepth_1661_ = v___x_1613_;
v_ref_1662_ = v___x_1654_;
v_currNamespace_1663_ = v___x_1611_;
v_openDecls_1664_ = v___x_1635_;
v_initHeartbeats_1665_ = v___x_1613_;
v_maxHeartbeats_1666_ = v___x_1655_;
v_quotContext_1667_ = v___x_1611_;
v_currMacroScope_1668_ = v___x_1631_;
v_cancelTk_x3f_1669_ = v___x_1627_;
v_suppressElabErrors_1670_ = v_val_1623_;
v_inheritedTraceOptions_1671_ = v___x_1648_;
v___y_1672_ = v___x_1647_;
goto v___jp_1658_;
}
}
}
else
{
lean_inc(v___x_1647_);
lean_inc(v___x_1611_);
lean_inc(v___x_1613_);
lean_inc_ref(v_fileMap_1652_);
lean_inc_ref(v_fileName_1651_);
v_fileName_1659_ = v_fileName_1651_;
v_fileMap_1660_ = v_fileMap_1652_;
v_currRecDepth_1661_ = v___x_1613_;
v_ref_1662_ = v___x_1654_;
v_currNamespace_1663_ = v___x_1611_;
v_openDecls_1664_ = v___x_1635_;
v_initHeartbeats_1665_ = v___x_1613_;
v_maxHeartbeats_1666_ = v___x_1655_;
v_quotContext_1667_ = v___x_1611_;
v_currMacroScope_1668_ = v___x_1631_;
v_cancelTk_x3f_1669_ = v___x_1627_;
v_suppressElabErrors_1670_ = v_val_1623_;
v_inheritedTraceOptions_1671_ = v___x_1648_;
v___y_1672_ = v___x_1647_;
goto v___jp_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v___x_1710_ = _args[0];
lean_object* v___x_1711_ = _args[1];
lean_object* v___x_1712_ = _args[2];
lean_object* v___x_1713_ = _args[3];
lean_object* v___x_1714_ = _args[4];
lean_object* v_env_1715_ = _args[5];
lean_object* v___x_1716_ = _args[6];
lean_object* v___x_1717_ = _args[7];
lean_object* v_a_1718_ = _args[8];
lean_object* v_opts_1719_ = _args[9];
lean_object* v___x_1720_ = _args[10];
lean_object* v_pos_1721_ = _args[11];
lean_object* v_val_1722_ = _args[12];
lean_object* v___x_1723_ = _args[13];
lean_object* v___x_1724_ = _args[14];
lean_object* v___x_1725_ = _args[15];
lean_object* v___x_1726_ = _args[16];
lean_object* v___x_1727_ = _args[17];
lean_object* v_x_1728_ = _args[18];
lean_object* v___y_1729_ = _args[19];
_start:
{
size_t v___x_44899__boxed_1730_; uint8_t v___x_44900__boxed_1731_; uint8_t v_val_44904__boxed_1732_; uint8_t v___x_44909__boxed_1733_; lean_object* v_res_1734_; 
v___x_44899__boxed_1730_ = lean_unbox_usize(v___x_1713_);
lean_dec(v___x_1713_);
v___x_44900__boxed_1731_ = lean_unbox(v___x_1714_);
v_val_44904__boxed_1732_ = lean_unbox(v_val_1722_);
v___x_44909__boxed_1733_ = lean_unbox(v___x_1727_);
v_res_1734_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v___x_1710_, v___x_1711_, v___x_1712_, v___x_44899__boxed_1730_, v___x_44900__boxed_1731_, v_env_1715_, v___x_1716_, v___x_1717_, v_a_1718_, v_opts_1719_, v___x_1720_, v_pos_1721_, v_val_44904__boxed_1732_, v___x_1723_, v___x_1724_, v___x_1725_, v___x_1726_, v___x_44909__boxed_1733_, v_x_1728_);
lean_dec(v_pos_1721_);
lean_dec_ref(v_a_1718_);
lean_dec(v___x_1717_);
lean_dec(v___x_1711_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1735_, lean_object* v___x_1736_, lean_object* v_parserState_1737_, lean_object* v_x_1738_){
_start:
{
lean_object* v_toProcessingContext_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_toProcessingContext_1739_ = lean_ctor_get(v_a_1735_, 0);
v___x_1740_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1739_);
v___x_1741_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1739_, v___x_1736_, v_parserState_1737_, v___x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1742_, lean_object* v___x_1743_, lean_object* v_parserState_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1742_, v___x_1743_, v_parserState_1744_, v_x_1745_);
lean_dec_ref(v_a_1742_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1748_, size_t v_i_1749_, size_t v_stop_1750_, lean_object* v_b_1751_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_eq(v_i_1749_, v_stop_1750_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; 
v___x_1754_ = lean_array_uget_borrowed(v_as_1748_, v_i_1749_);
v___f_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
lean_inc(v___x_1754_);
v___x_1756_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1755_, v___x_1754_);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1749_, v___x_1757_);
v_i_1749_ = v___x_1758_;
v_b_1751_ = v___x_1756_;
goto _start;
}
else
{
return v_b_1751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1760_, lean_object* v_i_1761_, lean_object* v_stop_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_){
_start:
{
size_t v_i_boxed_1765_; size_t v_stop_boxed_1766_; lean_object* v_res_1767_; 
v_i_boxed_1765_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_stop_boxed_1766_ = lean_unbox_usize(v_stop_1762_);
lean_dec(v_stop_1762_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1760_, v_i_boxed_1765_, v_stop_boxed_1766_, v_b_1763_);
lean_dec_ref(v_as_1760_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1768_, lean_object* v_cmds_1769_, lean_object* v_stx_1770_, lean_object* v_newParserState_1771_, lean_object* v_val_1772_, lean_object* v_sync_1773_, lean_object* v_val_1774_, lean_object* v_a_1775_, lean_object* v_oldNext_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v_sync_boxed_1778_; lean_object* v_res_1779_; 
v_sync_boxed_1778_ = lean_unbox(v_sync_1773_);
v_res_1779_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1768_, v_cmds_1769_, v_stx_1770_, v_newParserState_1771_, v_val_1772_, v_sync_boxed_1778_, v_val_1774_, v_a_1775_, v_oldNext_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1780_, lean_object* v_cmds_1781_, lean_object* v_stx_1782_, lean_object* v_newParserState_1783_, lean_object* v_val_1784_, uint8_t v_sync_1785_, lean_object* v_val_1786_, lean_object* v_a_1787_, lean_object* v_oldResult_1788_){
_start:
{
lean_object* v_task_1790_; lean_object* v___x_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; 
v_task_1790_ = lean_ctor_get(v_val_1780_, 3);
lean_inc_ref(v_task_1790_);
lean_dec_ref(v_val_1780_);
v___x_1791_ = lean_box(v_sync_1785_);
lean_inc_ref(v_a_1787_);
v___f_1792_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1792_, 0, v_oldResult_1788_);
lean_closure_set(v___f_1792_, 1, v_cmds_1781_);
lean_closure_set(v___f_1792_, 2, v_stx_1782_);
lean_closure_set(v___f_1792_, 3, v_newParserState_1783_);
lean_closure_set(v___f_1792_, 4, v_val_1784_);
lean_closure_set(v___f_1792_, 5, v___x_1791_);
lean_closure_set(v___f_1792_, 6, v_val_1786_);
lean_closure_set(v___f_1792_, 7, v_a_1787_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = 1;
v___x_1795_ = l_BaseIO_chainTask___redArg(v_task_1790_, v___f_1792_, v___x_1793_, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1796_, lean_object* v_cmds_1797_, lean_object* v_stx_1798_, lean_object* v_newParserState_1799_, lean_object* v_val_1800_, lean_object* v_sync_1801_, lean_object* v_val_1802_, lean_object* v_a_1803_, lean_object* v_oldResult_1804_, lean_object* v___y_1805_){
_start:
{
uint8_t v_sync_boxed_1806_; lean_object* v_res_1807_; 
v_sync_boxed_1806_ = lean_unbox(v_sync_1801_);
v_res_1807_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1796_, v_cmds_1797_, v_stx_1798_, v_newParserState_1799_, v_val_1800_, v_sync_boxed_1806_, v_val_1802_, v_a_1803_, v_oldResult_1804_);
lean_dec_ref(v_a_1803_);
return v_res_1807_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1810_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1812_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1821_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1822_ = l_Lean_Name_append(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1823_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1826_, lean_object* v_val_1827_, lean_object* v_cmds_1828_, lean_object* v_fst_1829_, lean_object* v_fst_1830_, uint8_t v_val_1831_, lean_object* v_a_1832_, lean_object* v_snd_1833_, lean_object* v___x_1834_, uint8_t v___x_1835_, lean_object* v_fst_1836_, lean_object* v_val_1837_, lean_object* v_val_1838_, lean_object* v_val_1839_, lean_object* v_snd_1840_, lean_object* v_prom_1841_, lean_object* v___x_1842_, lean_object* v___f_1843_, lean_object* v___f_1844_, lean_object* v___f_1845_, lean_object* v_pos_1846_, lean_object* v_cmdState_1847_, lean_object* v_opts_1848_, lean_object* v___x_1849_, lean_object* v_old_x3f_1850_, lean_object* v_parseCancelTk_1851_, lean_object* v_next_x3f_1852_){
_start:
{
lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v_snapshotTasks_1859_; lean_object* v___y_1860_; lean_object* v_traceTask_1861_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; size_t v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v_env_1899_; lean_object* v_messages_1900_; lean_object* v_scopes_1901_; lean_object* v_infoState_1902_; lean_object* v_traceState_1903_; lean_object* v_snapshotTasks_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_reportedCmdState_1911_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; size_t v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_reportedCmdState_1968_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; size_t v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; size_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2032_; 
if (lean_obj_tag(v_next_x3f_1852_) == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref(v_parseCancelTk_1851_);
v___x_2085_ = lean_box(0);
v___y_2032_ = v___x_2085_;
goto v___jp_2031_;
}
else
{
lean_object* v_toProcessingContext_2086_; lean_object* v_val_2087_; lean_object* v_pos_2088_; lean_object* v_endPos_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_toProcessingContext_2086_ = lean_ctor_get(v_a_1832_, 0);
v_val_2087_ = lean_ctor_get(v_next_x3f_1852_, 0);
v_pos_2088_ = lean_ctor_get(v_fst_1830_, 0);
v_endPos_2089_ = lean_ctor_get(v_toProcessingContext_2086_, 3);
v___x_2090_ = lean_box(0);
lean_inc(v_endPos_2089_);
lean_inc(v_pos_2088_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_pos_2088_);
lean_ctor_set(v___x_2091_, 1, v_endPos_2089_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_parseCancelTk_1851_);
v___x_2094_ = l_IO_Promise_result_x21___redArg(v_val_2087_);
v___x_2095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2090_);
lean_ctor_set(v___x_2095_, 1, v___x_2092_);
lean_ctor_set(v___x_2095_, 2, v___x_2093_);
lean_ctor_set(v___x_2095_, 3, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___y_2032_ = v___x_2096_;
goto v___jp_2031_;
}
v___jp_1854_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1856_);
lean_ctor_set(v___x_1862_, 1, v___x_1826_);
lean_ctor_set(v___x_1862_, 2, v___y_1855_);
lean_ctor_set(v___x_1862_, 3, v_traceTask_1861_);
v___x_1863_ = lean_array_push(v_snapshotTasks_1859_, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___y_1857_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_io_promise_resolve(v___x_1864_, v_val_1827_);
if (lean_obj_tag(v_next_x3f_1852_) == 1)
{
lean_object* v_val_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_val_1866_ = lean_ctor_get(v_next_x3f_1852_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_next_x3f_1852_, 1);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_array_push(v_cmds_1828_, v_fst_1829_);
v___x_1869_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1867_, v_fst_1830_, v___y_1858_, v_val_1866_, v_val_1831_, v___y_1860_, v___x_1868_, v_a_1832_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
lean_dec_ref(v___y_1860_);
lean_dec_ref(v___y_1858_);
lean_dec(v_next_x3f_1852_);
lean_dec_ref(v_fst_1830_);
lean_dec(v_fst_1829_);
lean_dec_ref(v_cmds_1828_);
v___x_1870_ = lean_box(0);
return v___x_1870_;
}
}
v___jp_1871_:
{
lean_object* v_snapshotTasks_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_snapshotTasks_1878_ = lean_ctor_get(v___y_1876_, 10);
lean_inc_ref(v_snapshotTasks_1878_);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___y_1873_);
lean_dec(v___y_1873_);
lean_inc_ref(v___y_1875_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___y_1875_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_task_pure(v___x_1880_);
v___y_1855_ = v___y_1872_;
v___y_1856_ = v___y_1874_;
v___y_1857_ = v___y_1875_;
v___y_1858_ = v___y_1876_;
v_snapshotTasks_1859_ = v_snapshotTasks_1878_;
v___y_1860_ = v___y_1877_;
v_traceTask_1861_ = v___x_1881_;
goto v___jp_1854_;
}
v___jp_1882_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_opts_1921_; uint8_t v_hasTrace_1922_; 
v___x_1912_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1900_);
v___x_1913_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1913_, 0, v___y_1894_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
lean_ctor_set(v___x_1913_, 2, v___y_1897_);
lean_ctor_set(v___x_1913_, 3, v_traceState_1903_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*4, v_val_1831_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v_reportedCmdState_1911_);
v___x_1915_ = lean_io_promise_resolve(v___x_1914_, v_val_1838_);
v___x_1916_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1902_);
lean_inc(v___y_1907_);
v___x_1917_ = l_BaseIO_chainTask___redArg(v___x_1916_, v___y_1892_, v___y_1907_, v___x_1835_);
v___x_1918_ = l_Lean_inheritedTraceOptions;
v___x_1919_ = lean_st_ref_get(v___x_1918_);
v___x_1920_ = l_List_head_x21___redArg(v___x_1842_, v_scopes_1901_);
lean_dec(v_scopes_1901_);
lean_dec_ref(v___x_1842_);
v_opts_1921_ = lean_ctor_get(v___x_1920_, 1);
lean_inc_ref(v_opts_1921_);
lean_dec(v___x_1920_);
v_hasTrace_1922_ = lean_ctor_get_uint8(v_opts_1921_, sizeof(void*)*1);
if (v_hasTrace_1922_ == 0)
{
lean_dec_ref(v_opts_1921_);
lean_dec(v___x_1919_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v_snapshotTasks_1904_);
lean_dec_ref(v_env_1899_);
lean_dec(v___y_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v_pos_1846_);
lean_dec_ref(v___f_1845_);
lean_dec_ref(v___f_1844_);
lean_dec_ref(v___f_1843_);
lean_dec(v___x_1834_);
v___y_1872_ = v___y_1908_;
v___y_1873_ = v___y_1907_;
v___y_1874_ = v___y_1895_;
v___y_1875_ = v___y_1896_;
v___y_1876_ = v___y_1898_;
v___y_1877_ = v___y_1905_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1919_, v_opts_1921_, v___x_1923_);
lean_dec(v___x_1919_);
if (v___x_1924_ == 0)
{
lean_dec_ref(v_opts_1921_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v_snapshotTasks_1904_);
lean_dec_ref(v_env_1899_);
lean_dec(v___y_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v_pos_1846_);
lean_dec_ref(v___f_1845_);
lean_dec_ref(v___f_1844_);
lean_dec_ref(v___f_1843_);
lean_dec(v___x_1834_);
v___y_1872_ = v___y_1908_;
v___y_1873_ = v___y_1907_;
v___y_1874_ = v___y_1895_;
v___y_1875_ = v___y_1896_;
v___y_1876_ = v___y_1898_;
v___y_1877_ = v___y_1905_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; 
lean_inc_n(v___y_1907_, 3);
v___x_1925_ = lean_task_map(v___f_1843_, v___y_1906_, v___y_1907_, v___x_1835_);
lean_inc_n(v___y_1908_, 3);
lean_inc_n(v___y_1893_, 2);
lean_inc_n(v___y_1891_, 2);
v___x_1926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1891_);
lean_ctor_set(v___x_1926_, 1, v___y_1893_);
lean_ctor_set(v___x_1926_, 2, v___y_1908_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = lean_task_map(v___f_1844_, v___y_1909_, v___y_1907_, v___x_1835_);
v___x_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1891_);
lean_ctor_set(v___x_1928_, 1, v___y_1893_);
lean_ctor_set(v___x_1928_, 2, v___y_1908_);
lean_ctor_set(v___x_1928_, 3, v___x_1927_);
v___x_1929_ = lean_task_map(v___f_1845_, v___y_1910_, v___y_1907_, v___x_1835_);
v___x_1930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1930_, 0, v___y_1891_);
lean_ctor_set(v___x_1930_, 1, v___y_1893_);
lean_ctor_set(v___x_1930_, 2, v___y_1908_);
lean_ctor_set(v___x_1930_, 3, v___x_1929_);
v___x_1931_ = lean_unsigned_to_nat(3u);
v___x_1932_ = lean_mk_empty_array_with_capacity(v___x_1931_);
v___x_1933_ = lean_array_push(v___x_1932_, v___x_1926_);
v___x_1934_ = lean_array_push(v___x_1933_, v___x_1928_);
v___x_1935_ = lean_array_push(v___x_1934_, v___x_1930_);
v___x_1936_ = l_Array_append___redArg(v___x_1935_, v_snapshotTasks_1904_);
lean_inc_ref(v___y_1896_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1896_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
lean_inc_ref(v___x_1937_);
v___x_1938_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1937_);
v___x_1939_ = lean_box_usize(v___y_1887_);
v___x_1940_ = lean_box(v___x_1835_);
v___x_1941_ = lean_box(v_val_1831_);
v___x_1942_ = lean_box(v___x_1924_);
lean_inc_ref(v_a_1832_);
lean_inc_ref(v___y_1889_);
v___f_1943_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1943_, 0, v___x_1834_);
lean_closure_set(v___f_1943_, 1, v___y_1890_);
lean_closure_set(v___f_1943_, 2, v___y_1883_);
lean_closure_set(v___f_1943_, 3, v___x_1939_);
lean_closure_set(v___f_1943_, 4, v___x_1940_);
lean_closure_set(v___f_1943_, 5, v_env_1899_);
lean_closure_set(v___f_1943_, 6, v___y_1889_);
lean_closure_set(v___f_1943_, 7, v___x_1918_);
lean_closure_set(v___f_1943_, 8, v_a_1832_);
lean_closure_set(v___f_1943_, 9, v_opts_1921_);
lean_closure_set(v___f_1943_, 10, v___x_1937_);
lean_closure_set(v___f_1943_, 11, v_pos_1846_);
lean_closure_set(v___f_1943_, 12, v___x_1941_);
lean_closure_set(v___f_1943_, 13, v___y_1888_);
lean_closure_set(v___f_1943_, 14, v___y_1886_);
lean_closure_set(v___f_1943_, 15, v___y_1885_);
lean_closure_set(v___f_1943_, 16, v___y_1884_);
lean_closure_set(v___f_1943_, 17, v___x_1942_);
v___x_1944_ = lean_io_bind_task(v___x_1938_, v___f_1943_, v___y_1907_, v_val_1831_);
v___y_1855_ = v___y_1908_;
v___y_1856_ = v___y_1895_;
v___y_1857_ = v___y_1896_;
v___y_1858_ = v___y_1898_;
v_snapshotTasks_1859_ = v_snapshotTasks_1904_;
v___y_1860_ = v___y_1905_;
v_traceTask_1861_ = v___x_1944_;
goto v___jp_1854_;
}
}
}
v___jp_1945_:
{
lean_object* v_env_1969_; lean_object* v_messages_1970_; lean_object* v_scopes_1971_; lean_object* v_infoState_1972_; lean_object* v_traceState_1973_; lean_object* v_snapshotTasks_1974_; 
v_env_1969_ = lean_ctor_get(v___y_1961_, 0);
lean_inc_ref(v_env_1969_);
v_messages_1970_ = lean_ctor_get(v___y_1961_, 1);
lean_inc_ref(v_messages_1970_);
v_scopes_1971_ = lean_ctor_get(v___y_1961_, 2);
lean_inc(v_scopes_1971_);
v_infoState_1972_ = lean_ctor_get(v___y_1961_, 8);
lean_inc_ref(v_infoState_1972_);
v_traceState_1973_ = lean_ctor_get(v___y_1961_, 9);
lean_inc_ref(v_traceState_1973_);
v_snapshotTasks_1974_ = lean_ctor_get(v___y_1961_, 10);
lean_inc_ref(v_snapshotTasks_1974_);
v___y_1883_ = v___y_1946_;
v___y_1884_ = v___y_1947_;
v___y_1885_ = v___y_1949_;
v___y_1886_ = v___y_1948_;
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
v___y_1898_ = v___y_1961_;
v_env_1899_ = v_env_1969_;
v_messages_1900_ = v_messages_1970_;
v_scopes_1901_ = v_scopes_1971_;
v_infoState_1902_ = v_infoState_1972_;
v_traceState_1903_ = v_traceState_1973_;
v_snapshotTasks_1904_ = v_snapshotTasks_1974_;
v___y_1905_ = v___y_1962_;
v___y_1906_ = v___y_1963_;
v___y_1907_ = v___y_1964_;
v___y_1908_ = v___y_1965_;
v___y_1909_ = v___y_1966_;
v___y_1910_ = v___y_1967_;
v_reportedCmdState_1911_ = v_reportedCmdState_1968_;
goto v___jp_1882_;
}
v___jp_1975_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___f_2004_; uint8_t v___x_2005_; 
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___y_1999_);
lean_ctor_set(v___x_2000_, 1, v_val_1837_);
lean_inc_ref(v___y_1993_);
lean_inc_n(v_pos_1846_, 2);
lean_inc_ref(v_cmds_1828_);
lean_inc(v_fst_1829_);
v___x_2001_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1829_, v_cmds_1828_, v_cmdState_1847_, v_pos_1846_, v___x_2000_, v___y_1993_, v_a_1832_);
v___x_2002_ = lean_box(v_val_1831_);
v___x_2003_ = lean_box(v___x_1835_);
lean_inc_ref(v_a_1832_);
lean_inc(v___y_1976_);
lean_inc_ref(v___x_1842_);
lean_inc_ref(v___x_2001_);
lean_inc_ref(v___y_1982_);
lean_inc_ref(v___y_1981_);
v___f_2004_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 12, 10);
lean_closure_set(v___f_2004_, 0, v___y_1981_);
lean_closure_set(v___f_2004_, 1, v___y_1982_);
lean_closure_set(v___f_2004_, 2, v___x_2002_);
lean_closure_set(v___f_2004_, 3, v_val_1839_);
lean_closure_set(v___f_2004_, 4, v___x_2001_);
lean_closure_set(v___f_2004_, 5, v___x_1842_);
lean_closure_set(v___f_2004_, 6, v___y_1976_);
lean_closure_set(v___f_2004_, 7, v___x_2003_);
lean_closure_set(v___f_2004_, 8, v_a_1832_);
lean_closure_set(v___f_2004_, 9, v_pos_1846_);
v___x_2005_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1848_, v___x_1849_);
if (v___x_2005_ == 0)
{
lean_dec(v___y_1990_);
lean_inc_ref(v___x_2001_);
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1978_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___f_2004_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1987_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1992_;
v___y_1961_ = v___x_2001_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1996_;
v___y_1965_ = v___y_1995_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1998_;
v_reportedCmdState_1968_ = v___x_2001_;
goto v___jp_1945_;
}
else
{
uint8_t v___x_2006_; 
lean_inc(v_fst_1829_);
v___x_2006_ = l_Lean_Parser_isTerminalCommand(v_fst_1829_);
if (v___x_2006_ == 0)
{
if (v___x_2005_ == 0)
{
lean_dec(v___y_1990_);
lean_inc_ref(v___x_2001_);
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1978_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___f_2004_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1987_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1992_;
v___y_1961_ = v___x_2001_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1996_;
v___y_1965_ = v___y_1995_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1998_;
v_reportedCmdState_1968_ = v___x_2001_;
goto v___jp_1945_;
}
else
{
lean_object* v_env_2007_; lean_object* v_messages_2008_; lean_object* v_scopes_2009_; lean_object* v_infoState_2010_; lean_object* v_traceState_2011_; lean_object* v_snapshotTasks_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_env_2007_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_ref_n(v_env_2007_, 2);
v_messages_2008_ = lean_ctor_get(v___x_2001_, 1);
lean_inc_ref(v_messages_2008_);
v_scopes_2009_ = lean_ctor_get(v___x_2001_, 2);
lean_inc(v_scopes_2009_);
v_infoState_2010_ = lean_ctor_get(v___x_2001_, 8);
lean_inc_ref(v_infoState_2010_);
v_traceState_2011_ = lean_ctor_get(v___x_2001_, 9);
lean_inc_ref(v_traceState_2011_);
v_snapshotTasks_2012_ = lean_ctor_get(v___x_2001_, 10);
lean_inc_ref(v_snapshotTasks_2012_);
v___x_2013_ = lean_mk_empty_array_with_capacity(v___y_1990_);
lean_dec(v___y_1990_);
lean_inc_ref(v___x_2013_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_inc_n(v___y_1996_, 3);
v___x_2015_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
lean_ctor_set(v___x_2015_, 2, v___y_1996_);
lean_ctor_set(v___x_2015_, 3, v___y_1996_);
lean_ctor_set_usize(v___x_2015_, 4, v___y_1991_);
v___x_2016_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2015_, 2);
v___x_2017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2015_);
lean_ctor_set(v___x_2017_, 2, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2019_ = l_Lean_Options_empty;
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_mk_empty_array_with_capacity(v___y_1996_);
lean_inc_ref_n(v___x_2021_, 2);
lean_inc_n(v___x_1834_, 2);
v___x_2022_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___x_2019_);
lean_ctor_set(v___x_2022_, 2, v___x_1834_);
lean_ctor_set(v___x_2022_, 3, v___x_2020_);
lean_ctor_set(v___x_2022_, 4, v___x_2020_);
lean_ctor_set(v___x_2022_, 5, v___x_2021_);
lean_ctor_set(v___x_2022_, 6, v___x_2021_);
lean_ctor_set(v___x_2022_, 7, v___x_2020_);
lean_ctor_set(v___x_2022_, 8, v___x_2020_);
lean_ctor_set(v___x_2022_, 9, v___x_2020_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*10, v_val_1831_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*10 + 1, v_val_1831_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*10 + 2, v_val_1831_);
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_2020_);
v___x_2024_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2026_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1834_);
v___x_2027_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2028_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
lean_ctor_set(v___x_2028_, 2, v___x_2015_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*3, v___x_1835_);
v___x_2029_ = lean_box(0);
lean_inc_ref(v___y_1985_);
v___x_2030_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2030_, 0, v_env_2007_);
lean_ctor_set(v___x_2030_, 1, v___x_2017_);
lean_ctor_set(v___x_2030_, 2, v___x_2023_);
lean_ctor_set(v___x_2030_, 3, v___x_2016_);
lean_ctor_set(v___x_2030_, 4, v___x_2024_);
lean_ctor_set(v___x_2030_, 5, v___y_1996_);
lean_ctor_set(v___x_2030_, 6, v___x_2025_);
lean_ctor_set(v___x_2030_, 7, v___x_2026_);
lean_ctor_set(v___x_2030_, 8, v___x_2028_);
lean_ctor_set(v___x_2030_, 9, v___y_1985_);
lean_ctor_set(v___x_2030_, 10, v___x_2021_);
lean_ctor_set(v___x_2030_, 11, v___x_2029_);
v___y_1883_ = v___y_1976_;
v___y_1884_ = v___y_1977_;
v___y_1885_ = v___y_1978_;
v___y_1886_ = v___y_1979_;
v___y_1887_ = v___y_1980_;
v___y_1888_ = v___y_1981_;
v___y_1889_ = v___y_1982_;
v___y_1890_ = v___y_1983_;
v___y_1891_ = v___y_1984_;
v___y_1892_ = v___f_2004_;
v___y_1893_ = v___y_1986_;
v___y_1894_ = v___y_1988_;
v___y_1895_ = v___y_1987_;
v___y_1896_ = v___y_1989_;
v___y_1897_ = v___y_1992_;
v___y_1898_ = v___x_2001_;
v_env_1899_ = v_env_2007_;
v_messages_1900_ = v_messages_2008_;
v_scopes_1901_ = v_scopes_2009_;
v_infoState_1902_ = v_infoState_2010_;
v_traceState_1903_ = v_traceState_2011_;
v_snapshotTasks_1904_ = v_snapshotTasks_2012_;
v___y_1905_ = v___y_1993_;
v___y_1906_ = v___y_1994_;
v___y_1907_ = v___y_1996_;
v___y_1908_ = v___y_1995_;
v___y_1909_ = v___y_1997_;
v___y_1910_ = v___y_1998_;
v_reportedCmdState_1911_ = v___x_2030_;
goto v___jp_1882_;
}
}
else
{
lean_dec(v___y_1990_);
lean_inc_ref(v___x_2001_);
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1979_;
v___y_1949_ = v___y_1978_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___f_2004_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1987_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1992_;
v___y_1961_ = v___x_2001_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1996_;
v___y_1965_ = v___y_1995_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1998_;
v_reportedCmdState_1968_ = v___x_2001_;
goto v___jp_1945_;
}
}
}
v___jp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2033_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1833_);
v___x_2034_ = l_IO_CancelToken_new();
v___x_2035_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1834_);
v___x_2036_ = l_Lean_Name_str___override(v___x_1834_, v___x_2035_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2038_ = l_Lean_Name_str___override(v___x_2036_, v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2040_ = l_Lean_Name_str___override(v___x_2038_, v___x_2039_);
v___x_2041_ = l_Lean_Name_str___override(v___x_2040_, v___x_2037_);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = l_Lean_Name_num___override(v___x_2041_, v___x_2042_);
v___x_2044_ = l_Lean_Name_str___override(v___x_2043_, v___x_2037_);
v___x_2045_ = l_Lean_Name_str___override(v___x_2044_, v___x_2039_);
v___x_2046_ = l_Lean_Name_str___override(v___x_2045_, v___x_2037_);
v___x_2047_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2048_ = l_Lean_Name_str___override(v___x_2046_, v___x_2047_);
v___x_2049_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2050_ = l_Lean_Name_str___override(v___x_2048_, v___x_2049_);
v___x_2051_ = l_Lean_Name_toString(v___x_2050_, v___x_1835_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_unsigned_to_nat(32u);
v___x_2054_ = ((size_t)5ULL);
v___x_2055_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2051_, 2);
v___x_2056_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2056_, 0, v___x_2051_);
lean_ctor_set(v___x_2056_, 1, v___x_2033_);
lean_ctor_set(v___x_2056_, 2, v___x_2052_);
lean_ctor_set(v___x_2056_, 3, v___x_2055_);
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*4, v_val_1831_);
v___x_2057_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2058_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2058_, 0, v___x_2051_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
lean_ctor_set(v___x_2058_, 2, v___x_2052_);
lean_ctor_set(v___x_2058_, 3, v___x_2055_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*4, v_val_1831_);
lean_inc(v_fst_1836_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_fst_1836_);
v___x_2060_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2059_);
lean_inc_ref(v___x_2034_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2034_);
v___x_2062_ = l_IO_Promise_result_x21___redArg(v_val_1837_);
lean_inc_ref(v___x_2062_);
lean_inc(v___x_2060_);
lean_inc_ref_n(v___x_2059_, 3);
v___x_2063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2059_);
lean_ctor_set(v___x_2063_, 1, v___x_2060_);
lean_ctor_set(v___x_2063_, 2, v___x_2061_);
lean_ctor_set(v___x_2063_, 3, v___x_2062_);
v___x_2064_ = l_IO_Promise_result_x21___redArg(v_val_1838_);
lean_inc_ref(v___x_2064_);
lean_inc_n(v___x_1826_, 3);
v___x_2065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2059_);
lean_ctor_set(v___x_2065_, 1, v___x_1826_);
lean_ctor_set(v___x_2065_, 2, v___x_2052_);
lean_ctor_set(v___x_2065_, 3, v___x_2064_);
v___x_2066_ = l_IO_Promise_result_x21___redArg(v_val_1839_);
lean_inc_ref(v___x_2066_);
v___x_2067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2059_);
lean_ctor_set(v___x_2067_, 1, v___x_1826_);
lean_ctor_set(v___x_2067_, 2, v___x_2052_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
v___x_2068_ = l_IO_Promise_result_x21___redArg(v_val_1827_);
v___x_2069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2052_);
lean_ctor_set(v___x_2069_, 1, v___x_1826_);
lean_ctor_set(v___x_2069_, 2, v___x_2052_);
lean_ctor_set(v___x_2069_, 3, v___x_2068_);
lean_inc_ref(v___x_2058_);
v___x_2070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2058_);
lean_ctor_set(v___x_2070_, 1, v___x_2063_);
lean_ctor_set(v___x_2070_, 2, v___x_2065_);
lean_ctor_set(v___x_2070_, 3, v___x_2067_);
lean_ctor_set(v___x_2070_, 4, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2056_);
lean_ctor_set(v___x_2071_, 1, v_fst_1836_);
lean_ctor_set(v___x_2071_, 2, v_snd_1840_);
lean_ctor_set(v___x_2071_, 3, v___x_2070_);
lean_ctor_set(v___x_2071_, 4, v___y_2032_);
v___x_2072_ = lean_io_promise_resolve(v___x_2071_, v_prom_1841_);
if (lean_obj_tag(v_old_x3f_1850_) == 0)
{
lean_inc_ref(v___x_2051_);
lean_inc_ref(v___x_2058_);
v___y_1976_ = v___x_2042_;
v___y_1977_ = v___x_2052_;
v___y_1978_ = v___x_2058_;
v___y_1979_ = v___x_2052_;
v___y_1980_ = v___x_2054_;
v___y_1981_ = v___x_2051_;
v___y_1982_ = v___x_2055_;
v___y_1983_ = v___x_2053_;
v___y_1984_ = v___x_2059_;
v___y_1985_ = v___x_2055_;
v___y_1986_ = v___x_2060_;
v___y_1987_ = v___x_2052_;
v___y_1988_ = v___x_2051_;
v___y_1989_ = v___x_2058_;
v___y_1990_ = v___x_2053_;
v___y_1991_ = v___x_2054_;
v___y_1992_ = v___x_2052_;
v___y_1993_ = v___x_2034_;
v___y_1994_ = v___x_2062_;
v___y_1995_ = v___x_2052_;
v___y_1996_ = v___x_2042_;
v___y_1997_ = v___x_2064_;
v___y_1998_ = v___x_2066_;
v___y_1999_ = v___x_2052_;
goto v___jp_1975_;
}
else
{
lean_object* v_val_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2084_; 
v_val_2073_ = lean_ctor_get(v_old_x3f_1850_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_old_x3f_1850_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2075_ = v_old_x3f_1850_;
v_isShared_2076_ = v_isSharedCheck_2084_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_val_2073_);
lean_dec(v_old_x3f_1850_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2084_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_elabSnap_2077_; lean_object* v_stx_2078_; lean_object* v_elabSnap_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v_elabSnap_2077_ = lean_ctor_get(v_val_2073_, 3);
lean_inc_ref(v_elabSnap_2077_);
v_stx_2078_ = lean_ctor_get(v_val_2073_, 1);
lean_inc(v_stx_2078_);
lean_dec(v_val_2073_);
v_elabSnap_2079_ = lean_ctor_get(v_elabSnap_2077_, 1);
lean_inc_ref(v_elabSnap_2079_);
lean_dec_ref(v_elabSnap_2077_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_stx_2078_);
lean_ctor_set(v___x_2080_, 1, v_elabSnap_2079_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2080_);
v___x_2082_ = v___x_2075_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_inc_ref(v___x_2051_);
lean_inc_ref(v___x_2058_);
v___y_1976_ = v___x_2042_;
v___y_1977_ = v___x_2052_;
v___y_1978_ = v___x_2058_;
v___y_1979_ = v___x_2052_;
v___y_1980_ = v___x_2054_;
v___y_1981_ = v___x_2051_;
v___y_1982_ = v___x_2055_;
v___y_1983_ = v___x_2053_;
v___y_1984_ = v___x_2059_;
v___y_1985_ = v___x_2055_;
v___y_1986_ = v___x_2060_;
v___y_1987_ = v___x_2052_;
v___y_1988_ = v___x_2051_;
v___y_1989_ = v___x_2058_;
v___y_1990_ = v___x_2053_;
v___y_1991_ = v___x_2054_;
v___y_1992_ = v___x_2052_;
v___y_1993_ = v___x_2034_;
v___y_1994_ = v___x_2062_;
v___y_1995_ = v___x_2052_;
v___y_1996_ = v___x_2042_;
v___y_1997_ = v___x_2064_;
v___y_1998_ = v___x_2066_;
v___y_1999_ = v___x_2082_;
goto v___jp_1975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_cmds_2097_, lean_object* v_fst_2098_, lean_object* v_fst_2099_, uint8_t v_val_2100_, lean_object* v_a_2101_, lean_object* v_snd_2102_, lean_object* v___x_2103_, uint8_t v___x_2104_, lean_object* v_prom_2105_, lean_object* v___x_2106_, lean_object* v___f_2107_, lean_object* v___f_2108_, lean_object* v___f_2109_, lean_object* v_pos_2110_, lean_object* v_cmdState_2111_, lean_object* v_opts_2112_, lean_object* v_old_x3f_2113_, lean_object* v_parseCancelTk_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v_snapshotTasks_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v_traceTask_2129_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; size_t v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v_env_2175_; lean_object* v_messages_2176_; lean_object* v_scopes_2177_; lean_object* v_infoState_2178_; lean_object* v_traceState_2179_; lean_object* v_snapshotTasks_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v_reportedCmdState_2183_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; size_t v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v_reportedCmdState_2242_; lean_object* v___x_2249_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; size_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; size_t v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v_fst_2387_; lean_object* v_snd_2388_; uint8_t v___y_2401_; uint8_t v___x_2404_; 
v___x_2116_ = lean_io_promise_new();
v___x_2117_ = lean_io_promise_new();
v___x_2118_ = lean_io_promise_new();
v___x_2119_ = lean_io_promise_new();
v___x_2249_ = l_Lean_internal_cmdlineSnapshots;
v___x_2404_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2112_, v___x_2249_);
if (v___x_2404_ == 0)
{
v___y_2401_ = v___x_2404_;
goto v___jp_2400_;
}
else
{
uint8_t v___x_2405_; 
lean_inc(v_fst_2098_);
v___x_2405_ = l_Lean_Parser_isTerminalCommand(v_fst_2098_);
if (v___x_2405_ == 0)
{
v___y_2401_ = v___x_2404_;
goto v___jp_2400_;
}
else
{
lean_inc_ref(v_fst_2099_);
lean_inc(v_fst_2098_);
v_fst_2387_ = v_fst_2098_;
v_snd_2388_ = v_fst_2099_;
goto v___jp_2386_;
}
}
v___jp_2120_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2130_, 0, v___y_2124_);
lean_ctor_set(v___x_2130_, 1, v___y_2123_);
lean_ctor_set(v___x_2130_, 2, v___y_2122_);
lean_ctor_set(v___x_2130_, 3, v_traceTask_2129_);
v___x_2131_ = lean_array_push(v_snapshotTasks_2126_, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___y_2128_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_io_promise_resolve(v___x_2132_, v___x_2119_);
lean_dec(v___x_2119_);
if (lean_obj_tag(v___y_2127_) == 1)
{
lean_object* v_val_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_val_2134_ = lean_ctor_get(v___y_2127_, 0);
lean_inc(v_val_2134_);
lean_dec_ref_known(v___y_2127_, 1);
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_array_push(v_cmds_2097_, v_fst_2098_);
v___x_2137_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2135_, v_fst_2099_, v___y_2125_, v_val_2134_, v_val_2100_, v___y_2121_, v___x_2136_, v_a_2101_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; 
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v_fst_2099_);
lean_dec(v_fst_2098_);
lean_dec_ref(v_cmds_2097_);
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
}
v___jp_2139_:
{
lean_object* v_snapshotTasks_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_snapshotTasks_2148_ = lean_ctor_get(v___y_2144_, 10);
lean_inc_ref(v_snapshotTasks_2148_);
v___x_2149_ = lean_mk_empty_array_with_capacity(v___y_2145_);
lean_dec(v___y_2145_);
lean_inc_ref(v___y_2147_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___y_2147_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_task_pure(v___x_2150_);
v___y_2121_ = v___y_2140_;
v___y_2122_ = v___y_2142_;
v___y_2123_ = v___y_2141_;
v___y_2124_ = v___y_2143_;
v___y_2125_ = v___y_2144_;
v_snapshotTasks_2126_ = v_snapshotTasks_2148_;
v___y_2127_ = v___y_2146_;
v___y_2128_ = v___y_2147_;
v_traceTask_2129_ = v___x_2151_;
goto v___jp_2120_;
}
v___jp_2152_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_opts_2193_; uint8_t v_hasTrace_2194_; 
v___x_2184_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2176_);
v___x_2185_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2185_, 0, v___y_2162_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
lean_ctor_set(v___x_2185_, 2, v___y_2163_);
lean_ctor_set(v___x_2185_, 3, v_traceState_2179_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*4, v_val_2100_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v_reportedCmdState_2183_);
v___x_2187_ = lean_io_promise_resolve(v___x_2186_, v___x_2117_);
lean_dec(v___x_2117_);
v___x_2188_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2178_);
lean_inc(v___y_2181_);
v___x_2189_ = l_BaseIO_chainTask___redArg(v___x_2188_, v___y_2173_, v___y_2181_, v___x_2104_);
v___x_2190_ = l_Lean_inheritedTraceOptions;
v___x_2191_ = lean_st_ref_get(v___x_2190_);
v___x_2192_ = l_List_head_x21___redArg(v___x_2106_, v_scopes_2177_);
lean_dec(v_scopes_2177_);
lean_dec_ref(v___x_2106_);
v_opts_2193_ = lean_ctor_get(v___x_2192_, 1);
lean_inc_ref(v_opts_2193_);
lean_dec(v___x_2192_);
v_hasTrace_2194_ = lean_ctor_get_uint8(v_opts_2193_, sizeof(void*)*1);
if (v_hasTrace_2194_ == 0)
{
lean_dec_ref(v_opts_2193_);
lean_dec(v___x_2191_);
lean_dec_ref(v_snapshotTasks_2180_);
lean_dec_ref(v_env_2175_);
lean_dec(v___y_2172_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v_pos_2110_);
lean_dec_ref(v___f_2109_);
lean_dec_ref(v___f_2108_);
lean_dec_ref(v___f_2107_);
lean_dec(v___x_2103_);
v___y_2140_ = v___y_2161_;
v___y_2141_ = v___y_2170_;
v___y_2142_ = v___y_2171_;
v___y_2143_ = v___y_2166_;
v___y_2144_ = v___y_2174_;
v___y_2145_ = v___y_2181_;
v___y_2146_ = v___y_2169_;
v___y_2147_ = v___y_2182_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2196_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2191_, v_opts_2193_, v___x_2195_);
lean_dec(v___x_2191_);
if (v___x_2196_ == 0)
{
lean_dec_ref(v_opts_2193_);
lean_dec_ref(v_snapshotTasks_2180_);
lean_dec_ref(v_env_2175_);
lean_dec(v___y_2172_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v_pos_2110_);
lean_dec_ref(v___f_2109_);
lean_dec_ref(v___f_2108_);
lean_dec_ref(v___f_2107_);
lean_dec(v___x_2103_);
v___y_2140_ = v___y_2161_;
v___y_2141_ = v___y_2170_;
v___y_2142_ = v___y_2171_;
v___y_2143_ = v___y_2166_;
v___y_2144_ = v___y_2174_;
v___y_2145_ = v___y_2181_;
v___y_2146_ = v___y_2169_;
v___y_2147_ = v___y_2182_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
lean_inc_n(v___y_2181_, 3);
v___x_2197_ = lean_task_map(v___f_2107_, v___y_2164_, v___y_2181_, v___x_2104_);
lean_inc_n(v___y_2171_, 3);
lean_inc_n(v___y_2168_, 2);
lean_inc_n(v___y_2172_, 2);
v___x_2198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2198_, 0, v___y_2172_);
lean_ctor_set(v___x_2198_, 1, v___y_2168_);
lean_ctor_set(v___x_2198_, 2, v___y_2171_);
lean_ctor_set(v___x_2198_, 3, v___x_2197_);
v___x_2199_ = lean_task_map(v___f_2108_, v___y_2167_, v___y_2181_, v___x_2104_);
v___x_2200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2200_, 0, v___y_2172_);
lean_ctor_set(v___x_2200_, 1, v___y_2168_);
lean_ctor_set(v___x_2200_, 2, v___y_2171_);
lean_ctor_set(v___x_2200_, 3, v___x_2199_);
v___x_2201_ = lean_task_map(v___f_2109_, v___y_2165_, v___y_2181_, v___x_2104_);
v___x_2202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2202_, 0, v___y_2172_);
lean_ctor_set(v___x_2202_, 1, v___y_2168_);
lean_ctor_set(v___x_2202_, 2, v___y_2171_);
lean_ctor_set(v___x_2202_, 3, v___x_2201_);
v___x_2203_ = lean_unsigned_to_nat(3u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
v___x_2205_ = lean_array_push(v___x_2204_, v___x_2198_);
v___x_2206_ = lean_array_push(v___x_2205_, v___x_2200_);
v___x_2207_ = lean_array_push(v___x_2206_, v___x_2202_);
v___x_2208_ = l_Array_append___redArg(v___x_2207_, v_snapshotTasks_2180_);
lean_inc_ref(v___y_2182_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___y_2182_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_inc_ref(v___x_2209_);
v___x_2210_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2209_);
v___x_2211_ = lean_box_usize(v___y_2160_);
v___x_2212_ = lean_box(v___x_2104_);
v___x_2213_ = lean_box(v_val_2100_);
v___x_2214_ = lean_box(v___x_2196_);
lean_inc_ref(v_a_2101_);
lean_inc_ref(v___y_2153_);
v___f_2215_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2215_, 0, v___x_2103_);
lean_closure_set(v___f_2215_, 1, v___y_2154_);
lean_closure_set(v___f_2215_, 2, v___y_2157_);
lean_closure_set(v___f_2215_, 3, v___x_2211_);
lean_closure_set(v___f_2215_, 4, v___x_2212_);
lean_closure_set(v___f_2215_, 5, v_env_2175_);
lean_closure_set(v___f_2215_, 6, v___y_2153_);
lean_closure_set(v___f_2215_, 7, v___x_2190_);
lean_closure_set(v___f_2215_, 8, v_a_2101_);
lean_closure_set(v___f_2215_, 9, v_opts_2193_);
lean_closure_set(v___f_2215_, 10, v___x_2209_);
lean_closure_set(v___f_2215_, 11, v_pos_2110_);
lean_closure_set(v___f_2215_, 12, v___x_2213_);
lean_closure_set(v___f_2215_, 13, v___y_2155_);
lean_closure_set(v___f_2215_, 14, v___y_2158_);
lean_closure_set(v___f_2215_, 15, v___y_2159_);
lean_closure_set(v___f_2215_, 16, v___y_2156_);
lean_closure_set(v___f_2215_, 17, v___x_2214_);
v___x_2216_ = lean_io_bind_task(v___x_2210_, v___f_2215_, v___y_2181_, v_val_2100_);
v___y_2121_ = v___y_2161_;
v___y_2122_ = v___y_2171_;
v___y_2123_ = v___y_2170_;
v___y_2124_ = v___y_2166_;
v___y_2125_ = v___y_2174_;
v_snapshotTasks_2126_ = v_snapshotTasks_2180_;
v___y_2127_ = v___y_2169_;
v___y_2128_ = v___y_2182_;
v_traceTask_2129_ = v___x_2216_;
goto v___jp_2120_;
}
}
}
v___jp_2217_:
{
lean_object* v_env_2243_; lean_object* v_messages_2244_; lean_object* v_scopes_2245_; lean_object* v_infoState_2246_; lean_object* v_traceState_2247_; lean_object* v_snapshotTasks_2248_; 
v_env_2243_ = lean_ctor_get(v___y_2239_, 0);
lean_inc_ref(v_env_2243_);
v_messages_2244_ = lean_ctor_get(v___y_2239_, 1);
lean_inc_ref(v_messages_2244_);
v_scopes_2245_ = lean_ctor_get(v___y_2239_, 2);
lean_inc(v_scopes_2245_);
v_infoState_2246_ = lean_ctor_get(v___y_2239_, 8);
lean_inc_ref(v_infoState_2246_);
v_traceState_2247_ = lean_ctor_get(v___y_2239_, 9);
lean_inc_ref(v_traceState_2247_);
v_snapshotTasks_2248_ = lean_ctor_get(v___y_2239_, 10);
lean_inc_ref(v_snapshotTasks_2248_);
v___y_2153_ = v___y_2219_;
v___y_2154_ = v___y_2218_;
v___y_2155_ = v___y_2220_;
v___y_2156_ = v___y_2221_;
v___y_2157_ = v___y_2222_;
v___y_2158_ = v___y_2223_;
v___y_2159_ = v___y_2225_;
v___y_2160_ = v___y_2224_;
v___y_2161_ = v___y_2226_;
v___y_2162_ = v___y_2227_;
v___y_2163_ = v___y_2228_;
v___y_2164_ = v___y_2229_;
v___y_2165_ = v___y_2230_;
v___y_2166_ = v___y_2231_;
v___y_2167_ = v___y_2232_;
v___y_2168_ = v___y_2233_;
v___y_2169_ = v___y_2234_;
v___y_2170_ = v___y_2235_;
v___y_2171_ = v___y_2236_;
v___y_2172_ = v___y_2237_;
v___y_2173_ = v___y_2238_;
v___y_2174_ = v___y_2239_;
v_env_2175_ = v_env_2243_;
v_messages_2176_ = v_messages_2244_;
v_scopes_2177_ = v_scopes_2245_;
v_infoState_2178_ = v_infoState_2246_;
v_traceState_2179_ = v_traceState_2247_;
v_snapshotTasks_2180_ = v_snapshotTasks_2248_;
v___y_2181_ = v___y_2240_;
v___y_2182_ = v___y_2241_;
v_reportedCmdState_2183_ = v_reportedCmdState_2242_;
goto v___jp_2152_;
}
v___jp_2250_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; uint8_t v___x_2282_; 
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___y_2276_);
lean_ctor_set(v___x_2277_, 1, v___x_2116_);
lean_inc_ref(v___y_2259_);
lean_inc_n(v_pos_2110_, 2);
lean_inc_ref(v_cmds_2097_);
lean_inc(v_fst_2098_);
v___x_2278_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2098_, v_cmds_2097_, v_cmdState_2111_, v_pos_2110_, v___x_2277_, v___y_2259_, v_a_2101_);
v___x_2279_ = lean_box(v_val_2100_);
v___x_2280_ = lean_box(v___x_2104_);
lean_inc_ref(v_a_2101_);
lean_inc(v___y_2255_);
lean_inc_ref(v___x_2106_);
lean_inc_ref(v___x_2278_);
lean_inc_ref(v___y_2252_);
lean_inc_ref(v___y_2253_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 12, 10);
lean_closure_set(v___f_2281_, 0, v___y_2253_);
lean_closure_set(v___f_2281_, 1, v___y_2252_);
lean_closure_set(v___f_2281_, 2, v___x_2279_);
lean_closure_set(v___f_2281_, 3, v___x_2118_);
lean_closure_set(v___f_2281_, 4, v___x_2278_);
lean_closure_set(v___f_2281_, 5, v___x_2106_);
lean_closure_set(v___f_2281_, 6, v___y_2255_);
lean_closure_set(v___f_2281_, 7, v___x_2280_);
lean_closure_set(v___f_2281_, 8, v_a_2101_);
lean_closure_set(v___f_2281_, 9, v_pos_2110_);
v___x_2282_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2112_, v___x_2249_);
if (v___x_2282_ == 0)
{
lean_dec(v___y_2272_);
lean_inc_ref(v___x_2278_);
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2254_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2258_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2262_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2270_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2271_;
v___y_2238_ = v___f_2281_;
v___y_2239_ = v___x_2278_;
v___y_2240_ = v___y_2274_;
v___y_2241_ = v___y_2275_;
v_reportedCmdState_2242_ = v___x_2278_;
goto v___jp_2217_;
}
else
{
uint8_t v___x_2283_; 
lean_inc(v_fst_2098_);
v___x_2283_ = l_Lean_Parser_isTerminalCommand(v_fst_2098_);
if (v___x_2283_ == 0)
{
if (v___x_2282_ == 0)
{
lean_dec(v___y_2272_);
lean_inc_ref(v___x_2278_);
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2254_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2258_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2262_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2270_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2271_;
v___y_2238_ = v___f_2281_;
v___y_2239_ = v___x_2278_;
v___y_2240_ = v___y_2274_;
v___y_2241_ = v___y_2275_;
v_reportedCmdState_2242_ = v___x_2278_;
goto v___jp_2217_;
}
else
{
lean_object* v_env_2284_; lean_object* v_messages_2285_; lean_object* v_scopes_2286_; lean_object* v_infoState_2287_; lean_object* v_traceState_2288_; lean_object* v_snapshotTasks_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_env_2284_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref_n(v_env_2284_, 2);
v_messages_2285_ = lean_ctor_get(v___x_2278_, 1);
lean_inc_ref(v_messages_2285_);
v_scopes_2286_ = lean_ctor_get(v___x_2278_, 2);
lean_inc(v_scopes_2286_);
v_infoState_2287_ = lean_ctor_get(v___x_2278_, 8);
lean_inc_ref(v_infoState_2287_);
v_traceState_2288_ = lean_ctor_get(v___x_2278_, 9);
lean_inc_ref(v_traceState_2288_);
v_snapshotTasks_2289_ = lean_ctor_get(v___x_2278_, 10);
lean_inc_ref(v_snapshotTasks_2289_);
v___x_2290_ = lean_mk_empty_array_with_capacity(v___y_2272_);
lean_dec(v___y_2272_);
lean_inc_ref(v___x_2290_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_inc_n(v___y_2274_, 3);
v___x_2292_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_2290_);
lean_ctor_set(v___x_2292_, 2, v___y_2274_);
lean_ctor_set(v___x_2292_, 3, v___y_2274_);
lean_ctor_set_usize(v___x_2292_, 4, v___y_2268_);
v___x_2293_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2292_, 2);
v___x_2294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2292_);
lean_ctor_set(v___x_2294_, 2, v___x_2293_);
v___x_2295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2296_ = l_Lean_Options_empty;
v___x_2297_ = lean_box(0);
v___x_2298_ = lean_mk_empty_array_with_capacity(v___y_2274_);
lean_inc_ref_n(v___x_2298_, 2);
lean_inc_n(v___x_2103_, 2);
v___x_2299_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2299_, 0, v___x_2295_);
lean_ctor_set(v___x_2299_, 1, v___x_2296_);
lean_ctor_set(v___x_2299_, 2, v___x_2103_);
lean_ctor_set(v___x_2299_, 3, v___x_2297_);
lean_ctor_set(v___x_2299_, 4, v___x_2297_);
lean_ctor_set(v___x_2299_, 5, v___x_2298_);
lean_ctor_set(v___x_2299_, 6, v___x_2298_);
lean_ctor_set(v___x_2299_, 7, v___x_2297_);
lean_ctor_set(v___x_2299_, 8, v___x_2297_);
lean_ctor_set(v___x_2299_, 9, v___x_2297_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*10, v_val_2100_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*10 + 1, v_val_2100_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*10 + 2, v_val_2100_);
v___x_2300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2297_);
v___x_2301_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2302_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2303_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2103_);
v___x_2304_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2305_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
lean_ctor_set(v___x_2305_, 2, v___x_2292_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*3, v___x_2104_);
v___x_2306_ = lean_box(0);
lean_inc_ref(v___y_2273_);
v___x_2307_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2307_, 0, v_env_2284_);
lean_ctor_set(v___x_2307_, 1, v___x_2294_);
lean_ctor_set(v___x_2307_, 2, v___x_2300_);
lean_ctor_set(v___x_2307_, 3, v___x_2293_);
lean_ctor_set(v___x_2307_, 4, v___x_2301_);
lean_ctor_set(v___x_2307_, 5, v___y_2274_);
lean_ctor_set(v___x_2307_, 6, v___x_2302_);
lean_ctor_set(v___x_2307_, 7, v___x_2303_);
lean_ctor_set(v___x_2307_, 8, v___x_2305_);
lean_ctor_set(v___x_2307_, 9, v___y_2273_);
lean_ctor_set(v___x_2307_, 10, v___x_2298_);
lean_ctor_set(v___x_2307_, 11, v___x_2306_);
v___y_2153_ = v___y_2252_;
v___y_2154_ = v___y_2251_;
v___y_2155_ = v___y_2253_;
v___y_2156_ = v___y_2254_;
v___y_2157_ = v___y_2255_;
v___y_2158_ = v___y_2256_;
v___y_2159_ = v___y_2257_;
v___y_2160_ = v___y_2258_;
v___y_2161_ = v___y_2259_;
v___y_2162_ = v___y_2260_;
v___y_2163_ = v___y_2261_;
v___y_2164_ = v___y_2262_;
v___y_2165_ = v___y_2263_;
v___y_2166_ = v___y_2264_;
v___y_2167_ = v___y_2265_;
v___y_2168_ = v___y_2266_;
v___y_2169_ = v___y_2267_;
v___y_2170_ = v___y_2270_;
v___y_2171_ = v___y_2269_;
v___y_2172_ = v___y_2271_;
v___y_2173_ = v___f_2281_;
v___y_2174_ = v___x_2278_;
v_env_2175_ = v_env_2284_;
v_messages_2176_ = v_messages_2285_;
v_scopes_2177_ = v_scopes_2286_;
v_infoState_2178_ = v_infoState_2287_;
v_traceState_2179_ = v_traceState_2288_;
v_snapshotTasks_2180_ = v_snapshotTasks_2289_;
v___y_2181_ = v___y_2274_;
v___y_2182_ = v___y_2275_;
v_reportedCmdState_2183_ = v___x_2307_;
goto v___jp_2152_;
}
}
else
{
lean_dec(v___y_2272_);
lean_inc_ref(v___x_2278_);
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2254_;
v___y_2222_ = v___y_2255_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2258_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2262_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2270_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2271_;
v___y_2238_ = v___f_2281_;
v___y_2239_ = v___x_2278_;
v___y_2240_ = v___y_2274_;
v___y_2241_ = v___y_2275_;
v_reportedCmdState_2242_ = v___x_2278_;
goto v___jp_2217_;
}
}
}
v___jp_2308_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; size_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2314_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2102_);
v___x_2315_ = l_IO_CancelToken_new();
v___x_2316_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2103_);
v___x_2317_ = l_Lean_Name_str___override(v___x_2103_, v___x_2316_);
v___x_2318_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2319_ = l_Lean_Name_str___override(v___x_2317_, v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2321_ = l_Lean_Name_str___override(v___x_2319_, v___x_2320_);
v___x_2322_ = l_Lean_Name_str___override(v___x_2321_, v___x_2318_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = l_Lean_Name_num___override(v___x_2322_, v___x_2323_);
v___x_2325_ = l_Lean_Name_str___override(v___x_2324_, v___x_2318_);
v___x_2326_ = l_Lean_Name_str___override(v___x_2325_, v___x_2320_);
v___x_2327_ = l_Lean_Name_str___override(v___x_2326_, v___x_2318_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2329_ = l_Lean_Name_str___override(v___x_2327_, v___x_2328_);
v___x_2330_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2331_ = l_Lean_Name_str___override(v___x_2329_, v___x_2330_);
v___x_2332_ = l_Lean_Name_toString(v___x_2331_, v___x_2104_);
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_unsigned_to_nat(32u);
v___x_2335_ = lean_mk_empty_array_with_capacity(v___x_2334_);
lean_dec_ref(v___x_2335_);
v___x_2336_ = ((size_t)5ULL);
v___x_2337_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2332_, 2);
v___x_2338_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2332_);
lean_ctor_set(v___x_2338_, 1, v___x_2314_);
lean_ctor_set(v___x_2338_, 2, v___x_2333_);
lean_ctor_set(v___x_2338_, 3, v___x_2337_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*4, v_val_2100_);
v___x_2339_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2340_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2340_, 0, v___x_2332_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
lean_ctor_set(v___x_2340_, 2, v___x_2333_);
lean_ctor_set(v___x_2340_, 3, v___x_2337_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*4, v_val_2100_);
lean_inc(v___y_2311_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___y_2311_);
v___x_2342_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2341_);
lean_inc_ref(v___x_2315_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2315_);
v___x_2344_ = l_IO_Promise_result_x21___redArg(v___x_2116_);
lean_inc_ref(v___x_2344_);
lean_inc(v___x_2342_);
lean_inc_ref_n(v___x_2341_, 3);
v___x_2345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2341_);
lean_ctor_set(v___x_2345_, 1, v___x_2342_);
lean_ctor_set(v___x_2345_, 2, v___x_2343_);
lean_ctor_set(v___x_2345_, 3, v___x_2344_);
v___x_2346_ = l_IO_Promise_result_x21___redArg(v___x_2117_);
lean_inc_ref(v___x_2346_);
lean_inc_n(v___y_2309_, 3);
v___x_2347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2341_);
lean_ctor_set(v___x_2347_, 1, v___y_2309_);
lean_ctor_set(v___x_2347_, 2, v___x_2333_);
lean_ctor_set(v___x_2347_, 3, v___x_2346_);
v___x_2348_ = l_IO_Promise_result_x21___redArg(v___x_2118_);
lean_inc_ref(v___x_2348_);
v___x_2349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2341_);
lean_ctor_set(v___x_2349_, 1, v___y_2309_);
lean_ctor_set(v___x_2349_, 2, v___x_2333_);
lean_ctor_set(v___x_2349_, 3, v___x_2348_);
v___x_2350_ = l_IO_Promise_result_x21___redArg(v___x_2119_);
v___x_2351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2333_);
lean_ctor_set(v___x_2351_, 1, v___y_2309_);
lean_ctor_set(v___x_2351_, 2, v___x_2333_);
lean_ctor_set(v___x_2351_, 3, v___x_2350_);
lean_inc_ref(v___x_2340_);
v___x_2352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2340_);
lean_ctor_set(v___x_2352_, 1, v___x_2345_);
lean_ctor_set(v___x_2352_, 2, v___x_2347_);
lean_ctor_set(v___x_2352_, 3, v___x_2349_);
lean_ctor_set(v___x_2352_, 4, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2338_);
lean_ctor_set(v___x_2353_, 1, v___y_2311_);
lean_ctor_set(v___x_2353_, 2, v___y_2310_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
lean_ctor_set(v___x_2353_, 4, v___y_2313_);
v___x_2354_ = lean_io_promise_resolve(v___x_2353_, v_prom_2105_);
if (lean_obj_tag(v_old_x3f_2113_) == 0)
{
lean_inc_ref(v___x_2340_);
lean_inc_ref(v___x_2332_);
v___y_2251_ = v___x_2334_;
v___y_2252_ = v___x_2337_;
v___y_2253_ = v___x_2332_;
v___y_2254_ = v___x_2333_;
v___y_2255_ = v___x_2323_;
v___y_2256_ = v___x_2333_;
v___y_2257_ = v___x_2340_;
v___y_2258_ = v___x_2336_;
v___y_2259_ = v___x_2315_;
v___y_2260_ = v___x_2332_;
v___y_2261_ = v___x_2333_;
v___y_2262_ = v___x_2344_;
v___y_2263_ = v___x_2348_;
v___y_2264_ = v___x_2333_;
v___y_2265_ = v___x_2346_;
v___y_2266_ = v___x_2342_;
v___y_2267_ = v___y_2312_;
v___y_2268_ = v___x_2336_;
v___y_2269_ = v___x_2333_;
v___y_2270_ = v___y_2309_;
v___y_2271_ = v___x_2341_;
v___y_2272_ = v___x_2334_;
v___y_2273_ = v___x_2337_;
v___y_2274_ = v___x_2323_;
v___y_2275_ = v___x_2340_;
v___y_2276_ = v___x_2333_;
goto v___jp_2250_;
}
else
{
lean_object* v_val_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2366_; 
v_val_2355_ = lean_ctor_get(v_old_x3f_2113_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_old_x3f_2113_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2357_ = v_old_x3f_2113_;
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_val_2355_);
lean_dec(v_old_x3f_2113_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_elabSnap_2359_; lean_object* v_stx_2360_; lean_object* v_elabSnap_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v_elabSnap_2359_ = lean_ctor_get(v_val_2355_, 3);
lean_inc_ref(v_elabSnap_2359_);
v_stx_2360_ = lean_ctor_get(v_val_2355_, 1);
lean_inc(v_stx_2360_);
lean_dec(v_val_2355_);
v_elabSnap_2361_ = lean_ctor_get(v_elabSnap_2359_, 1);
lean_inc_ref(v_elabSnap_2361_);
lean_dec_ref(v_elabSnap_2359_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_stx_2360_);
lean_ctor_set(v___x_2362_, 1, v_elabSnap_2361_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2362_);
v___x_2364_ = v___x_2357_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_inc_ref(v___x_2340_);
lean_inc_ref(v___x_2332_);
v___y_2251_ = v___x_2334_;
v___y_2252_ = v___x_2337_;
v___y_2253_ = v___x_2332_;
v___y_2254_ = v___x_2333_;
v___y_2255_ = v___x_2323_;
v___y_2256_ = v___x_2333_;
v___y_2257_ = v___x_2340_;
v___y_2258_ = v___x_2336_;
v___y_2259_ = v___x_2315_;
v___y_2260_ = v___x_2332_;
v___y_2261_ = v___x_2333_;
v___y_2262_ = v___x_2344_;
v___y_2263_ = v___x_2348_;
v___y_2264_ = v___x_2333_;
v___y_2265_ = v___x_2346_;
v___y_2266_ = v___x_2342_;
v___y_2267_ = v___y_2312_;
v___y_2268_ = v___x_2336_;
v___y_2269_ = v___x_2333_;
v___y_2270_ = v___y_2309_;
v___y_2271_ = v___x_2341_;
v___y_2272_ = v___x_2334_;
v___y_2273_ = v___x_2337_;
v___y_2274_ = v___x_2323_;
v___y_2275_ = v___x_2340_;
v___y_2276_ = v___x_2364_;
goto v___jp_2250_;
}
}
}
}
v___jp_2367_:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2370_);
lean_inc(v_fst_2098_);
v___x_2372_ = l_Lean_Parser_isTerminalCommand(v_fst_2098_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v_toProcessingContext_2374_; lean_object* v_pos_2375_; lean_object* v_endPos_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2373_ = lean_io_promise_new();
v_toProcessingContext_2374_ = lean_ctor_get(v_a_2101_, 0);
v_pos_2375_ = lean_ctor_get(v_fst_2099_, 0);
v_endPos_2376_ = lean_ctor_get(v_toProcessingContext_2374_, 3);
lean_inc(v___x_2373_);
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2373_);
v___x_2378_ = lean_box(0);
lean_inc(v_endPos_2376_);
lean_inc(v_pos_2375_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_pos_2375_);
lean_ctor_set(v___x_2379_, 1, v_endPos_2376_);
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_parseCancelTk_2114_);
v___x_2382_ = l_IO_Promise_result_x21___redArg(v___x_2373_);
lean_dec(v___x_2373_);
v___x_2383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2378_);
lean_ctor_set(v___x_2383_, 1, v___x_2380_);
lean_ctor_set(v___x_2383_, 2, v___x_2381_);
lean_ctor_set(v___x_2383_, 3, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
v___y_2309_ = v___x_2371_;
v___y_2310_ = v___y_2368_;
v___y_2311_ = v___y_2369_;
v___y_2312_ = v___x_2377_;
v___y_2313_ = v___x_2384_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2385_; 
lean_dec_ref(v_parseCancelTk_2114_);
v___x_2385_ = lean_box(0);
v___y_2309_ = v___x_2371_;
v___y_2310_ = v___y_2368_;
v___y_2311_ = v___y_2369_;
v___y_2312_ = v___x_2385_;
v___y_2313_ = v___x_2385_;
goto v___jp_2308_;
}
}
v___jp_2386_:
{
lean_object* v___x_2389_; 
lean_inc(v_fst_2098_);
v___x_2389_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2098_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_box(0);
v___y_2368_ = v_snd_2388_;
v___y_2369_ = v_fst_2387_;
v___y_2370_ = v___x_2390_;
goto v___jp_2367_;
}
else
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_val_2391_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2393_ = v___x_2389_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v___x_2389_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_inc(v_val_2391_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_val_2391_);
lean_ctor_set(v___x_2395_, 1, v_val_2391_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
v___y_2368_ = v_snd_2388_;
v___y_2369_ = v_fst_2387_;
v___y_2370_ = v___x_2397_;
goto v___jp_2367_;
}
}
}
}
v___jp_2400_:
{
if (v___y_2401_ == 0)
{
lean_inc_ref(v_fst_2099_);
lean_inc(v_fst_2098_);
v_fst_2387_ = v_fst_2098_;
v_snd_2388_ = v_fst_2099_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_box(0);
v___x_2403_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2387_ = v___x_2402_;
v_snd_2388_ = v___x_2403_;
goto v___jp_2386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_cmds_2406_ = _args[0];
lean_object* v_fst_2407_ = _args[1];
lean_object* v_fst_2408_ = _args[2];
lean_object* v_val_2409_ = _args[3];
lean_object* v_a_2410_ = _args[4];
lean_object* v_snd_2411_ = _args[5];
lean_object* v___x_2412_ = _args[6];
lean_object* v___x_2413_ = _args[7];
lean_object* v_prom_2414_ = _args[8];
lean_object* v___x_2415_ = _args[9];
lean_object* v___f_2416_ = _args[10];
lean_object* v___f_2417_ = _args[11];
lean_object* v___f_2418_ = _args[12];
lean_object* v_pos_2419_ = _args[13];
lean_object* v_cmdState_2420_ = _args[14];
lean_object* v_opts_2421_ = _args[15];
lean_object* v_old_x3f_2422_ = _args[16];
lean_object* v_parseCancelTk_2423_ = _args[17];
lean_object* v___y_2424_ = _args[18];
_start:
{
uint8_t v_val_45551__boxed_2425_; uint8_t v___x_45554__boxed_2426_; lean_object* v_res_2427_; 
v_val_45551__boxed_2425_ = lean_unbox(v_val_2409_);
v___x_45554__boxed_2426_ = lean_unbox(v___x_2413_);
v_res_2427_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_cmds_2406_, v_fst_2407_, v_fst_2408_, v_val_45551__boxed_2425_, v_a_2410_, v_snd_2411_, v___x_2412_, v___x_45554__boxed_2426_, v_prom_2414_, v___x_2415_, v___f_2416_, v___f_2417_, v___f_2418_, v_pos_2419_, v_cmdState_2420_, v_opts_2421_, v_old_x3f_2422_, v_parseCancelTk_2423_);
lean_dec_ref(v_opts_2421_);
lean_dec(v_prom_2414_);
lean_dec_ref(v_a_2410_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2430_, lean_object* v_parserState_2431_, lean_object* v_cmdState_2432_, lean_object* v_prom_2433_, uint8_t v_sync_2434_, lean_object* v_parseCancelTk_2435_, lean_object* v_cmds_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_toSnapshot_2440_; lean_object* v_stx_2441_; lean_object* v_parserState_2442_; lean_object* v_elabSnap_2443_; lean_object* v_val_2444_; lean_object* v_newParserState_2445_; lean_object* v___y_2479_; lean_object* v___y_2481_; uint8_t v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___f_2523_; lean_object* v___x_2524_; uint8_t v___y_2526_; lean_object* v___y_2527_; uint8_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___y_2551_; lean_object* v___y_2552_; uint8_t v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; uint8_t v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2594_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; 
v___f_2521_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2522_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2523_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2524_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2430_) == 1)
{
lean_object* v_val_2669_; lean_object* v_nextCmdSnap_x3f_2670_; 
v_val_2669_ = lean_ctor_get(v_old_x3f_2430_, 0);
v_nextCmdSnap_x3f_2670_ = lean_ctor_get(v_val_2669_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2670_) == 0)
{
goto v___jp_2636_;
}
else
{
lean_object* v_toSnapshot_2671_; lean_object* v_stx_2672_; lean_object* v_parserState_2673_; lean_object* v_elabSnap_2674_; lean_object* v_val_2675_; lean_object* v___x_2676_; 
v_toSnapshot_2671_ = lean_ctor_get(v_val_2669_, 0);
v_stx_2672_ = lean_ctor_get(v_val_2669_, 1);
v_parserState_2673_ = lean_ctor_get(v_val_2669_, 2);
v_elabSnap_2674_ = lean_ctor_get(v_val_2669_, 3);
v_val_2675_ = lean_ctor_get(v_nextCmdSnap_x3f_2670_, 0);
lean_inc(v_val_2675_);
v___x_2676_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2675_);
if (lean_obj_tag(v___x_2676_) == 1)
{
lean_object* v_val_2677_; lean_object* v_nextCmdSnap_x3f_2678_; 
v_val_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v_nextCmdSnap_x3f_2678_ = lean_ctor_get(v_val_2677_, 4);
lean_inc(v_nextCmdSnap_x3f_2678_);
lean_dec(v_val_2677_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2678_) == 0)
{
goto v___jp_2636_;
}
else
{
lean_object* v_val_2679_; lean_object* v___x_2680_; 
v_val_2679_ = lean_ctor_get(v_nextCmdSnap_x3f_2678_, 0);
lean_inc(v_val_2679_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2678_, 1);
v___x_2680_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2679_);
if (lean_obj_tag(v___x_2680_) == 1)
{
lean_object* v_val_2681_; lean_object* v_parserState_2682_; lean_object* v_pos_2683_; uint8_t v___x_2684_; 
v_val_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_val_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v_parserState_2682_ = lean_ctor_get(v_val_2681_, 2);
lean_inc_ref(v_parserState_2682_);
lean_dec(v_val_2681_);
v_pos_2683_ = lean_ctor_get(v_parserState_2682_, 0);
lean_inc(v_pos_2683_);
lean_dec_ref(v_parserState_2682_);
v___x_2684_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2683_, v_a_2437_);
lean_dec(v_pos_2683_);
if (v___x_2684_ == 0)
{
goto v___jp_2636_;
}
else
{
lean_inc(v_val_2675_);
lean_inc_ref(v_elabSnap_2674_);
lean_inc_ref_n(v_parserState_2673_, 2);
lean_inc(v_stx_2672_);
lean_inc_ref(v_toSnapshot_2671_);
lean_dec_ref_known(v_old_x3f_2430_, 1);
lean_dec_ref(v_parseCancelTk_2435_);
lean_dec_ref(v_cmdState_2432_);
lean_dec_ref(v_parserState_2431_);
v_toSnapshot_2440_ = v_toSnapshot_2671_;
v_stx_2441_ = v_stx_2672_;
v_parserState_2442_ = v_parserState_2673_;
v_elabSnap_2443_ = v_elabSnap_2674_;
v_val_2444_ = v_val_2675_;
v_newParserState_2445_ = v_parserState_2673_;
goto v___jp_2439_;
}
}
else
{
lean_dec(v___x_2680_);
goto v___jp_2636_;
}
}
}
else
{
lean_dec(v___x_2676_);
goto v___jp_2636_;
}
}
}
else
{
goto v___jp_2636_;
}
v___jp_2439_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_resultSnap_2448_; lean_object* v_task_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2472_; 
v___x_2446_ = lean_io_promise_new();
v___x_2447_ = l_IO_CancelToken_new();
v_resultSnap_2448_ = lean_ctor_get(v_elabSnap_2443_, 2);
lean_inc_ref(v_resultSnap_2448_);
v_task_2449_ = lean_ctor_get(v_resultSnap_2448_, 3);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_resultSnap_2448_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; lean_object* v_unused_2474_; lean_object* v_unused_2475_; 
v_unused_2473_ = lean_ctor_get(v_resultSnap_2448_, 2);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_resultSnap_2448_, 1);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_resultSnap_2448_, 0);
lean_dec(v_unused_2475_);
v___x_2451_ = v_resultSnap_2448_;
v_isShared_2452_ = v_isSharedCheck_2472_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_task_2449_);
lean_dec(v_resultSnap_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2472_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v_toProcessingContext_2458_; lean_object* v_pos_2459_; lean_object* v_endPos_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2453_ = lean_box(v_sync_2434_);
lean_inc_ref(v_a_2437_);
lean_inc_ref(v___x_2447_);
lean_inc(v___x_2446_);
lean_inc_ref(v_newParserState_2445_);
lean_inc(v_stx_2441_);
v___f_2454_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2454_, 0, v_val_2444_);
lean_closure_set(v___f_2454_, 1, v_cmds_2436_);
lean_closure_set(v___f_2454_, 2, v_stx_2441_);
lean_closure_set(v___f_2454_, 3, v_newParserState_2445_);
lean_closure_set(v___f_2454_, 4, v___x_2446_);
lean_closure_set(v___f_2454_, 5, v___x_2453_);
lean_closure_set(v___f_2454_, 6, v___x_2447_);
lean_closure_set(v___f_2454_, 7, v_a_2437_);
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = 1;
v___x_2457_ = l_BaseIO_chainTask___redArg(v_task_2449_, v___f_2454_, v___x_2455_, v___x_2456_);
v_toProcessingContext_2458_ = lean_ctor_get(v_a_2437_, 0);
v_pos_2459_ = lean_ctor_get(v_newParserState_2445_, 0);
lean_inc(v_pos_2459_);
lean_dec_ref(v_newParserState_2445_);
v_endPos_2460_ = lean_ctor_get(v_toProcessingContext_2458_, 3);
v___x_2461_ = lean_box(0);
lean_inc(v_endPos_2460_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_pos_2459_);
lean_ctor_set(v___x_2462_, 1, v_endPos_2460_);
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2447_);
v___x_2465_ = l_IO_Promise_result_x21___redArg(v___x_2446_);
lean_dec(v___x_2446_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 3, v___x_2465_);
lean_ctor_set(v___x_2451_, 2, v___x_2464_);
lean_ctor_set(v___x_2451_, 1, v___x_2463_);
lean_ctor_set(v___x_2451_, 0, v___x_2461_);
v___x_2467_ = v___x_2451_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2469_, 0, v_toSnapshot_2440_);
lean_ctor_set(v___x_2469_, 1, v_stx_2441_);
lean_ctor_set(v___x_2469_, 2, v_parserState_2442_);
lean_ctor_set(v___x_2469_, 3, v_elabSnap_2443_);
lean_ctor_set(v___x_2469_, 4, v___x_2468_);
v___x_2470_ = lean_io_promise_resolve(v___x_2469_, v_prom_2433_);
lean_dec(v_prom_2433_);
return v___x_2470_;
}
}
}
v___jp_2476_:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_box(0);
return v___x_2477_;
}
v___jp_2478_:
{
goto v___jp_2476_;
}
v___jp_2480_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2485_ = l_Lean_Name_str___override(v___y_2481_, v___x_2484_);
v___x_2486_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2487_ = l_Lean_Name_str___override(v___x_2485_, v___x_2486_);
v___x_2488_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2489_ = l_Lean_Name_str___override(v___x_2487_, v___x_2488_);
v___x_2490_ = l_Lean_Name_str___override(v___x_2489_, v___x_2486_);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = l_Lean_Name_num___override(v___x_2490_, v___x_2491_);
v___x_2493_ = l_Lean_Name_str___override(v___x_2492_, v___x_2486_);
v___x_2494_ = l_Lean_Name_str___override(v___x_2493_, v___x_2488_);
v___x_2495_ = l_Lean_Name_str___override(v___x_2494_, v___x_2486_);
v___x_2496_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2497_ = l_Lean_Name_str___override(v___x_2495_, v___x_2496_);
v___x_2498_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2499_ = l_Lean_Name_str___override(v___x_2497_, v___x_2498_);
v___x_2500_ = l_Lean_Name_toString(v___x_2499_, v___y_2482_);
v___x_2501_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2504_ = 0;
v___x_2505_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2505_, 0, v___x_2500_);
lean_ctor_set(v___x_2505_, 1, v___x_2501_);
lean_ctor_set(v___x_2505_, 2, v___x_2502_);
lean_ctor_set(v___x_2505_, 3, v___x_2503_);
lean_ctor_set_uint8(v___x_2505_, sizeof(void*)*4, v___x_2504_);
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2505_, 3);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2505_);
lean_ctor_set(v___x_2508_, 1, v_cmdState_2432_);
v___x_2509_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2502_, v___x_2508_);
v___x_2510_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2502_, v___x_2505_);
v___x_2511_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2505_);
lean_ctor_set(v___x_2512_, 1, v___x_2507_);
lean_ctor_set(v___x_2512_, 2, v___x_2509_);
lean_ctor_set(v___x_2512_, 3, v___x_2510_);
lean_ctor_set(v___x_2512_, 4, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2505_);
lean_ctor_set(v___x_2513_, 1, v___x_2506_);
lean_ctor_set(v___x_2513_, 2, v___y_2483_);
lean_ctor_set(v___x_2513_, 3, v___x_2512_);
lean_ctor_set(v___x_2513_, 4, v___x_2502_);
v___x_2514_ = lean_io_promise_resolve(v___x_2513_, v_prom_2433_);
lean_dec(v_prom_2433_);
v___x_2515_ = lean_box(0);
return v___x_2515_;
}
v___jp_2516_:
{
v___y_2481_ = v___y_2517_;
v___y_2482_ = v___y_2518_;
v___y_2483_ = v___y_2519_;
goto v___jp_2480_;
}
v___jp_2525_:
{
lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2542_);
v___x_2544_ = l_Lean_Parser_isTerminalCommand(v___y_2539_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_io_promise_new();
v___x_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
v___x_2547_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2543_, v___y_2535_, v_cmds_2436_, v___y_2530_, v___y_2541_, v___y_2526_, v_a_2437_, v___y_2537_, v___y_2536_, v___y_2528_, v___y_2531_, v___y_2532_, v___y_2527_, v___y_2533_, v___y_2534_, v_prom_2433_, v___x_2524_, v___f_2521_, v___f_2522_, v___f_2523_, v___y_2538_, v_cmdState_2432_, v___y_2540_, v___y_2529_, v_old_x3f_2430_, v_parseCancelTk_2435_, v___x_2546_);
lean_dec_ref(v___y_2540_);
lean_dec(v_prom_2433_);
lean_dec(v___y_2527_);
lean_dec(v___y_2535_);
v___y_2479_ = v___x_2547_;
goto v___jp_2478_;
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_box(0);
v___x_2549_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2543_, v___y_2535_, v_cmds_2436_, v___y_2530_, v___y_2541_, v___y_2526_, v_a_2437_, v___y_2537_, v___y_2536_, v___y_2528_, v___y_2531_, v___y_2532_, v___y_2527_, v___y_2533_, v___y_2534_, v_prom_2433_, v___x_2524_, v___f_2521_, v___f_2522_, v___f_2523_, v___y_2538_, v_cmdState_2432_, v___y_2540_, v___y_2529_, v_old_x3f_2430_, v_parseCancelTk_2435_, v___x_2548_);
lean_dec_ref(v___y_2540_);
lean_dec(v_prom_2433_);
lean_dec(v___y_2527_);
lean_dec(v___y_2535_);
v___y_2479_ = v___x_2549_;
goto v___jp_2478_;
}
}
v___jp_2550_:
{
lean_object* v___x_2567_; 
lean_inc(v___y_2564_);
v___x_2567_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_box(0);
v___y_2526_ = v___y_2551_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v_fst_2565_;
v___y_2532_ = v___y_2556_;
v___y_2533_ = v___y_2557_;
v___y_2534_ = v_snd_2566_;
v___y_2535_ = v___y_2558_;
v___y_2536_ = v___y_2559_;
v___y_2537_ = v___y_2560_;
v___y_2538_ = v___y_2561_;
v___y_2539_ = v___y_2564_;
v___y_2540_ = v___y_2562_;
v___y_2541_ = v___y_2563_;
v___y_2542_ = v___x_2568_;
goto v___jp_2525_;
}
else
{
lean_object* v_val_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2577_; 
v_val_2569_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2571_ = v___x_2567_;
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_val_2569_);
lean_dec(v___x_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
lean_inc(v_val_2569_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_val_2569_);
lean_ctor_set(v___x_2573_, 1, v_val_2569_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2573_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
v___y_2526_ = v___y_2551_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v_fst_2565_;
v___y_2532_ = v___y_2556_;
v___y_2533_ = v___y_2557_;
v___y_2534_ = v_snd_2566_;
v___y_2535_ = v___y_2558_;
v___y_2536_ = v___y_2559_;
v___y_2537_ = v___y_2560_;
v___y_2538_ = v___y_2561_;
v___y_2539_ = v___y_2564_;
v___y_2540_ = v___y_2562_;
v___y_2541_ = v___y_2563_;
v___y_2542_ = v___x_2575_;
goto v___jp_2525_;
}
}
}
}
v___jp_2578_:
{
if (v___y_2594_ == 0)
{
lean_inc(v___y_2592_);
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2580_;
v___y_2553_ = v___y_2581_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v___y_2586_;
v___y_2559_ = v___y_2587_;
v___y_2560_ = v___y_2588_;
v___y_2561_ = v___y_2589_;
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___y_2592_;
v_fst_2565_ = v___y_2592_;
v_snd_2566_ = v___y_2593_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v___y_2593_);
v___x_2595_ = lean_box(0);
v___x_2596_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2580_;
v___y_2553_ = v___y_2581_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v___y_2586_;
v___y_2559_ = v___y_2587_;
v___y_2560_ = v___y_2588_;
v___y_2561_ = v___y_2589_;
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___y_2592_;
v_fst_2565_ = v___x_2595_;
v_snd_2566_ = v___x_2596_;
goto v___jp_2550_;
}
}
v___jp_2597_:
{
uint8_t v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = l_IO_CancelToken_isSet(v_parseCancelTk_2435_);
v___x_2609_ = 1;
if (v___x_2608_ == 0)
{
lean_dec(v___y_2604_);
if (v_sync_2434_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2610_ = lean_io_promise_new();
v___x_2611_ = lean_io_promise_new();
v___x_2612_ = lean_io_promise_new();
v___x_2613_ = lean_io_promise_new();
v___x_2614_ = l_Lean_internal_cmdlineSnapshots;
v___x_2615_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2606_, v___x_2614_);
lean_dec_ref(v___y_2606_);
if (v___x_2615_ == 0)
{
v___y_2579_ = v___x_2608_;
v___y_2580_ = v___x_2611_;
v___y_2581_ = v___x_2609_;
v___y_2582_ = v___x_2614_;
v___y_2583_ = v___y_2601_;
v___y_2584_ = v___x_2610_;
v___y_2585_ = v___x_2612_;
v___y_2586_ = v___x_2613_;
v___y_2587_ = v___y_2598_;
v___y_2588_ = v___y_2599_;
v___y_2589_ = v___y_2600_;
v___y_2590_ = v___y_2602_;
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2605_;
v___y_2593_ = v___y_2607_;
v___y_2594_ = v___x_2615_;
goto v___jp_2578_;
}
else
{
uint8_t v___x_2616_; 
lean_inc(v___y_2605_);
v___x_2616_ = l_Lean_Parser_isTerminalCommand(v___y_2605_);
if (v___x_2616_ == 0)
{
v___y_2579_ = v___x_2608_;
v___y_2580_ = v___x_2611_;
v___y_2581_ = v___x_2609_;
v___y_2582_ = v___x_2614_;
v___y_2583_ = v___y_2601_;
v___y_2584_ = v___x_2610_;
v___y_2585_ = v___x_2612_;
v___y_2586_ = v___x_2613_;
v___y_2587_ = v___y_2598_;
v___y_2588_ = v___y_2599_;
v___y_2589_ = v___y_2600_;
v___y_2590_ = v___y_2602_;
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2605_;
v___y_2593_ = v___y_2607_;
v___y_2594_ = v___x_2615_;
goto v___jp_2578_;
}
else
{
lean_inc(v___y_2605_);
v___y_2551_ = v___x_2608_;
v___y_2552_ = v___x_2611_;
v___y_2553_ = v___x_2609_;
v___y_2554_ = v___x_2614_;
v___y_2555_ = v___y_2601_;
v___y_2556_ = v___x_2610_;
v___y_2557_ = v___x_2612_;
v___y_2558_ = v___x_2613_;
v___y_2559_ = v___y_2598_;
v___y_2560_ = v___y_2599_;
v___y_2561_ = v___y_2600_;
v___y_2562_ = v___y_2602_;
v___y_2563_ = v___y_2603_;
v___y_2564_ = v___y_2605_;
v_fst_2565_ = v___y_2605_;
v_snd_2566_ = v___y_2607_;
goto v___jp_2550_;
}
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
v___x_2617_ = lean_box(v___x_2608_);
v___x_2618_ = lean_box(v___x_2609_);
lean_inc_ref(v_a_2437_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 19, 18);
lean_closure_set(v___f_2619_, 0, v_cmds_2436_);
lean_closure_set(v___f_2619_, 1, v___y_2601_);
lean_closure_set(v___f_2619_, 2, v___y_2603_);
lean_closure_set(v___f_2619_, 3, v___x_2617_);
lean_closure_set(v___f_2619_, 4, v_a_2437_);
lean_closure_set(v___f_2619_, 5, v___y_2599_);
lean_closure_set(v___f_2619_, 6, v___y_2598_);
lean_closure_set(v___f_2619_, 7, v___x_2618_);
lean_closure_set(v___f_2619_, 8, v_prom_2433_);
lean_closure_set(v___f_2619_, 9, v___x_2524_);
lean_closure_set(v___f_2619_, 10, v___f_2521_);
lean_closure_set(v___f_2619_, 11, v___f_2522_);
lean_closure_set(v___f_2619_, 12, v___f_2523_);
lean_closure_set(v___f_2619_, 13, v___y_2600_);
lean_closure_set(v___f_2619_, 14, v_cmdState_2432_);
lean_closure_set(v___f_2619_, 15, v___y_2602_);
lean_closure_set(v___f_2619_, 16, v_old_x3f_2430_);
lean_closure_set(v___f_2619_, 17, v_parseCancelTk_2435_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_io_as_task(v___f_2619_, v___x_2620_);
lean_dec_ref(v___x_2621_);
goto v___jp_2476_;
}
}
else
{
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v_cmds_2436_);
lean_dec_ref(v_parseCancelTk_2435_);
if (lean_obj_tag(v_old_x3f_2430_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; lean_object* v_children_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v_val_2622_ = lean_ctor_get(v_old_x3f_2430_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v_old_x3f_2430_, 1);
v___x_2623_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2622_);
v_children_2624_ = lean_ctor_get(v___x_2623_, 1);
lean_inc_ref(v_children_2624_);
lean_dec_ref(v___x_2623_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_array_get_size(v_children_2624_);
v___x_2627_ = lean_nat_dec_lt(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_dec_ref(v_children_2624_);
v___y_2481_ = v___y_2604_;
v___y_2482_ = v___x_2609_;
v___y_2483_ = v___y_2607_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_nat_dec_le(v___x_2626_, v___x_2626_);
if (v___x_2629_ == 0)
{
if (v___x_2627_ == 0)
{
lean_dec_ref(v_children_2624_);
v___y_2481_ = v___y_2604_;
v___y_2482_ = v___x_2609_;
v___y_2483_ = v___y_2607_;
goto v___jp_2480_;
}
else
{
size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = lean_usize_of_nat(v___x_2626_);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2624_, v___x_2630_, v___x_2631_, v___x_2628_);
lean_dec_ref(v_children_2624_);
v___y_2517_ = v___y_2604_;
v___y_2518_ = v___x_2609_;
v___y_2519_ = v___y_2607_;
v___y_2520_ = v___x_2632_;
goto v___jp_2516_;
}
}
else
{
size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = lean_usize_of_nat(v___x_2626_);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2624_, v___x_2633_, v___x_2634_, v___x_2628_);
lean_dec_ref(v_children_2624_);
v___y_2517_ = v___y_2604_;
v___y_2518_ = v___x_2609_;
v___y_2519_ = v___y_2607_;
v___y_2520_ = v___x_2635_;
goto v___jp_2516_;
}
}
}
else
{
lean_dec(v_old_x3f_2430_);
v___y_2481_ = v___y_2604_;
v___y_2482_ = v___x_2609_;
v___y_2483_ = v___y_2607_;
goto v___jp_2480_;
}
}
}
v___jp_2636_:
{
lean_object* v_env_2637_; lean_object* v_scopes_2638_; lean_object* v___x_2639_; lean_object* v_opts_2640_; lean_object* v_currNamespace_2641_; lean_object* v_openDecls_2642_; lean_object* v___x_2643_; lean_object* v___f_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_snd_2648_; 
v_env_2637_ = lean_ctor_get(v_cmdState_2432_, 0);
v_scopes_2638_ = lean_ctor_get(v_cmdState_2432_, 2);
v___x_2639_ = l_List_head_x21___redArg(v___x_2524_, v_scopes_2638_);
v_opts_2640_ = lean_ctor_get(v___x_2639_, 1);
lean_inc_ref_n(v_opts_2640_, 2);
v_currNamespace_2641_ = lean_ctor_get(v___x_2639_, 2);
lean_inc(v_currNamespace_2641_);
v_openDecls_2642_ = lean_ctor_get(v___x_2639_, 3);
lean_inc(v_openDecls_2642_);
lean_dec(v___x_2639_);
lean_inc_ref(v_env_2637_);
v___x_2643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2643_, 0, v_env_2637_);
lean_ctor_set(v___x_2643_, 1, v_opts_2640_);
lean_ctor_set(v___x_2643_, 2, v_currNamespace_2641_);
lean_ctor_set(v___x_2643_, 3, v_openDecls_2642_);
lean_inc_ref(v_parserState_2431_);
lean_inc_ref(v_a_2437_);
v___f_2644_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2644_, 0, v_a_2437_);
lean_closure_set(v___f_2644_, 1, v___x_2643_);
lean_closure_set(v___f_2644_, 2, v_parserState_2431_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2646_ = lean_box(0);
v___x_2647_ = lean_profileit(v___x_2645_, v_opts_2640_, v___f_2644_, v___x_2646_);
v_snd_2648_ = lean_ctor_get(v___x_2647_, 1);
lean_inc(v_snd_2648_);
if (lean_obj_tag(v_old_x3f_2430_) == 1)
{
lean_object* v_val_2649_; lean_object* v_fst_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v_pos_2653_; lean_object* v_toSnapshot_2654_; lean_object* v_stx_2655_; lean_object* v_parserState_2656_; lean_object* v_elabSnap_2657_; lean_object* v_nextCmdSnap_x3f_2658_; uint8_t v___x_2659_; 
v_val_2649_ = lean_ctor_get(v_old_x3f_2430_, 0);
v_fst_2650_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_n(v_fst_2650_, 2);
lean_dec(v___x_2647_);
v_fst_2651_ = lean_ctor_get(v_snd_2648_, 0);
lean_inc(v_fst_2651_);
v_snd_2652_ = lean_ctor_get(v_snd_2648_, 1);
lean_inc(v_snd_2652_);
lean_dec(v_snd_2648_);
v_pos_2653_ = lean_ctor_get(v_parserState_2431_, 0);
lean_inc(v_pos_2653_);
lean_dec_ref(v_parserState_2431_);
v_toSnapshot_2654_ = lean_ctor_get(v_val_2649_, 0);
v_stx_2655_ = lean_ctor_get(v_val_2649_, 1);
v_parserState_2656_ = lean_ctor_get(v_val_2649_, 2);
v_elabSnap_2657_ = lean_ctor_get(v_val_2649_, 3);
v_nextCmdSnap_x3f_2658_ = lean_ctor_get(v_val_2649_, 4);
lean_inc(v_stx_2655_);
v___x_2659_ = l_Lean_Syntax_eqWithInfo(v_fst_2650_, v_stx_2655_);
if (v___x_2659_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2658_) == 0)
{
lean_inc(v_fst_2651_);
lean_inc_ref(v_opts_2640_);
lean_inc(v_fst_2650_);
v___y_2598_ = v___x_2646_;
v___y_2599_ = v_snd_2652_;
v___y_2600_ = v_pos_2653_;
v___y_2601_ = v_fst_2650_;
v___y_2602_ = v_opts_2640_;
v___y_2603_ = v_fst_2651_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v_fst_2650_;
v___y_2606_ = v_opts_2640_;
v___y_2607_ = v_fst_2651_;
goto v___jp_2597_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_val_2660_ = lean_ctor_get(v_nextCmdSnap_x3f_2658_, 0);
v___x_2661_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2660_);
v___x_2662_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2661_, v_val_2660_);
lean_inc(v_fst_2651_);
lean_inc_ref(v_opts_2640_);
lean_inc(v_fst_2650_);
v___y_2598_ = v___x_2646_;
v___y_2599_ = v_snd_2652_;
v___y_2600_ = v_pos_2653_;
v___y_2601_ = v_fst_2650_;
v___y_2602_ = v_opts_2640_;
v___y_2603_ = v_fst_2651_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v_fst_2650_;
v___y_2606_ = v_opts_2640_;
v___y_2607_ = v_fst_2651_;
goto v___jp_2597_;
}
}
else
{
lean_inc(v_val_2649_);
lean_dec(v_pos_2653_);
lean_dec(v_snd_2652_);
lean_dec(v_fst_2650_);
lean_dec_ref_known(v_old_x3f_2430_, 1);
lean_dec_ref(v_opts_2640_);
lean_dec_ref(v_parseCancelTk_2435_);
lean_dec_ref(v_cmdState_2432_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2658_) == 1)
{
lean_object* v_val_2663_; 
lean_inc_ref(v_nextCmdSnap_x3f_2658_);
lean_inc_ref(v_elabSnap_2657_);
lean_inc_ref(v_parserState_2656_);
lean_inc(v_stx_2655_);
lean_inc_ref(v_toSnapshot_2654_);
lean_dec(v_val_2649_);
v_val_2663_ = lean_ctor_get(v_nextCmdSnap_x3f_2658_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2658_, 1);
v_toSnapshot_2440_ = v_toSnapshot_2654_;
v_stx_2441_ = v_stx_2655_;
v_parserState_2442_ = v_parserState_2656_;
v_elabSnap_2443_ = v_elabSnap_2657_;
v_val_2444_ = v_val_2663_;
v_newParserState_2445_ = v_fst_2651_;
goto v___jp_2439_;
}
else
{
lean_object* v___x_2664_; 
lean_dec(v_fst_2651_);
lean_dec_ref(v_cmds_2436_);
v___x_2664_ = lean_io_promise_resolve(v_val_2649_, v_prom_2433_);
lean_dec(v_prom_2433_);
return v___x_2664_;
}
}
}
else
{
lean_object* v_fst_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v_pos_2668_; 
v_fst_2665_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_n(v_fst_2665_, 2);
lean_dec(v___x_2647_);
v_fst_2666_ = lean_ctor_get(v_snd_2648_, 0);
lean_inc_n(v_fst_2666_, 2);
v_snd_2667_ = lean_ctor_get(v_snd_2648_, 1);
lean_inc(v_snd_2667_);
lean_dec(v_snd_2648_);
v_pos_2668_ = lean_ctor_get(v_parserState_2431_, 0);
lean_inc(v_pos_2668_);
lean_dec_ref(v_parserState_2431_);
lean_inc_ref(v_opts_2640_);
v___y_2598_ = v___x_2646_;
v___y_2599_ = v_snd_2667_;
v___y_2600_ = v_pos_2668_;
v___y_2601_ = v_fst_2665_;
v___y_2602_ = v_opts_2640_;
v___y_2603_ = v_fst_2666_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v_fst_2665_;
v___y_2606_ = v_opts_2640_;
v___y_2607_ = v_fst_2666_;
goto v___jp_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2685_, lean_object* v_cmds_2686_, lean_object* v_stx_2687_, lean_object* v_newParserState_2688_, lean_object* v_val_2689_, uint8_t v_sync_2690_, lean_object* v_val_2691_, lean_object* v_a_2692_, lean_object* v_oldNext_2693_){
_start:
{
lean_object* v_cmdState_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_cmdState_2695_ = lean_ctor_get(v_oldResult_2685_, 1);
lean_inc_ref(v_cmdState_2695_);
lean_dec_ref(v_oldResult_2685_);
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_oldNext_2693_);
v___x_2697_ = lean_array_push(v_cmds_2686_, v_stx_2687_);
v___x_2698_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2696_, v_newParserState_2688_, v_cmdState_2695_, v_val_2689_, v_sync_2690_, v_val_2691_, v___x_2697_, v_a_2692_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2699_ = _args[0];
lean_object* v_val_2700_ = _args[1];
lean_object* v_cmds_2701_ = _args[2];
lean_object* v_fst_2702_ = _args[3];
lean_object* v_fst_2703_ = _args[4];
lean_object* v_val_2704_ = _args[5];
lean_object* v_a_2705_ = _args[6];
lean_object* v_snd_2706_ = _args[7];
lean_object* v___x_2707_ = _args[8];
lean_object* v___x_2708_ = _args[9];
lean_object* v_fst_2709_ = _args[10];
lean_object* v_val_2710_ = _args[11];
lean_object* v_val_2711_ = _args[12];
lean_object* v_val_2712_ = _args[13];
lean_object* v_snd_2713_ = _args[14];
lean_object* v_prom_2714_ = _args[15];
lean_object* v___x_2715_ = _args[16];
lean_object* v___f_2716_ = _args[17];
lean_object* v___f_2717_ = _args[18];
lean_object* v___f_2718_ = _args[19];
lean_object* v_pos_2719_ = _args[20];
lean_object* v_cmdState_2720_ = _args[21];
lean_object* v_opts_2721_ = _args[22];
lean_object* v___x_2722_ = _args[23];
lean_object* v_old_x3f_2723_ = _args[24];
lean_object* v_parseCancelTk_2724_ = _args[25];
lean_object* v_next_x3f_2725_ = _args[26];
lean_object* v___y_2726_ = _args[27];
_start:
{
uint8_t v_val_45334__boxed_2727_; uint8_t v___x_45337__boxed_2728_; lean_object* v_res_2729_; 
v_val_45334__boxed_2727_ = lean_unbox(v_val_2704_);
v___x_45337__boxed_2728_ = lean_unbox(v___x_2708_);
v_res_2729_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2699_, v_val_2700_, v_cmds_2701_, v_fst_2702_, v_fst_2703_, v_val_45334__boxed_2727_, v_a_2705_, v_snd_2706_, v___x_2707_, v___x_45337__boxed_2728_, v_fst_2709_, v_val_2710_, v_val_2711_, v_val_2712_, v_snd_2713_, v_prom_2714_, v___x_2715_, v___f_2716_, v___f_2717_, v___f_2718_, v_pos_2719_, v_cmdState_2720_, v_opts_2721_, v___x_2722_, v_old_x3f_2723_, v_parseCancelTk_2724_, v_next_x3f_2725_);
lean_dec_ref(v___x_2722_);
lean_dec_ref(v_opts_2721_);
lean_dec(v_prom_2714_);
lean_dec(v_val_2711_);
lean_dec_ref(v_a_2705_);
lean_dec(v_val_2700_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2730_, lean_object* v_parserState_2731_, lean_object* v_cmdState_2732_, lean_object* v_prom_2733_, lean_object* v_sync_2734_, lean_object* v_parseCancelTk_2735_, lean_object* v_cmds_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
uint8_t v_sync_boxed_2739_; lean_object* v_res_2740_; 
v_sync_boxed_2739_ = lean_unbox(v_sync_2734_);
v_res_2740_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2730_, v_parserState_2731_, v_cmdState_2732_, v_prom_2733_, v_sync_boxed_2739_, v_parseCancelTk_2735_, v_cmds_2736_, v_a_2737_);
lean_dec_ref(v_a_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2741_, size_t v_i_2742_, size_t v_stop_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2741_, v_i_2742_, v_stop_2743_, v_b_2744_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2748_, lean_object* v_i_2749_, lean_object* v_stop_2750_, lean_object* v_b_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
size_t v_i_boxed_2754_; size_t v_stop_boxed_2755_; lean_object* v_res_2756_; 
v_i_boxed_2754_ = lean_unbox_usize(v_i_2749_);
lean_dec(v_i_2749_);
v_stop_boxed_2755_ = lean_unbox_usize(v_stop_2750_);
lean_dec(v_stop_2750_);
v_res_2756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2748_, v_i_boxed_2754_, v_stop_boxed_2755_, v_b_2751_, v___y_2752_);
lean_dec_ref(v___y_2752_);
lean_dec_ref(v_as_2748_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2757_, lean_object* v_opt_2758_){
_start:
{
lean_object* v_name_2759_; lean_object* v_map_2760_; lean_object* v___x_2761_; 
v_name_2759_ = lean_ctor_get(v_opt_2758_, 0);
v_map_2760_ = lean_ctor_get(v_opts_2757_, 0);
v___x_2761_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2760_, v_name_2759_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_box(0);
return v___x_2762_;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2772_; 
v_val_2763_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2765_ = v___x_2761_;
v_isShared_2766_ = v_isSharedCheck_2772_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_val_2763_);
lean_dec(v___x_2761_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2772_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
if (lean_obj_tag(v_val_2763_) == 0)
{
lean_object* v_v_2767_; lean_object* v___x_2769_; 
v_v_2767_ = lean_ctor_get(v_val_2763_, 0);
lean_inc_ref(v_v_2767_);
lean_dec_ref_known(v_val_2763_, 1);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v_v_2767_);
v___x_2769_ = v___x_2765_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_v_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
else
{
lean_object* v___x_2771_; 
lean_del_object(v___x_2765_);
lean_dec(v_val_2763_);
v___x_2771_ = lean_box(0);
return v___x_2771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2773_, lean_object* v_opt_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2773_, v_opt_2774_);
lean_dec_ref(v_opt_2774_);
lean_dec_ref(v_opts_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2776_, lean_object* v_x_2777_){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2776_);
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2780_, 0, v_x_2777_);
lean_ctor_set(v___x_2780_, 1, v___x_2778_);
lean_ctor_set(v___x_2780_, 2, v___x_2779_);
return v___x_2780_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2787_ = l_Lean_Array_toPArray_x27___redArg(v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
if (lean_obj_tag(v_a_2788_) == 0)
{
lean_object* v___x_2790_; 
v___x_2790_ = l_List_reverse___redArg(v_a_2789_);
return v___x_2790_;
}
else
{
lean_object* v_head_2791_; lean_object* v_tail_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2805_; 
v_head_2791_ = lean_ctor_get(v_a_2788_, 0);
v_tail_2792_ = lean_ctor_get(v_a_2788_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_a_2788_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2794_ = v_a_2788_;
v_isShared_2795_ = v_isSharedCheck_2805_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_tail_2792_);
lean_inc(v_head_2791_);
lean_dec(v_a_2788_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2805_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2796_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v_head_2791_);
v___x_2798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
v___x_2799_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v_a_2789_);
lean_ctor_set(v___x_2794_, 0, v___x_2800_);
v___x_2802_ = v___x_2794_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_a_2789_);
v___x_2802_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
v_a_2788_ = v_tail_2792_;
v_a_2789_ = v___x_2802_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
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
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2825_ = l_Lean_MessageData_ofFormat(v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2826_, lean_object* v_stx_2827_, lean_object* v_origStx_2828_, lean_object* v_toProcessingContext_2829_, lean_object* v___x_2830_, lean_object* v_fileMap_2831_, lean_object* v_parserState_2832_, lean_object* v_a_2833_, lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_toProcessingContext_2838_; lean_object* v___x_2839_; 
v_toProcessingContext_2838_ = lean_ctor_get(v___y_2836_, 0);
lean_inc_ref(v_toProcessingContext_2838_);
lean_inc(v_stx_2827_);
v___x_2839_ = lean_apply_3(v_setupImports_2826_, v_stx_2827_, v_toProcessingContext_2838_, lean_box(0));
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_3053_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_3053_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_3053_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
if (lean_obj_tag(v_a_2840_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; 
lean_dec_ref(v___x_2835_);
lean_dec(v___x_2834_);
lean_dec_ref(v_parserState_2832_);
lean_dec_ref(v_fileMap_2831_);
lean_dec(v___x_2830_);
lean_dec_ref(v_toProcessingContext_2829_);
lean_dec(v_origStx_2828_);
lean_dec(v_stx_2827_);
v_a_2844_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v_a_2840_, 1);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_a_2844_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_3052_; 
v_a_2848_ = lean_ctor_get(v_a_2840_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_2850_ = v_a_2840_;
v_isShared_2851_ = v_isSharedCheck_3052_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v_a_2840_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_3052_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v_mainModuleName_2853_; lean_object* v_package_x3f_2854_; uint8_t v_isModule_2855_; lean_object* v_imports_2856_; lean_object* v_opts_2857_; uint32_t v_trustLevel_2858_; lean_object* v_importArts_2859_; lean_object* v_plugins_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2865_; 
v___x_2852_ = lean_io_mono_nanos_now();
v_mainModuleName_2853_ = lean_ctor_get(v_a_2848_, 0);
lean_inc(v_mainModuleName_2853_);
v_package_x3f_2854_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_package_x3f_2854_);
v_isModule_2855_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*6 + 4);
v_imports_2856_ = lean_ctor_get(v_a_2848_, 2);
lean_inc_ref(v_imports_2856_);
v_opts_2857_ = lean_ctor_get(v_a_2848_, 3);
lean_inc_ref(v_opts_2857_);
v_trustLevel_2858_ = lean_ctor_get_uint32(v_a_2848_, sizeof(void*)*6);
v_importArts_2859_ = lean_ctor_get(v_a_2848_, 4);
lean_inc(v_importArts_2859_);
v_plugins_2860_ = lean_ctor_get(v_a_2848_, 5);
lean_inc_ref(v_plugins_2860_);
lean_dec(v_a_2848_);
v___x_2861_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2827_);
v___x_2862_ = l_Lean_MessageLog_empty;
v___x_2863_ = 1;
lean_inc(v_stx_2827_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v_stx_2827_);
v___x_2865_ = v___x_2850_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_stx_2827_);
v___x_2865_ = v_reuseFailAlloc_3051_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_origStx_2828_);
lean_inc_ref(v___x_2865_);
lean_inc_ref(v_opts_2857_);
v___x_2867_ = l_Lean_Elab_processHeaderCore(v___x_2861_, v_imports_2856_, v_isModule_2855_, v_opts_2857_, v___x_2862_, v_toProcessingContext_2829_, v_trustLevel_2858_, v_plugins_2860_, v___x_2863_, v_mainModuleName_2853_, v_package_x3f_2854_, v_importArts_2859_, v___x_2865_, v___x_2866_);
lean_dec(v___x_2861_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_3042_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_3042_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_3042_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_3041_; 
v_fst_2872_ = lean_ctor_get(v_a_2868_, 0);
v_snd_2873_ = lean_ctor_get(v_a_2868_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_2875_ = v_a_2868_;
v_isShared_2876_ = v_isSharedCheck_3041_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_snd_2873_);
lean_inc(v_fst_2872_);
lean_dec(v_a_2868_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_3041_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v_traceState_2895_; 
v___x_2877_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2873_);
v___x_2878_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2873_);
v___x_2879_ = l_Lean_MessageLog_hasErrors(v_snd_2873_);
if (v___x_2879_ == 0)
{
double v___x_2989_; double v___x_2990_; double v___x_2991_; double v___x_2992_; double v___x_2993_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_del_object(v___x_2842_);
lean_dec_ref(v___x_2835_);
v___x_2989_ = lean_float_of_nat(v___x_2852_);
v___x_2990_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2991_ = lean_float_div(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_float_of_nat(v___x_2877_);
v___x_2993_ = lean_float_div(v___x_2992_, v___x_2990_);
v___x_3010_ = l_Lean_trace_profiler_output;
v___x_3011_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2857_, v___x_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = l_Lean_trace_profiler_serve;
v___x_3013_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2857_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2895_ = v___x_3014_;
goto v___jp_2894_;
}
else
{
goto v___jp_2994_;
}
}
else
{
lean_dec_ref_known(v___x_3011_, 1);
goto v___jp_2994_;
}
v___jp_2994_:
{
uint64_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_2995_ = 0ULL;
v___x_2996_ = lean_box(0);
v___x_2997_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2998_ = lean_box(0);
v___x_2999_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_3000_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3000_, 0, v___x_2997_);
lean_ctor_set(v___x_3000_, 1, v___x_2998_);
lean_ctor_set(v___x_3000_, 2, v___x_2999_);
lean_ctor_set_float(v___x_3000_, sizeof(void*)*3, v___x_2991_);
lean_ctor_set_float(v___x_3000_, sizeof(void*)*3 + 8, v___x_2993_);
lean_ctor_set_uint8(v___x_3000_, sizeof(void*)*3 + 16, v___x_2863_);
v___x_3001_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3002_ = lean_mk_empty_array_with_capacity(v___x_2830_);
v___x_3003_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3000_);
lean_ctor_set(v___x_3003_, 1, v___x_3001_);
lean_ctor_set(v___x_3003_, 2, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_2996_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_mk_empty_array_with_capacity(v___x_3005_);
v___x_3007_ = lean_array_push(v___x_3006_, v___x_3004_);
v___x_3008_ = l_Lean_Array_toPArray_x27___redArg(v___x_3007_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set_uint64(v___x_3009_, sizeof(void*)*1, v___x_2995_);
v_traceState_2895_ = v___x_3009_;
goto v___jp_2894_;
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint64_t v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; size_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v___x_2877_);
lean_del_object(v___x_2875_);
lean_dec(v_snd_2873_);
lean_dec(v_fst_2872_);
lean_del_object(v___x_2870_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v_opts_2857_);
lean_dec(v___x_2852_);
lean_dec(v___x_2834_);
lean_dec_ref(v_parserState_2832_);
lean_dec_ref(v_fileMap_2831_);
lean_dec(v_stx_2827_);
v___x_3015_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3016_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3017_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2830_, 2);
v___x_3018_ = l_Lean_Name_num___override(v___x_3017_, v___x_2830_);
v___x_3019_ = l_Lean_Name_str___override(v___x_3018_, v___x_3015_);
v___x_3020_ = l_Lean_Name_str___override(v___x_3019_, v___x_3016_);
v___x_3021_ = l_Lean_Name_str___override(v___x_3020_, v___x_3015_);
v___x_3022_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3023_ = l_Lean_Name_str___override(v___x_3021_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3025_ = l_Lean_Name_str___override(v___x_3023_, v___x_3024_);
v___x_3026_ = l_Lean_Name_toString(v___x_3025_, v___x_2863_);
v___x_3027_ = lean_box(0);
v___x_3028_ = 0ULL;
v___x_3029_ = lean_unsigned_to_nat(32u);
v___x_3030_ = lean_mk_empty_array_with_capacity(v___x_3029_);
v___x_3031_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3032_ = ((size_t)5ULL);
v___x_3033_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set(v___x_3033_, 1, v___x_3030_);
lean_ctor_set(v___x_3033_, 2, v___x_2830_);
lean_ctor_set(v___x_3033_, 3, v___x_2830_);
lean_ctor_set_usize(v___x_3033_, 4, v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set_uint64(v___x_3034_, sizeof(void*)*1, v___x_3028_);
v___x_3035_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3035_, 0, v___x_3026_);
lean_ctor_set(v___x_3035_, 1, v___x_2878_);
lean_ctor_set(v___x_3035_, 2, v___x_3027_);
lean_ctor_set(v___x_3035_, 3, v___x_3034_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*4, v___x_2879_);
v___x_3036_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2835_);
v___x_3037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
lean_ctor_set(v___x_3037_, 2, v___x_3027_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_3037_);
v___x_3039_ = v___x_2842_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
v___jp_2880_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___y_2886_);
v___x_2888_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2888_, 0, v___y_2883_);
lean_ctor_set(v___x_2888_, 1, v___x_2878_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
lean_ctor_set(v___x_2888_, 3, v___y_2884_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*4, v___x_2879_);
v___x_2889_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2881_, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___y_2882_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_ctor_set(v___x_2890_, 2, v___y_2885_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2890_);
v___x_2892_ = v___x_2870_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
v___jp_2894_:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Language_Lean_reparseOptions(v_opts_2857_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_env_2903_; lean_object* v_messages_2904_; lean_object* v_scopes_2905_; lean_object* v_usedQuotCtxts_2906_; lean_object* v_nextMacroScope_2907_; lean_object* v_maxRecDepth_2908_; lean_object* v_ngen_2909_; lean_object* v_auxDeclNGen_2910_; lean_object* v_snapshotTasks_2911_; lean_object* v_prevLinterStates_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2978_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2830_, 4);
v___x_2899_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2830_);
lean_ctor_set(v___x_2899_, 1, v___x_2830_);
lean_ctor_set(v___x_2899_, 2, v___x_2830_);
lean_ctor_set(v___x_2899_, 3, v___x_2830_);
lean_ctor_set(v___x_2899_, 4, v___x_2898_);
lean_ctor_set(v___x_2899_, 5, v___x_2898_);
lean_ctor_set(v___x_2899_, 6, v___x_2898_);
lean_ctor_set(v___x_2899_, 7, v___x_2898_);
lean_ctor_set(v___x_2899_, 8, v___x_2898_);
lean_ctor_set(v___x_2899_, 9, v___x_2898_);
v___x_2900_ = lean_io_promise_new();
v___x_2901_ = l_IO_CancelToken_new();
lean_inc(v_fst_2872_);
v___x_2902_ = l_Lean_Elab_Command_mkState(v_fst_2872_, v_snd_2873_, v_a_2897_);
v_env_2903_ = lean_ctor_get(v___x_2902_, 0);
v_messages_2904_ = lean_ctor_get(v___x_2902_, 1);
v_scopes_2905_ = lean_ctor_get(v___x_2902_, 2);
v_usedQuotCtxts_2906_ = lean_ctor_get(v___x_2902_, 3);
v_nextMacroScope_2907_ = lean_ctor_get(v___x_2902_, 4);
v_maxRecDepth_2908_ = lean_ctor_get(v___x_2902_, 5);
v_ngen_2909_ = lean_ctor_get(v___x_2902_, 6);
v_auxDeclNGen_2910_ = lean_ctor_get(v___x_2902_, 7);
v_snapshotTasks_2911_ = lean_ctor_get(v___x_2902_, 10);
v_prevLinterStates_2912_ = lean_ctor_get(v___x_2902_, 11);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; lean_object* v_unused_2980_; 
v_unused_2979_ = lean_ctor_get(v___x_2902_, 9);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v___x_2902_, 8);
lean_dec(v_unused_2980_);
v___x_2914_ = v___x_2902_;
v_isShared_2915_ = v_isSharedCheck_2978_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_prevLinterStates_2912_);
lean_inc(v_snapshotTasks_2911_);
lean_inc(v_auxDeclNGen_2910_);
lean_inc(v_ngen_2909_);
lean_inc(v_maxRecDepth_2908_);
lean_inc(v_nextMacroScope_2907_);
lean_inc(v_usedQuotCtxts_2906_);
lean_inc(v_scopes_2905_);
lean_inc(v_messages_2904_);
lean_inc(v_env_2903_);
lean_dec(v___x_2902_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2978_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2916_ = lean_box(0);
v___x_2917_ = l_Lean_Options_empty;
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2922_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2922_, 0, v_fst_2872_);
lean_ctor_set(v___x_2922_, 1, v___x_2916_);
lean_ctor_set(v___x_2922_, 2, v_fileMap_2831_);
lean_ctor_set(v___x_2922_, 3, v___x_2899_);
lean_ctor_set(v___x_2922_, 4, v___x_2917_);
lean_ctor_set(v___x_2922_, 5, v___x_2918_);
lean_ctor_set(v___x_2922_, 6, v___x_2919_);
lean_ctor_set(v___x_2922_, 7, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
v___x_2924_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2827_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v_stx_2827_);
lean_ctor_set(v___x_2875_, 0, v___x_2924_);
v___x_2926_ = v___x_2875_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_stx_2827_);
v___x_2926_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
v___x_2928_ = lean_unsigned_to_nat(2u);
v___x_2929_ = l_Lean_Syntax_getArg(v_stx_2827_, v___x_2928_);
lean_dec(v_stx_2827_);
v___x_2930_ = l_Lean_Syntax_getArgs(v___x_2929_);
lean_dec(v___x_2929_);
v___x_2931_ = lean_array_to_list(v___x_2930_);
v___x_2932_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2931_, v___x_2919_);
v___x_2933_ = l_Lean_List_toPArray_x27___redArg(v___x_2932_);
v___x_2934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2927_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2923_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = lean_mk_empty_array_with_capacity(v___x_2920_);
v___x_2937_ = lean_array_push(v___x_2936_, v___x_2935_);
v___x_2938_ = l_Lean_Array_toPArray_x27___redArg(v___x_2937_);
lean_dec_ref(v___x_2937_);
lean_inc_ref(v___x_2938_);
v___x_2939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2939_, 0, v___x_2898_);
lean_ctor_set(v___x_2939_, 1, v___x_2898_);
lean_ctor_set(v___x_2939_, 2, v___x_2938_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3, v___x_2863_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 9, v_traceState_2895_);
lean_ctor_set(v___x_2914_, 8, v___x_2939_);
v___x_2941_ = v___x_2914_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_env_2903_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_messages_2904_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_scopes_2905_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_usedQuotCtxts_2906_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_nextMacroScope_2907_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v_maxRecDepth_2908_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v_ngen_2909_);
lean_ctor_set(v_reuseFailAlloc_2976_, 7, v_auxDeclNGen_2910_);
lean_ctor_set(v_reuseFailAlloc_2976_, 8, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2976_, 9, v_traceState_2895_);
lean_ctor_set(v_reuseFailAlloc_2976_, 10, v_snapshotTasks_2911_);
lean_ctor_set(v_reuseFailAlloc_2976_, 11, v_prevLinterStates_2912_);
v___x_2941_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; lean_object* v_size_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint64_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2830_);
lean_inc_ref(v___x_2901_);
lean_inc(v___x_2900_);
lean_inc_ref(v___x_2941_);
v___x_2943_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2916_, v_parserState_2832_, v___x_2941_, v___x_2900_, v___x_2863_, v___x_2901_, v___x_2942_, v_a_2833_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2945_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2946_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2830_, 3);
v___x_2947_ = l_Lean_Name_num___override(v___x_2946_, v___x_2830_);
v___x_2948_ = lean_unsigned_to_nat(32u);
v___x_2949_ = lean_mk_empty_array_with_capacity(v___x_2948_);
v___x_2950_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2951_ = ((size_t)5ULL);
v___x_2952_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2949_);
lean_ctor_set(v___x_2952_, 2, v___x_2830_);
lean_ctor_set(v___x_2952_, 3, v___x_2830_);
lean_ctor_set_usize(v___x_2952_, 4, v___x_2951_);
v_size_2953_ = lean_ctor_get(v___x_2938_, 2);
lean_inc(v_size_2953_);
v___x_2954_ = l_Lean_Name_str___override(v___x_2947_, v___x_2944_);
v___x_2955_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2834_);
v___x_2956_ = l_Lean_Name_str___override(v___x_2954_, v___x_2945_);
v___x_2957_ = l_Lean_Name_str___override(v___x_2956_, v___x_2944_);
v___x_2958_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2959_ = l_Lean_Name_str___override(v___x_2957_, v___x_2958_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2961_ = l_Lean_Name_str___override(v___x_2959_, v___x_2960_);
v___x_2962_ = l_Lean_Name_toString(v___x_2961_, v___x_2863_);
v___x_2963_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2964_ = 0ULL;
v___x_2965_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2965_, 0, v___x_2952_);
lean_ctor_set_uint64(v___x_2965_, sizeof(void*)*1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2901_);
v___x_2967_ = l_IO_Promise_result_x21___redArg(v___x_2900_);
lean_dec(v___x_2900_);
v___x_2968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2834_);
lean_ctor_set(v___x_2968_, 1, v___x_2955_);
lean_ctor_set(v___x_2968_, 2, v___x_2966_);
lean_ctor_set(v___x_2968_, 3, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2941_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_inc_ref(v___x_2965_);
lean_inc_ref(v___x_2962_);
v___x_2971_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2971_, 0, v___x_2962_);
lean_ctor_set(v___x_2971_, 1, v___x_2963_);
lean_ctor_set(v___x_2971_, 2, v___x_2916_);
lean_ctor_set(v___x_2971_, 3, v___x_2965_);
lean_ctor_set_uint8(v___x_2971_, sizeof(void*)*4, v___x_2879_);
v___x_2972_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2973_ = lean_nat_dec_lt(v___x_2830_, v_size_2953_);
lean_dec(v_size_2953_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec_ref(v___x_2938_);
lean_dec(v___x_2830_);
v___x_2974_ = l_outOfBounds___redArg(v___x_2972_);
v___y_2881_ = v___x_2865_;
v___y_2882_ = v___x_2971_;
v___y_2883_ = v___x_2962_;
v___y_2884_ = v___x_2965_;
v___y_2885_ = v___x_2970_;
v___y_2886_ = v___x_2974_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2972_, v___x_2938_, v___x_2830_);
lean_dec(v___x_2830_);
lean_dec_ref(v___x_2938_);
v___y_2881_ = v___x_2865_;
v___y_2882_ = v___x_2971_;
v___y_2883_ = v___x_2962_;
v___y_2884_ = v___x_2965_;
v___y_2885_ = v___x_2970_;
v___y_2886_ = v___x_2975_;
goto v___jp_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v_traceState_2895_);
lean_dec_ref(v___x_2878_);
lean_del_object(v___x_2875_);
lean_dec(v_snd_2873_);
lean_dec(v_fst_2872_);
lean_del_object(v___x_2870_);
lean_dec_ref(v___x_2865_);
lean_dec(v___x_2834_);
lean_dec_ref(v_parserState_2832_);
lean_dec_ref(v_fileMap_2831_);
lean_dec(v___x_2830_);
lean_dec(v_stx_2827_);
v_a_2981_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2896_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2896_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v___x_2865_);
lean_dec_ref(v_opts_2857_);
lean_dec(v___x_2852_);
lean_del_object(v___x_2842_);
lean_dec_ref(v___x_2835_);
lean_dec(v___x_2834_);
lean_dec_ref(v_parserState_2832_);
lean_dec_ref(v_fileMap_2831_);
lean_dec(v___x_2830_);
lean_dec(v_stx_2827_);
v_a_3043_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2867_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2867_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
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
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___x_2835_);
lean_dec(v___x_2834_);
lean_dec_ref(v_parserState_2832_);
lean_dec_ref(v_fileMap_2831_);
lean_dec(v___x_2830_);
lean_dec_ref(v_toProcessingContext_2829_);
lean_dec(v_origStx_2828_);
lean_dec(v_stx_2827_);
v_a_3054_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2839_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2839_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3062_, lean_object* v_stx_3063_, lean_object* v_origStx_3064_, lean_object* v_toProcessingContext_3065_, lean_object* v___x_3066_, lean_object* v_fileMap_3067_, lean_object* v_parserState_3068_, lean_object* v_a_3069_, lean_object* v___x_3070_, lean_object* v___x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3062_, v_stx_3063_, v_origStx_3064_, v_toProcessingContext_3065_, v___x_3066_, v_fileMap_3067_, v_parserState_3068_, v_a_3069_, v___x_3070_, v___x_3071_, v___y_3072_);
lean_dec_ref(v___y_3072_);
lean_dec_ref(v_a_3069_);
return v_res_3074_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___f_3076_; 
v___x_3075_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3076_, 0, v___x_3075_);
return v___f_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3077_, lean_object* v_stx_3078_, lean_object* v_origStx_3079_, lean_object* v_parserState_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_toProcessingContext_3083_; lean_object* v_fileMap_3084_; lean_object* v_endPos_3085_; lean_object* v___x_3086_; lean_object* v___f_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_toProcessingContext_3083_ = lean_ctor_get(v_a_3081_, 0);
v_fileMap_3084_ = lean_ctor_get(v_toProcessingContext_3083_, 2);
v_endPos_3085_ = lean_ctor_get(v_toProcessingContext_3083_, 3);
v___x_3086_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3087_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3088_ = lean_box(0);
v___x_3089_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3081_, 2);
lean_inc_ref(v_fileMap_3084_);
lean_inc_ref(v_toProcessingContext_3083_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3090_, 0, v_setupImports_3077_);
lean_closure_set(v___f_3090_, 1, v_stx_3078_);
lean_closure_set(v___f_3090_, 2, v_origStx_3079_);
lean_closure_set(v___f_3090_, 3, v_toProcessingContext_3083_);
lean_closure_set(v___f_3090_, 4, v___x_3089_);
lean_closure_set(v___f_3090_, 5, v_fileMap_3084_);
lean_closure_set(v___f_3090_, 6, v_parserState_3080_);
lean_closure_set(v___f_3090_, 7, v_a_3081_);
lean_closure_set(v___f_3090_, 8, v___x_3088_);
lean_closure_set(v___f_3090_, 9, v___x_3086_);
lean_inc(v_endPos_3085_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v_endPos_3085_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
v___x_3093_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3093_, 0, lean_box(0));
lean_closure_set(v___x_3093_, 1, v___f_3087_);
lean_closure_set(v___x_3093_, 2, v___f_3090_);
lean_closure_set(v___x_3093_, 3, v_a_3081_);
v___x_3094_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3088_, v___x_3088_, v___x_3092_, v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3095_, lean_object* v_stx_3096_, lean_object* v_origStx_3097_, lean_object* v_parserState_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3095_, v_stx_3096_, v_origStx_3097_, v_parserState_3098_, v_a_3099_);
lean_dec_ref(v_a_3099_);
return v_res_3101_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = 1;
v___x_3111_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3112_ = l_Lean_Name_toString(v___x_3111_, v___x_3110_);
return v___x_3112_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3113_ = 0;
v___x_3114_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3115_ = lean_box(0);
v___x_3116_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3117_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3118_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
lean_ctor_set(v___x_3118_, 1, v___x_3116_);
lean_ctor_set(v___x_3118_, 2, v___x_3115_);
lean_ctor_set(v___x_3118_, 3, v___x_3114_);
lean_ctor_set_uint8(v___x_3118_, sizeof(void*)*4, v___x_3113_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3119_, lean_object* v_cmdState_3120_, lean_object* v_a_3121_, lean_object* v_toSnapshot_3122_, lean_object* v_newStx_3123_, lean_object* v_oldCmd_3124_){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v_diagnostics_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3154_; 
v___x_3126_ = lean_io_promise_new();
v___x_3127_ = l_IO_CancelToken_new();
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_oldCmd_3124_);
v___x_3129_ = 1;
v___x_3130_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3127_);
lean_inc(v___x_3126_);
lean_inc_ref(v_cmdState_3120_);
v___x_3131_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3128_, v_newParserState_3119_, v_cmdState_3120_, v___x_3126_, v___x_3129_, v___x_3127_, v___x_3130_, v_a_3121_);
v_diagnostics_3132_ = lean_ctor_get(v_toSnapshot_3122_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_toSnapshot_3122_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; lean_object* v_unused_3156_; lean_object* v_unused_3157_; 
v_unused_3155_ = lean_ctor_get(v_toSnapshot_3122_, 3);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_toSnapshot_3122_, 2);
lean_dec(v_unused_3156_);
v_unused_3157_ = lean_ctor_get(v_toSnapshot_3122_, 0);
lean_dec(v_unused_3157_);
v___x_3134_ = v_toSnapshot_3122_;
v_isShared_3135_ = v_isSharedCheck_3154_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_diagnostics_3132_);
lean_dec(v_toSnapshot_3122_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3154_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3138_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3139_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3127_);
v___x_3141_ = l_IO_Promise_result_x21___redArg(v___x_3126_);
lean_dec(v___x_3126_);
v___x_3142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3136_);
lean_ctor_set(v___x_3142_, 1, v___x_3137_);
lean_ctor_set(v___x_3142_, 2, v___x_3140_);
lean_ctor_set(v___x_3142_, 3, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_cmdState_3120_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
v___x_3145_ = 0;
v___x_3146_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_newStx_3123_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 3, v___x_3139_);
lean_ctor_set(v___x_3134_, 2, v___x_3136_);
lean_ctor_set(v___x_3134_, 0, v___x_3138_);
v___x_3149_ = v___x_3134_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_diagnostics_3132_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v___x_3139_);
v___x_3149_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*4, v___x_3145_);
v___x_3150_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3147_, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3146_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
lean_ctor_set(v___x_3151_, 2, v___x_3144_);
v___x_3152_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3136_, v___x_3151_);
return v___x_3152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3158_, lean_object* v_cmdState_3159_, lean_object* v_a_3160_, lean_object* v_toSnapshot_3161_, lean_object* v_newStx_3162_, lean_object* v_oldCmd_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3158_, v_cmdState_3159_, v_a_3160_, v_toSnapshot_3161_, v_newStx_3162_, v_oldCmd_3163_);
lean_dec_ref(v_a_3160_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3166_, lean_object* v_a_3167_, lean_object* v_newStx_3168_, lean_object* v___x_3169_, lean_object* v_oldProcessed_3170_){
_start:
{
lean_object* v_result_x3f_3172_; 
v_result_x3f_3172_ = lean_ctor_get(v_oldProcessed_3170_, 2);
if (lean_obj_tag(v_result_x3f_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v_firstCmdSnap_3174_; lean_object* v_toSnapshot_3175_; lean_object* v_cmdState_3176_; lean_object* v_stx_x3f_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; lean_object* v___x_3181_; 
v_val_3173_ = lean_ctor_get(v_result_x3f_3172_, 0);
lean_inc(v_val_3173_);
v_firstCmdSnap_3174_ = lean_ctor_get(v_val_3173_, 1);
lean_inc_ref(v_firstCmdSnap_3174_);
v_toSnapshot_3175_ = lean_ctor_get(v_oldProcessed_3170_, 0);
lean_inc_ref(v_toSnapshot_3175_);
lean_dec_ref(v_oldProcessed_3170_);
v_cmdState_3176_ = lean_ctor_get(v_val_3173_, 0);
lean_inc_ref(v_cmdState_3176_);
lean_dec(v_val_3173_);
v_stx_x3f_3177_ = lean_ctor_get(v_firstCmdSnap_3174_, 0);
lean_inc(v_stx_x3f_3177_);
lean_inc_ref(v_a_3167_);
v___f_3178_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3178_, 0, v_newParserState_3166_);
lean_closure_set(v___f_3178_, 1, v_cmdState_3176_);
lean_closure_set(v___f_3178_, 2, v_a_3167_);
lean_closure_set(v___f_3178_, 3, v_toSnapshot_3175_);
lean_closure_set(v___f_3178_, 4, v_newStx_3168_);
v___x_3179_ = lean_box(0);
v___x_3180_ = 1;
v___x_3181_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3174_, v___f_3178_, v_stx_x3f_3177_, v___x_3169_, v___x_3179_, v___x_3180_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec(v___x_3169_);
lean_dec_ref(v_newParserState_3166_);
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_newStx_3168_);
v___x_3183_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3182_, v_oldProcessed_3170_);
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3184_, lean_object* v_a_3185_, lean_object* v_newStx_3186_, lean_object* v___x_3187_, lean_object* v_oldProcessed_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3184_, v_a_3185_, v_newStx_3186_, v___x_3187_, v_oldProcessed_3188_);
lean_dec_ref(v_a_3185_);
return v_res_3190_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3191_ = 0;
v___x_3192_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3193_ = lean_box(0);
v___x_3194_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3195_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3196_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v___x_3194_);
lean_ctor_set(v___x_3196_, 2, v___x_3193_);
lean_ctor_set(v___x_3196_, 3, v___x_3192_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*4, v___x_3191_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3197_, lean_object* v_a_3198_, lean_object* v_old_3199_, lean_object* v_newStx_3200_, lean_object* v_newParserState_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_result_x3f_3204_; 
v_result_x3f_3204_ = lean_ctor_get(v_old_3199_, 4);
lean_inc(v_result_x3f_3204_);
if (lean_obj_tag(v_result_x3f_3204_) == 1)
{
lean_object* v_val_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3259_; 
v_val_3205_ = lean_ctor_get(v_result_x3f_3204_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_result_x3f_3204_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3207_ = v_result_x3f_3204_;
v_isShared_3208_ = v_isSharedCheck_3259_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_val_3205_);
lean_dec(v_result_x3f_3204_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3259_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_processedSnap_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3257_; 
v_processedSnap_3209_ = lean_ctor_get(v_val_3205_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_val_3205_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v_val_3205_, 0);
lean_dec(v_unused_3258_);
v___x_3211_ = v_val_3205_;
v_isShared_3212_ = v_isSharedCheck_3257_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_processedSnap_3209_);
lean_dec(v_val_3205_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3257_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_toSnapshot_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3252_; 
v_toSnapshot_3213_ = lean_ctor_get(v_old_3199_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_old_3199_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; lean_object* v_unused_3256_; 
v_unused_3253_ = lean_ctor_get(v_old_3199_, 4);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_old_3199_, 3);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v_old_3199_, 2);
lean_dec(v_unused_3255_);
v_unused_3256_ = lean_ctor_get(v_old_3199_, 1);
lean_dec(v_unused_3256_);
v___x_3215_ = v_old_3199_;
v_isShared_3216_ = v_isSharedCheck_3252_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_toSnapshot_3213_);
lean_dec(v_old_3199_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3252_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v_pos_3217_; lean_object* v_endPos_3218_; lean_object* v_stx_x3f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v_diagnostics_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3248_; 
v_pos_3217_ = lean_ctor_get(v_newParserState_3201_, 0);
v_endPos_3218_ = lean_ctor_get(v_toProcessingContext_3197_, 3);
v_stx_x3f_3219_ = lean_ctor_get(v_processedSnap_3209_, 0);
lean_inc(v_stx_x3f_3219_);
lean_inc(v_endPos_3218_);
lean_inc(v_pos_3217_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_pos_3217_);
lean_ctor_set(v___x_3220_, 1, v_endPos_3218_);
v___x_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_inc_ref(v___x_3221_);
lean_inc(v_newStx_3200_);
lean_inc_ref(v_a_3198_);
lean_inc_ref(v_newParserState_3201_);
v___f_3222_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3222_, 0, v_newParserState_3201_);
lean_closure_set(v___f_3222_, 1, v_a_3198_);
lean_closure_set(v___f_3222_, 2, v_newStx_3200_);
lean_closure_set(v___f_3222_, 3, v___x_3221_);
v___x_3223_ = lean_box(0);
v___x_3224_ = 1;
v___x_3225_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3209_, v___f_3222_, v_stx_x3f_3219_, v___x_3221_, v___x_3223_, v___x_3224_);
v_diagnostics_3226_ = lean_ctor_get(v_toSnapshot_3213_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_toSnapshot_3213_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; lean_object* v_unused_3250_; lean_object* v_unused_3251_; 
v_unused_3249_ = lean_ctor_get(v_toSnapshot_3213_, 3);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_toSnapshot_3213_, 2);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v_toSnapshot_3213_, 0);
lean_dec(v_unused_3251_);
v___x_3228_ = v_toSnapshot_3213_;
v_isShared_3229_ = v_isSharedCheck_3248_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_diagnostics_3226_);
lean_dec(v_toSnapshot_3213_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3248_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3230_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3231_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v___x_3225_);
lean_ctor_set(v___x_3211_, 0, v_newParserState_3201_);
v___x_3233_ = v___x_3211_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_newParserState_3201_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3225_);
v___x_3233_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3235_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3233_);
v___x_3235_ = v___x_3207_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3236_ = 0;
v___x_3237_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3200_);
v___x_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_newStx_3200_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 3, v___x_3231_);
lean_ctor_set(v___x_3228_, 2, v___x_3223_);
lean_ctor_set(v___x_3228_, 0, v___x_3230_);
v___x_3240_ = v___x_3228_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_diagnostics_3226_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v___x_3231_);
v___x_3240_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
lean_ctor_set_uint8(v___x_3240_, sizeof(void*)*4, v___x_3236_);
v___x_3241_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3238_, v___x_3240_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 4, v___x_3235_);
lean_ctor_set(v___x_3215_, 3, v_newStx_3200_);
lean_ctor_set(v___x_3215_, 2, v_toProcessingContext_3197_);
lean_ctor_set(v___x_3215_, 1, v___x_3241_);
lean_ctor_set(v___x_3215_, 0, v___x_3237_);
v___x_3243_ = v___x_3215_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_toProcessingContext_3197_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_newStx_3200_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v___x_3235_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
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
lean_dec(v_result_x3f_3204_);
lean_dec_ref(v_newParserState_3201_);
lean_dec(v_newStx_3200_);
lean_dec_ref(v_toProcessingContext_3197_);
return v_old_3199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3260_, lean_object* v_a_3261_, lean_object* v_old_3262_, lean_object* v_newStx_3263_, lean_object* v_newParserState_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3260_, v_a_3261_, v_old_3262_, v_newStx_3263_, v_newParserState_3264_, v___y_3265_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_a_3261_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3268_, lean_object* v_setupImports_3269_, lean_object* v_old_x3f_3270_, lean_object* v___f_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; 
lean_inc_ref(v_toProcessingContext_3268_);
v___x_3274_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3268_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3344_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3344_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3344_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_snd_3279_; lean_object* v_fst_3280_; lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3343_; 
v_snd_3279_ = lean_ctor_get(v_a_3275_, 1);
lean_inc(v_snd_3279_);
v_fst_3280_ = lean_ctor_get(v_a_3275_, 0);
lean_inc(v_fst_3280_);
lean_dec(v_a_3275_);
v_fst_3281_ = lean_ctor_get(v_snd_3279_, 0);
v_snd_3282_ = lean_ctor_get(v_snd_3279_, 1);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_snd_3279_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3284_ = v_snd_3279_;
v_isShared_3285_ = v_isSharedCheck_3343_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_dec(v_snd_3279_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3343_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
uint8_t v___x_3286_; 
v___x_3286_ = l_Lean_MessageLog_hasErrors(v_snd_3282_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___y_3289_; 
lean_inc(v_fst_3280_);
v___x_3287_ = l_Lean_Syntax_unsetTrailing(v_fst_3280_);
if (lean_obj_tag(v_old_x3f_3270_) == 1)
{
lean_object* v_val_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3326_; 
v_val_3310_ = lean_ctor_get(v_old_x3f_3270_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_old_x3f_3270_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3312_ = v_old_x3f_3270_;
v_isShared_3313_ = v_isSharedCheck_3326_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_val_3310_);
lean_dec(v_old_x3f_3270_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3326_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v_stx_3314_; lean_object* v_result_x3f_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_stx_3314_ = lean_ctor_get(v_val_3310_, 3);
v_result_x3f_3315_ = lean_ctor_get(v_val_3310_, 4);
lean_inc(v_stx_3314_);
v___x_3316_ = l_Lean_Syntax_unsetTrailing(v_stx_3314_);
lean_inc(v___x_3287_);
v___x_3317_ = l_Lean_Syntax_eqWithInfo(v___x_3287_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_inc(v_result_x3f_3315_);
lean_del_object(v___x_3312_);
lean_dec(v_val_3310_);
lean_dec_ref(v___f_3271_);
if (lean_obj_tag(v_result_x3f_3315_) == 0)
{
v___y_3289_ = v___y_3272_;
goto v___jp_3288_;
}
else
{
lean_object* v_val_3318_; lean_object* v_processedSnap_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_val_3318_ = lean_ctor_get(v_result_x3f_3315_, 0);
lean_inc(v_val_3318_);
lean_dec_ref_known(v_result_x3f_3315_, 1);
v_processedSnap_3319_ = lean_ctor_get(v_val_3318_, 1);
lean_inc_ref(v_processedSnap_3319_);
lean_dec(v_val_3318_);
v___x_3320_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3321_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3320_, v_processedSnap_3319_);
v___y_3289_ = v___y_3272_;
goto v___jp_3288_;
}
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec(v___x_3287_);
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_del_object(v___x_3277_);
lean_dec_ref(v_setupImports_3269_);
lean_dec_ref(v_toProcessingContext_3268_);
lean_inc_ref(v___y_3272_);
v___x_3322_ = lean_apply_5(v___f_3271_, v_val_3310_, v_fst_3280_, v_fst_3281_, v___y_3272_, lean_box(0));
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3322_);
v___x_3324_ = v___x_3312_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
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
else
{
lean_dec_ref(v___f_3271_);
lean_dec(v_old_x3f_3270_);
v___y_3289_ = v___y_3272_;
goto v___jp_3288_;
}
v___jp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3290_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_inc(v_fst_3280_);
v___x_3291_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3269_, v___x_3287_, v_fst_3280_, v_fst_3281_, v___y_3289_);
v___x_3292_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3293_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_unsigned_to_nat(32u);
v___x_3296_ = lean_mk_empty_array_with_capacity(v___x_3295_);
lean_dec_ref(v___x_3296_);
v___x_3297_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3291_);
v___x_3299_ = v___x_3284_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_fst_3281_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v___x_3291_);
v___x_3299_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
v___x_3301_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3301_, 0, v___x_3292_);
lean_ctor_set(v___x_3301_, 1, v___x_3293_);
lean_ctor_set(v___x_3301_, 2, v___x_3294_);
lean_ctor_set(v___x_3301_, 3, v___x_3297_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*4, v___x_3286_);
lean_inc(v_fst_3280_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v_fst_3280_);
v___x_3303_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3303_, 0, v___x_3292_);
lean_ctor_set(v___x_3303_, 1, v___x_3290_);
lean_ctor_set(v___x_3303_, 2, v___x_3294_);
lean_ctor_set(v___x_3303_, 3, v___x_3297_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*4, v___x_3286_);
v___x_3304_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3301_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
lean_ctor_set(v___x_3305_, 2, v_toProcessingContext_3268_);
lean_ctor_set(v___x_3305_, 3, v_fst_3280_);
lean_ctor_set(v___x_3305_, 4, v___x_3300_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3305_);
v___x_3307_ = v___x_3277_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
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
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
lean_del_object(v___x_3284_);
lean_dec(v_fst_3281_);
lean_dec_ref(v___f_3271_);
lean_dec(v_old_x3f_3270_);
lean_dec_ref(v_setupImports_3269_);
v___x_3327_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3282_);
v___x_3328_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3329_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_unsigned_to_nat(32u);
v___x_3332_ = lean_mk_empty_array_with_capacity(v___x_3331_);
lean_dec_ref(v___x_3332_);
v___x_3333_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3334_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3334_, 0, v___x_3328_);
lean_ctor_set(v___x_3334_, 1, v___x_3329_);
lean_ctor_set(v___x_3334_, 2, v___x_3330_);
lean_ctor_set(v___x_3334_, 3, v___x_3333_);
lean_ctor_set_uint8(v___x_3334_, sizeof(void*)*4, v___x_3286_);
lean_inc(v_fst_3280_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_fst_3280_);
v___x_3336_ = 0;
v___x_3337_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3337_, 0, v___x_3328_);
lean_ctor_set(v___x_3337_, 1, v___x_3327_);
lean_ctor_set(v___x_3337_, 2, v___x_3330_);
lean_ctor_set(v___x_3337_, 3, v___x_3333_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*4, v___x_3336_);
v___x_3338_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3335_, v___x_3337_);
v___x_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3334_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
lean_ctor_set(v___x_3339_, 2, v_toProcessingContext_3268_);
lean_ctor_set(v___x_3339_, 3, v_fst_3280_);
lean_ctor_set(v___x_3339_, 4, v___x_3330_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3339_);
v___x_3341_ = v___x_3277_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v___f_3271_);
lean_dec(v_old_x3f_3270_);
lean_dec_ref(v_setupImports_3269_);
lean_dec_ref(v_toProcessingContext_3268_);
v_a_3345_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3274_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3274_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3353_, lean_object* v_setupImports_3354_, lean_object* v_old_x3f_3355_, lean_object* v___f_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3353_, v_setupImports_3354_, v_old_x3f_3355_, v___f_3356_, v___y_3357_);
lean_dec_ref(v___y_3357_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3360_, lean_object* v_toProcessingContext_3361_, lean_object* v_x_3362_){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3363_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3360_);
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3366_, 0, v_x_3362_);
lean_ctor_set(v___x_3366_, 1, v___x_3363_);
lean_ctor_set(v___x_3366_, 2, v_toProcessingContext_3361_);
lean_ctor_set(v___x_3366_, 3, v___x_3364_);
lean_ctor_set(v___x_3366_, 4, v___x_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3367_, lean_object* v_old_x3f_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_toProcessingContext_3371_; lean_object* v___x_3372_; lean_object* v___f_3373_; lean_object* v___f_3374_; lean_object* v___f_3375_; 
v_toProcessingContext_3371_ = lean_ctor_get(v_a_3369_, 0);
v___x_3372_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3369_);
lean_inc_ref_n(v_toProcessingContext_3371_, 3);
v___f_3373_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3373_, 0, v_toProcessingContext_3371_);
lean_closure_set(v___f_3373_, 1, v_a_3369_);
lean_inc(v_old_x3f_3368_);
v___f_3374_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3374_, 0, v_toProcessingContext_3371_);
lean_closure_set(v___f_3374_, 1, v_setupImports_3367_);
lean_closure_set(v___f_3374_, 2, v_old_x3f_3368_);
lean_closure_set(v___f_3374_, 3, v___f_3373_);
v___f_3375_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3375_, 0, v___x_3372_);
lean_closure_set(v___f_3375_, 1, v_toProcessingContext_3371_);
if (lean_obj_tag(v_old_x3f_3368_) == 1)
{
lean_object* v_val_3376_; lean_object* v_result_x3f_3377_; 
v_val_3376_ = lean_ctor_get(v_old_x3f_3368_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_old_x3f_3368_, 1);
v_result_x3f_3377_ = lean_ctor_get(v_val_3376_, 4);
if (lean_obj_tag(v_result_x3f_3377_) == 1)
{
lean_object* v_stx_3378_; lean_object* v_val_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_stx_3378_ = lean_ctor_get(v_val_3376_, 3);
lean_inc(v_stx_3378_);
v_val_3379_ = lean_ctor_get(v_result_x3f_3377_, 0);
lean_inc(v_val_3376_);
v___x_3380_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3376_);
v___x_3381_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3380_);
if (lean_obj_tag(v___x_3381_) == 1)
{
lean_object* v_val_3382_; 
v_val_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v___x_3381_, 1);
if (lean_obj_tag(v_val_3382_) == 1)
{
lean_object* v_val_3383_; lean_object* v_firstCmdSnap_3384_; lean_object* v___x_3385_; 
v_val_3383_ = lean_ctor_get(v_val_3382_, 0);
lean_inc(v_val_3383_);
lean_dec_ref_known(v_val_3382_, 1);
v_firstCmdSnap_3384_ = lean_ctor_get(v_val_3383_, 1);
lean_inc_ref(v_firstCmdSnap_3384_);
lean_dec(v_val_3383_);
v___x_3385_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3384_);
if (lean_obj_tag(v___x_3385_) == 1)
{
lean_object* v_val_3386_; lean_object* v_nextCmdSnap_x3f_3387_; 
v_val_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_val_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v_nextCmdSnap_x3f_3387_ = lean_ctor_get(v_val_3386_, 4);
lean_inc(v_nextCmdSnap_x3f_3387_);
lean_dec(v_val_3386_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3387_) == 0)
{
lean_object* v___x_3388_; 
lean_dec(v_stx_3378_);
lean_dec(v_val_3376_);
v___x_3388_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3388_;
}
else
{
lean_object* v_val_3389_; lean_object* v___x_3390_; 
v_val_3389_ = lean_ctor_get(v_nextCmdSnap_x3f_3387_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3387_, 1);
v___x_3390_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3389_);
if (lean_obj_tag(v___x_3390_) == 1)
{
lean_object* v_val_3391_; lean_object* v_parserState_3392_; lean_object* v_pos_3393_; uint8_t v___x_3394_; 
v_val_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_val_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v_parserState_3392_ = lean_ctor_get(v_val_3391_, 2);
lean_inc_ref(v_parserState_3392_);
lean_dec(v_val_3391_);
v_pos_3393_ = lean_ctor_get(v_parserState_3392_, 0);
lean_inc(v_pos_3393_);
lean_dec_ref(v_parserState_3392_);
v___x_3394_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3393_, v_a_3369_);
lean_dec(v_pos_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
lean_dec(v_stx_3378_);
lean_dec(v_val_3376_);
v___x_3395_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3395_;
}
else
{
lean_object* v_parserState_3396_; lean_object* v___x_3397_; 
lean_dec_ref(v___f_3375_);
lean_dec_ref(v___f_3374_);
v_parserState_3396_ = lean_ctor_get(v_val_3379_, 0);
lean_inc_ref(v_parserState_3396_);
lean_inc_ref(v_toProcessingContext_3371_);
v___x_3397_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3371_, v_a_3369_, v_val_3376_, v_stx_3378_, v_parserState_3396_, v_a_3369_);
return v___x_3397_;
}
}
else
{
lean_object* v___x_3398_; 
lean_dec(v___x_3390_);
lean_dec(v_stx_3378_);
lean_dec(v_val_3376_);
v___x_3398_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3398_;
}
}
}
else
{
lean_object* v___x_3399_; 
lean_dec(v___x_3385_);
lean_dec(v_stx_3378_);
lean_dec(v_val_3376_);
v___x_3399_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3399_;
}
}
else
{
lean_object* v___x_3400_; 
lean_dec(v_val_3382_);
lean_dec(v_stx_3378_);
lean_dec(v_val_3376_);
v___x_3400_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3400_;
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v___x_3381_);
lean_dec(v_stx_3378_);
lean_dec(v_val_3376_);
v___x_3401_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3401_;
}
}
else
{
lean_object* v___x_3402_; 
lean_dec(v_val_3376_);
v___x_3402_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3402_;
}
}
else
{
lean_object* v___x_3403_; 
lean_dec(v_old_x3f_3368_);
v___x_3403_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3375_, v___f_3374_, v_a_3369_);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3404_, lean_object* v_old_x3f_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3404_, v_old_x3f_3405_, v_a_3406_);
lean_dec_ref(v_a_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3409_, lean_object* v_old_x3f_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v___x_3413_; 
lean_inc(v_old_x3f_3410_);
v___x_3413_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3413_, 0, v_setupImports_3409_);
lean_closure_set(v___x_3413_, 1, v_old_x3f_3410_);
if (lean_obj_tag(v_old_x3f_3410_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_box(0);
v___x_3415_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3413_, v___x_3414_, v_a_3411_);
return v___x_3415_;
}
else
{
lean_object* v_val_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3425_; 
v_val_3416_ = lean_ctor_get(v_old_x3f_3410_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_old_x3f_3410_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3418_ = v_old_x3f_3410_;
v_isShared_3419_ = v_isSharedCheck_3425_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_val_3416_);
lean_dec(v_old_x3f_3410_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3425_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_ictx_3420_; lean_object* v___x_3422_; 
v_ictx_3420_ = lean_ctor_get(v_val_3416_, 2);
lean_inc_ref(v_ictx_3420_);
lean_dec(v_val_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v_ictx_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_ictx_3420_);
v___x_3422_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3413_, v___x_3422_, v_a_3411_);
return v___x_3423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3426_, lean_object* v_old_x3f_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Language_Lean_process(v_setupImports_3426_, v_old_x3f_3427_, v_a_3428_);
lean_dec_ref(v_a_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3431_, lean_object* v_parserState_3432_, lean_object* v_commandState_3433_, lean_object* v_old_x3f_3434_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3444_; 
v___x_3436_ = lean_io_promise_new();
v___x_3437_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3434_) == 0)
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_box(0);
v___y_3444_ = v___x_3459_;
goto v___jp_3443_;
}
else
{
lean_object* v_val_3460_; lean_object* v_snd_3461_; lean_object* v___x_3462_; 
v_val_3460_ = lean_ctor_get(v_old_x3f_3434_, 0);
v_snd_3461_ = lean_ctor_get(v_val_3460_, 1);
lean_inc(v_snd_3461_);
v___x_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_snd_3461_);
v___y_3444_ = v___x_3462_;
goto v___jp_3443_;
}
v___jp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3439_, v___y_3440_, v_inputCtx_3431_);
lean_dec(v___x_3441_);
v___x_3442_ = l_IO_Promise_result_x21___redArg(v___x_3436_);
lean_dec(v___x_3436_);
return v___x_3442_;
}
v___jp_3443_:
{
uint8_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3445_ = 1;
v___x_3446_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
v___x_3447_ = lean_box(v___x_3445_);
lean_inc(v___x_3436_);
v___x_3448_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3448_, 0, v___y_3444_);
lean_closure_set(v___x_3448_, 1, v_parserState_3432_);
lean_closure_set(v___x_3448_, 2, v_commandState_3433_);
lean_closure_set(v___x_3448_, 3, v___x_3436_);
lean_closure_set(v___x_3448_, 4, v___x_3447_);
lean_closure_set(v___x_3448_, 5, v___x_3437_);
lean_closure_set(v___x_3448_, 6, v___x_3446_);
if (lean_obj_tag(v_old_x3f_3434_) == 0)
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_box(0);
v___y_3439_ = v___x_3448_;
v___y_3440_ = v___x_3449_;
goto v___jp_3438_;
}
else
{
lean_object* v_val_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3458_; 
v_val_3450_ = lean_ctor_get(v_old_x3f_3434_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_old_x3f_3434_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3452_ = v_old_x3f_3434_;
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_val_3450_);
lean_dec(v_old_x3f_3434_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_fst_3454_; lean_object* v___x_3456_; 
v_fst_3454_ = lean_ctor_get(v_val_3450_, 0);
lean_inc(v_fst_3454_);
lean_dec(v_val_3450_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v_fst_3454_);
v___x_3456_ = v___x_3452_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_fst_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
v___y_3439_ = v___x_3448_;
v___y_3440_ = v___x_3456_;
goto v___jp_3438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3463_, lean_object* v_parserState_3464_, lean_object* v_commandState_3465_, lean_object* v_old_x3f_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3463_, v_parserState_3464_, v_commandState_3465_, v_old_x3f_3466_);
lean_dec_ref(v_inputCtx_3463_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3469_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3470_; 
v_nextCmdSnap_x3f_3470_ = lean_ctor_get(v_snap_3469_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3470_) == 1)
{
lean_object* v_val_3471_; lean_object* v___x_3472_; 
lean_inc_ref(v_nextCmdSnap_x3f_3470_);
lean_dec_ref(v_snap_3469_);
v_val_3471_ = lean_ctor_get(v_nextCmdSnap_x3f_3470_, 0);
lean_inc(v_val_3471_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3470_, 1);
v___x_3472_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3471_);
v_snap_3469_ = v___x_3472_;
goto _start;
}
else
{
lean_object* v_elabSnap_3474_; lean_object* v_resultSnap_3475_; lean_object* v___x_3476_; lean_object* v_cmdState_3477_; lean_object* v___x_3478_; 
v_elabSnap_3474_ = lean_ctor_get(v_snap_3469_, 3);
lean_inc_ref(v_elabSnap_3474_);
lean_dec_ref(v_snap_3469_);
v_resultSnap_3475_ = lean_ctor_get(v_elabSnap_3474_, 2);
lean_inc_ref(v_resultSnap_3475_);
lean_dec_ref(v_elabSnap_3474_);
v___x_3476_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3475_);
v_cmdState_3477_ = lean_ctor_get(v___x_3476_, 1);
lean_inc_ref(v_cmdState_3477_);
lean_dec(v___x_3476_);
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_cmdState_3477_);
return v___x_3478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3479_){
_start:
{
lean_object* v_result_x3f_3480_; 
v_result_x3f_3480_ = lean_ctor_get(v_snap_3479_, 4);
lean_inc(v_result_x3f_3480_);
lean_dec_ref(v_snap_3479_);
if (lean_obj_tag(v_result_x3f_3480_) == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_box(0);
return v___x_3481_;
}
else
{
lean_object* v_val_3482_; lean_object* v_processedSnap_3483_; lean_object* v___x_3484_; lean_object* v_result_x3f_3485_; 
v_val_3482_ = lean_ctor_get(v_result_x3f_3480_, 0);
lean_inc(v_val_3482_);
lean_dec_ref_known(v_result_x3f_3480_, 1);
v_processedSnap_3483_ = lean_ctor_get(v_val_3482_, 1);
lean_inc_ref(v_processedSnap_3483_);
lean_dec(v_val_3482_);
v___x_3484_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3483_);
v_result_x3f_3485_ = lean_ctor_get(v___x_3484_, 2);
lean_inc(v_result_x3f_3485_);
lean_dec(v___x_3484_);
if (lean_obj_tag(v_result_x3f_3485_) == 0)
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_box(0);
return v___x_3486_;
}
else
{
lean_object* v_val_3487_; lean_object* v_firstCmdSnap_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v_val_3487_ = lean_ctor_get(v_result_x3f_3485_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v_result_x3f_3485_, 1);
v_firstCmdSnap_3488_ = lean_ctor_get(v_val_3487_, 1);
lean_inc_ref(v_firstCmdSnap_3488_);
lean_dec(v_val_3487_);
v___x_3489_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3488_);
v___x_3490_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3489_);
return v___x_3490_;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = 1;
v___x_3497_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3498_ = l_Lean_Name_toString(v___x_3497_, v___x_3496_);
return v___x_3498_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3499_ = 0;
v___x_3500_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3501_ = lean_box(0);
v___x_3502_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3503_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3504_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3502_);
lean_ctor_set(v___x_3504_, 2, v___x_3501_);
lean_ctor_set(v___x_3504_, 3, v___x_3500_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*4, v___x_3499_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3506_ = lean_box(0);
v___x_3507_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3506_, v___x_3505_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3508_){
_start:
{
lean_object* v_result_x3f_3509_; 
v_result_x3f_3509_ = lean_ctor_get(v_snap_3508_, 4);
lean_inc(v_result_x3f_3509_);
if (lean_obj_tag(v_result_x3f_3509_) == 1)
{
lean_object* v_val_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3584_; 
v_val_3510_ = lean_ctor_get(v_result_x3f_3509_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_result_x3f_3509_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3512_ = v_result_x3f_3509_;
v_isShared_3513_ = v_isSharedCheck_3584_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_val_3510_);
lean_dec(v_result_x3f_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3584_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_toSnapshot_3514_; lean_object* v_metaSnap_3515_; lean_object* v_ictx_3516_; lean_object* v_stx_3517_; lean_object* v_parserState_3518_; lean_object* v_processedSnap_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3583_; 
v_toSnapshot_3514_ = lean_ctor_get(v_snap_3508_, 0);
v_metaSnap_3515_ = lean_ctor_get(v_snap_3508_, 1);
v_ictx_3516_ = lean_ctor_get(v_snap_3508_, 2);
v_stx_3517_ = lean_ctor_get(v_snap_3508_, 3);
v_parserState_3518_ = lean_ctor_get(v_val_3510_, 0);
v_processedSnap_3519_ = lean_ctor_get(v_val_3510_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_val_3510_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3521_ = v_val_3510_;
v_isShared_3522_ = v_isSharedCheck_3583_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_processedSnap_3519_);
lean_inc(v_parserState_3518_);
lean_dec(v_val_3510_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3583_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_processed_3523_; lean_object* v_result_x3f_3524_; 
v_processed_3523_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3519_);
v_result_x3f_3524_ = lean_ctor_get(v_processed_3523_, 2);
lean_inc(v_result_x3f_3524_);
if (lean_obj_tag(v_result_x3f_3524_) == 1)
{
lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3577_; 
lean_inc(v_stx_3517_);
lean_inc_ref(v_ictx_3516_);
lean_inc_ref(v_metaSnap_3515_);
lean_inc_ref(v_toSnapshot_3514_);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_snap_3508_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3578_ = lean_ctor_get(v_snap_3508_, 4);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_snap_3508_, 3);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_snap_3508_, 2);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_snap_3508_, 1);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_snap_3508_, 0);
lean_dec(v_unused_3582_);
v___x_3526_ = v_snap_3508_;
v_isShared_3527_ = v_isSharedCheck_3577_;
goto v_resetjp_3525_;
}
else
{
lean_dec(v_snap_3508_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3577_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_val_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3576_; 
v_val_3528_ = lean_ctor_get(v_result_x3f_3524_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_result_x3f_3524_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3530_ = v_result_x3f_3524_;
v_isShared_3531_ = v_isSharedCheck_3576_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_val_3528_);
lean_dec(v_result_x3f_3524_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3576_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v_toSnapshot_3532_; lean_object* v_metaSnap_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3574_; 
v_toSnapshot_3532_ = lean_ctor_get(v_processed_3523_, 0);
v_metaSnap_3533_ = lean_ctor_get(v_processed_3523_, 1);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_processed_3523_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v_processed_3523_, 2);
lean_dec(v_unused_3575_);
v___x_3535_ = v_processed_3523_;
v_isShared_3536_ = v_isSharedCheck_3574_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_metaSnap_3533_);
lean_inc(v_toSnapshot_3532_);
lean_dec(v_processed_3523_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3574_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v_cmdState_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3572_; 
v_cmdState_3537_ = lean_ctor_get(v_val_3528_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_val_3528_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_val_3528_, 1);
lean_dec(v_unused_3573_);
v___x_3539_ = v_val_3528_;
v_isShared_3540_ = v_isSharedCheck_3572_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_cmdState_3537_);
lean_dec(v_val_3528_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3572_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v_resultSnap_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v_elabSnap_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v_termCmd_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
lean_inc_ref(v_cmdState_3537_);
v_resultSnap_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_resultSnap_3543_, 0, v___x_3542_);
lean_ctor_set(v_resultSnap_3543_, 1, v_cmdState_3537_);
v___x_3544_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
v___x_3545_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3541_, v_resultSnap_3543_);
v___x_3546_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3547_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v_elabSnap_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3548_, 0, v___x_3542_);
lean_ctor_set(v_elabSnap_3548_, 1, v___x_3544_);
lean_ctor_set(v_elabSnap_3548_, 2, v___x_3545_);
lean_ctor_set(v_elabSnap_3548_, 3, v___x_3546_);
lean_ctor_set(v_elabSnap_3548_, 4, v___x_3547_);
v___x_3549_ = lean_box(0);
v___x_3550_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3551_, 0, v___x_3542_);
lean_ctor_set(v_termCmd_3551_, 1, v___x_3549_);
lean_ctor_set(v_termCmd_3551_, 2, v___x_3550_);
lean_ctor_set(v_termCmd_3551_, 3, v_elabSnap_3548_);
lean_ctor_set(v_termCmd_3551_, 4, v___x_3541_);
v___x_3552_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3541_, v_termCmd_3551_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 1, v___x_3552_);
v___x_3554_ = v___x_3539_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_cmdState_3537_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3556_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3554_);
v___x_3556_ = v___x_3530_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v_newProcessed_3558_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 2, v___x_3556_);
v_newProcessed_3558_ = v___x_3535_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_toSnapshot_3532_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_metaSnap_3533_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v___x_3556_);
v_newProcessed_3558_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3541_, v_newProcessed_3558_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___x_3559_);
v___x_3561_ = v___x_3521_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_parserState_3518_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3561_);
v___x_3563_ = v___x_3512_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 4, v___x_3563_);
v___x_3565_ = v___x_3526_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_toSnapshot_3514_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_metaSnap_3515_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_ictx_3516_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_stx_3517_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
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
lean_dec(v_result_x3f_3524_);
lean_dec(v_processed_3523_);
lean_del_object(v___x_3521_);
lean_dec_ref(v_parserState_3518_);
lean_del_object(v___x_3512_);
return v_snap_3508_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3509_);
return v_snap_3508_;
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

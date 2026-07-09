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
lean_dec_ref_known(v___x_562_, 1);
if (lean_obj_tag(v_val_564_) == 1)
{
uint8_t v_v_565_; 
v_v_565_ = lean_ctor_get_uint8(v_val_564_, 0);
lean_dec_ref_known(v_val_564_, 0);
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
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_Language_Snapshot_transform(v_val_573_, v___y_574_);
v___x_576_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_578_, v___y_579_);
lean_dec_ref(v___y_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_581_, lean_object* v_val_582_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_inc_ref(v_val_582_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_583_, 0, v_val_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_inst_581_);
lean_ctor_set(v___x_584_, 1, v_val_582_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___f_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_586_, lean_object* v_cmds_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_589_);
lean_dec_ref(v___x_591_);
v___x_592_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_586_, v_cmds_587_, v___y_588_, v___y_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_593_, lean_object* v_cmds_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_593_, v_cmds_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_599_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
lean_ctor_set(v___x_604_, 2, v___x_603_);
lean_ctor_set(v___x_604_, 3, v___x_603_);
lean_ctor_set(v___x_604_, 4, v___x_602_);
lean_ctor_set(v___x_604_, 5, v___x_602_);
lean_ctor_set(v___x_604_, 6, v___x_602_);
lean_ctor_set(v___x_604_, 7, v___x_602_);
lean_ctor_set(v___x_604_, 8, v___x_602_);
lean_ctor_set(v___x_604_, 9, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(32u);
v___x_606_ = lean_mk_empty_array_with_capacity(v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_608_ = ((size_t)5ULL);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_unsigned_to_nat(32u);
v___x_611_ = lean_mk_empty_array_with_capacity(v___x_610_);
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_613_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___x_609_);
lean_ctor_set(v___x_613_, 3, v___x_609_);
lean_ctor_set_usize(v___x_613_, 4, v___x_608_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_box(1);
v___x_615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_616_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; lean_object* v_env_622_; lean_object* v___x_623_; lean_object* v_scopes_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_opts_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_621_ = lean_st_ref_get(v___y_619_);
v_env_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_621_);
v___x_623_ = lean_st_ref_get(v___y_619_);
v_scopes_624_ = lean_ctor_get(v___x_623_, 2);
lean_inc(v_scopes_624_);
lean_dec(v___x_623_);
v___x_625_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_626_ = l_List_head_x21___redArg(v___x_625_, v_scopes_624_);
lean_dec(v_scopes_624_);
v_opts_627_ = lean_ctor_get(v___x_626_, 1);
lean_inc_ref(v_opts_627_);
lean_dec(v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_629_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_630_, 0, v_env_622_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set(v___x_630_, 3, v_opts_627_);
v___x_631_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_msgData_618_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_633_, v___y_634_);
lean_dec(v___y_634_);
return v_res_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v___y_637_, uint8_t v_suppressElabErrors_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_639_) == 1)
{
lean_object* v_pre_640_; 
v_pre_640_ = lean_ctor_get(v_x_639_, 0);
if (lean_obj_tag(v_pre_640_) == 0)
{
lean_object* v_str_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_str_641_ = lean_ctor_get(v_x_639_, 1);
v___x_642_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_643_ = lean_string_dec_eq(v_str_641_, v___x_642_);
if (v___x_643_ == 0)
{
return v___y_637_;
}
else
{
return v_suppressElabErrors_638_;
}
}
else
{
return v___y_637_;
}
}
else
{
return v___y_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v___y_644_, lean_object* v_suppressElabErrors_645_, lean_object* v_x_646_){
_start:
{
uint8_t v___y_9165__boxed_647_; uint8_t v_suppressElabErrors_boxed_648_; uint8_t v_res_649_; lean_object* v_r_650_; 
v___y_9165__boxed_647_ = lean_unbox(v___y_644_);
v_suppressElabErrors_boxed_648_ = lean_unbox(v_suppressElabErrors_645_);
v_res_649_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9165__boxed_647_, v_suppressElabErrors_boxed_648_, v_x_646_);
lean_dec(v_x_646_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_652_, lean_object* v_msgData_653_, uint8_t v_severity_654_, uint8_t v_isSilent_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint8_t v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; uint8_t v___y_723_; uint8_t v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; uint8_t v___y_751_; uint8_t v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; uint8_t v___y_759_; uint8_t v___y_760_; uint8_t v___y_761_; uint8_t v___x_776_; uint8_t v___y_778_; uint8_t v___y_779_; uint8_t v___y_780_; uint8_t v___y_782_; uint8_t v___x_794_; 
v___x_776_ = 2;
v___x_794_ = l_Lean_instBEqMessageSeverity_beq(v_severity_654_, v___x_776_);
if (v___x_794_ == 0)
{
v___y_782_ = v___x_794_;
goto v___jp_781_;
}
else
{
uint8_t v___x_795_; 
lean_inc_ref(v_msgData_653_);
v___x_795_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_653_);
v___y_782_ = v___x_795_;
goto v___jp_781_;
}
v___jp_659_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Elab_Command_getScope___redArg(v___y_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_Elab_Command_getScope___redArg(v___y_667_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_705_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_705_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_705_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_705_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v_currNamespace_676_; lean_object* v_openDecls_677_; lean_object* v_env_678_; lean_object* v_messages_679_; lean_object* v_scopes_680_; lean_object* v_usedQuotCtxts_681_; lean_object* v_nextMacroScope_682_; lean_object* v_maxRecDepth_683_; lean_object* v_ngen_684_; lean_object* v_auxDeclNGen_685_; lean_object* v_infoState_686_; lean_object* v_traceState_687_; lean_object* v_snapshotTasks_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_704_; 
v___x_675_ = lean_st_ref_take(v___y_667_);
v_currNamespace_676_ = lean_ctor_get(v_a_669_, 2);
lean_inc(v_currNamespace_676_);
lean_dec(v_a_669_);
v_openDecls_677_ = lean_ctor_get(v_a_671_, 3);
lean_inc(v_openDecls_677_);
lean_dec(v_a_671_);
v_env_678_ = lean_ctor_get(v___x_675_, 0);
v_messages_679_ = lean_ctor_get(v___x_675_, 1);
v_scopes_680_ = lean_ctor_get(v___x_675_, 2);
v_usedQuotCtxts_681_ = lean_ctor_get(v___x_675_, 3);
v_nextMacroScope_682_ = lean_ctor_get(v___x_675_, 4);
v_maxRecDepth_683_ = lean_ctor_get(v___x_675_, 5);
v_ngen_684_ = lean_ctor_get(v___x_675_, 6);
v_auxDeclNGen_685_ = lean_ctor_get(v___x_675_, 7);
v_infoState_686_ = lean_ctor_get(v___x_675_, 8);
v_traceState_687_ = lean_ctor_get(v___x_675_, 9);
v_snapshotTasks_688_ = lean_ctor_get(v___x_675_, 10);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_704_ == 0)
{
v___x_690_ = v___x_675_;
v_isShared_691_ = v_isSharedCheck_704_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snapshotTasks_688_);
lean_inc(v_traceState_687_);
lean_inc(v_infoState_686_);
lean_inc(v_auxDeclNGen_685_);
lean_inc(v_ngen_684_);
lean_inc(v_maxRecDepth_683_);
lean_inc(v_nextMacroScope_682_);
lean_inc(v_usedQuotCtxts_681_);
lean_inc(v_scopes_680_);
lean_inc(v_messages_679_);
lean_inc(v_env_678_);
lean_dec(v___x_675_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_704_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_currNamespace_676_);
lean_ctor_set(v___x_692_, 1, v_openDecls_677_);
v___x_693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___y_660_);
lean_inc_ref(v___y_662_);
lean_inc_ref(v___y_666_);
v___x_694_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_694_, 0, v___y_666_);
lean_ctor_set(v___x_694_, 1, v___y_665_);
lean_ctor_set(v___x_694_, 2, v___y_663_);
lean_ctor_set(v___x_694_, 3, v___y_662_);
lean_ctor_set(v___x_694_, 4, v___x_693_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*5, v___y_661_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*5 + 1, v___y_664_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*5 + 2, v_isSilent_655_);
v___x_695_ = l_Lean_MessageLog_add(v___x_694_, v_messages_679_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_695_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_env_678_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_scopes_680_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_usedQuotCtxts_681_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_nextMacroScope_682_);
lean_ctor_set(v_reuseFailAlloc_703_, 5, v_maxRecDepth_683_);
lean_ctor_set(v_reuseFailAlloc_703_, 6, v_ngen_684_);
lean_ctor_set(v_reuseFailAlloc_703_, 7, v_auxDeclNGen_685_);
lean_ctor_set(v_reuseFailAlloc_703_, 8, v_infoState_686_);
lean_ctor_set(v_reuseFailAlloc_703_, 9, v_traceState_687_);
lean_ctor_set(v_reuseFailAlloc_703_, 10, v_snapshotTasks_688_);
v___x_697_ = v_reuseFailAlloc_703_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_698_ = lean_st_ref_set(v___y_667_, v___x_697_);
v___x_699_ = lean_box(0);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_699_);
v___x_701_ = v___x_673_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_669_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_660_);
v_a_706_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_670_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_670_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
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
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v___y_665_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_660_);
v_a_714_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_668_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_668_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
v___jp_722_:
{
lean_object* v_fileName_728_; lean_object* v_fileMap_729_; uint8_t v_suppressElabErrors_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_749_; 
v_fileName_728_ = lean_ctor_get(v___y_656_, 0);
v_fileMap_729_ = lean_ctor_get(v___y_656_, 1);
v_suppressElabErrors_730_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*10);
v___x_731_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_653_);
v___x_732_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_731_, v___y_657_);
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_749_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_749_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_749_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_inc_ref_n(v_fileMap_729_, 2);
v___x_737_ = l_Lean_FileMap_toPosition(v_fileMap_729_, v___y_726_);
lean_dec(v___y_726_);
v___x_738_ = l_Lean_FileMap_toPosition(v_fileMap_729_, v___y_727_);
lean_dec(v___y_727_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_730_ == 0)
{
lean_del_object(v___x_735_);
v___y_660_ = v_a_733_;
v___y_661_ = v___y_724_;
v___y_662_ = v___x_740_;
v___y_663_ = v___x_739_;
v___y_664_ = v___y_725_;
v___y_665_ = v___x_737_;
v___y_666_ = v_fileName_728_;
v___y_667_ = v___y_657_;
goto v___jp_659_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___f_743_; uint8_t v___x_744_; 
v___x_741_ = lean_box(v___y_723_);
v___x_742_ = lean_box(v_suppressElabErrors_730_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_743_, 0, v___x_741_);
lean_closure_set(v___f_743_, 1, v___x_742_);
lean_inc(v_a_733_);
v___x_744_ = l_Lean_MessageData_hasTag(v___f_743_, v_a_733_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec_ref_known(v___x_739_, 1);
lean_dec_ref(v___x_737_);
lean_dec(v_a_733_);
v___x_745_ = lean_box(0);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_745_);
v___x_747_ = v___x_735_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_del_object(v___x_735_);
v___y_660_ = v_a_733_;
v___y_661_ = v___y_724_;
v___y_662_ = v___x_740_;
v___y_663_ = v___x_739_;
v___y_664_ = v___y_725_;
v___y_665_ = v___x_737_;
v___y_666_ = v_fileName_728_;
v___y_667_ = v___y_657_;
goto v___jp_659_;
}
}
}
}
v___jp_750_:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Syntax_getTailPos_x3f(v___y_753_, v___y_752_);
lean_dec(v___y_753_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_inc(v___y_755_);
v___y_723_ = v___y_751_;
v___y_724_ = v___y_752_;
v___y_725_ = v___y_754_;
v___y_726_ = v___y_755_;
v___y_727_ = v___y_755_;
goto v___jp_722_;
}
else
{
lean_object* v_val_757_; 
v_val_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v___x_756_, 1);
v___y_723_ = v___y_751_;
v___y_724_ = v___y_752_;
v___y_725_ = v___y_754_;
v___y_726_ = v___y_755_;
v___y_727_ = v_val_757_;
goto v___jp_722_;
}
}
v___jp_758_:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Elab_Command_getRef___redArg(v___y_656_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_ref_764_; lean_object* v___x_765_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v_ref_764_ = l_Lean_replaceRef(v_ref_652_, v_a_763_);
lean_dec(v_a_763_);
v___x_765_ = l_Lean_Syntax_getPos_x3f(v_ref_764_, v___y_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___y_751_ = v___y_759_;
v___y_752_ = v___y_760_;
v___y_753_ = v_ref_764_;
v___y_754_ = v___y_761_;
v___y_755_ = v___x_766_;
goto v___jp_750_;
}
else
{
lean_object* v_val_767_; 
v_val_767_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v___x_765_, 1);
v___y_751_ = v___y_759_;
v___y_752_ = v___y_760_;
v___y_753_ = v_ref_764_;
v___y_754_ = v___y_761_;
v___y_755_ = v_val_767_;
goto v___jp_750_;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_msgData_653_);
v_a_768_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_762_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_762_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
v___jp_777_:
{
if (v___y_780_ == 0)
{
v___y_759_ = v___y_778_;
v___y_760_ = v___y_779_;
v___y_761_ = v_severity_654_;
goto v___jp_758_;
}
else
{
v___y_759_ = v___y_778_;
v___y_760_ = v___y_779_;
v___y_761_ = v___x_776_;
goto v___jp_758_;
}
}
v___jp_781_:
{
if (v___y_782_ == 0)
{
lean_object* v___x_783_; lean_object* v_scopes_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_opts_787_; uint8_t v___x_788_; uint8_t v___x_789_; 
v___x_783_ = lean_st_ref_get(v___y_657_);
v_scopes_784_ = lean_ctor_get(v___x_783_, 2);
lean_inc(v_scopes_784_);
lean_dec(v___x_783_);
v___x_785_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_786_ = l_List_head_x21___redArg(v___x_785_, v_scopes_784_);
lean_dec(v_scopes_784_);
v_opts_787_ = lean_ctor_get(v___x_786_, 1);
lean_inc_ref(v_opts_787_);
lean_dec(v___x_786_);
v___x_788_ = 1;
v___x_789_ = l_Lean_instBEqMessageSeverity_beq(v_severity_654_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec_ref(v_opts_787_);
v___y_778_ = v___y_782_;
v___y_779_ = v___y_782_;
v___y_780_ = v___x_789_;
goto v___jp_777_;
}
else
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = l_Lean_warningAsError;
v___x_791_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_787_, v___x_790_);
lean_dec_ref(v_opts_787_);
v___y_778_ = v___y_782_;
v___y_779_ = v___y_782_;
v___y_780_ = v___x_791_;
goto v___jp_777_;
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_msgData_653_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_796_, lean_object* v_msgData_797_, lean_object* v_severity_798_, lean_object* v_isSilent_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v_severity_boxed_803_; uint8_t v_isSilent_boxed_804_; lean_object* v_res_805_; 
v_severity_boxed_803_ = lean_unbox(v_severity_798_);
v_isSilent_boxed_804_ = lean_unbox(v_isSilent_799_);
v_res_805_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_796_, v_msgData_797_, v_severity_boxed_803_, v_isSilent_boxed_804_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v_ref_796_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_806_, uint8_t v_severity_807_, uint8_t v_isSilent_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Elab_Command_getRef___redArg(v___y_809_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_813_, v_msgData_806_, v_severity_807_, v_isSilent_808_, v___y_809_, v___y_810_);
lean_dec(v_a_813_);
return v___x_814_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_msgData_806_);
v_a_815_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_812_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_823_, lean_object* v_severity_824_, lean_object* v_isSilent_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v_severity_boxed_829_; uint8_t v_isSilent_boxed_830_; lean_object* v_res_831_; 
v_severity_boxed_829_ = lean_unbox(v_severity_824_);
v_isSilent_boxed_830_ = lean_unbox(v_isSilent_825_);
v_res_831_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_823_, v_severity_boxed_829_, v_isSilent_boxed_830_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = 2;
v___x_837_ = 0;
v___x_838_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_832_, v___x_836_, v___x_837_, v___y_833_, v___y_834_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_844_, lean_object* v_msgData_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
v___x_849_ = 2;
v___x_850_ = 0;
v___x_851_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_844_, v_msgData_845_, v___x_849_, v___x_850_, v___y_846_, v___y_847_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_852_, lean_object* v_msgData_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_852_, v_msgData_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v_ref_852_);
return v_res_857_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
if (lean_obj_tag(v_ex_861_) == 0)
{
lean_object* v_ref_865_; lean_object* v_msg_866_; lean_object* v___x_867_; 
v_ref_865_ = lean_ctor_get(v_ex_861_, 0);
lean_inc(v_ref_865_);
v_msg_866_ = lean_ctor_get(v_ex_861_, 1);
lean_inc_ref(v_msg_866_);
lean_dec_ref_known(v_ex_861_, 2);
v___x_867_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_865_, v_msg_866_, v___y_862_, v___y_863_);
lean_dec(v_ref_865_);
return v___x_867_;
}
else
{
lean_object* v_id_868_; uint8_t v___y_870_; uint8_t v___x_892_; 
v_id_868_ = lean_ctor_get(v_ex_861_, 0);
lean_inc(v_id_868_);
v___x_892_ = l_Lean_Elab_isAbortExceptionId(v_id_868_);
if (v___x_892_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = l_Lean_Exception_isInterrupt(v_ex_861_);
lean_dec_ref_known(v_ex_861_, 2);
v___y_870_ = v___x_893_;
goto v___jp_869_;
}
else
{
lean_dec_ref_known(v_ex_861_, 2);
v___y_870_ = v___x_892_;
goto v___jp_869_;
}
v___jp_869_:
{
if (v___y_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_InternalExceptionId_getName(v_id_868_);
lean_dec(v_id_868_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_874_ = l_Lean_MessageData_ofName(v_a_872_);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_875_, v___y_862_, v___y_863_);
return v___x_876_;
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_889_; 
v_a_877_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_889_ == 0)
{
v___x_879_ = v___x_871_;
v_isShared_880_ = v_isSharedCheck_889_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_871_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_889_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_ref_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v_ref_881_ = lean_ctor_get(v___y_862_, 7);
v___x_882_ = lean_io_error_to_string(v_a_877_);
v___x_883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
v___x_884_ = l_Lean_MessageData_ofFormat(v___x_883_);
lean_inc(v_ref_881_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_ref_881_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_885_);
v___x_887_ = v___x_879_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_id_868_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
v___x_903_ = lean_apply_3(v_x_899_, v___y_900_, v___y_901_, lean_box(0));
if (lean_obj_tag(v___x_903_) == 0)
{
return v___x_903_;
}
else
{
lean_object* v_a_904_; uint8_t v___x_905_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
v___x_905_ = l_Lean_Exception_isInterrupt(v_a_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref_known(v___x_903_, 1);
v___x_906_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_904_, v___y_900_, v___y_901_);
return v___x_906_;
}
else
{
lean_dec(v_a_904_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_912_, lean_object* v___x_913_, lean_object* v_val_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_a_918_; lean_object* v___x_920_; 
v___x_920_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_912_, v___x_913_, v_val_914_);
if (lean_obj_tag(v___x_920_) == 0)
{
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v_a_918_ = v_a_921_;
goto v___jp_917_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_920_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; 
lean_dec_ref_known(v___x_920_, 1);
v___x_930_ = lean_box(0);
v_a_918_ = v___x_930_;
goto v___jp_917_;
}
v___jp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v_a_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_931_, lean_object* v___x_932_, lean_object* v_val_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_931_, v___x_932_, v_val_933_, v___y_934_);
lean_dec_ref(v___y_934_);
lean_dec(v_val_933_);
lean_dec_ref(v___x_932_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_937_, lean_object* v_x_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_get_set_stderr(v_h_937_);
lean_inc_ref(v___y_939_);
v___x_942_ = lean_apply_2(v_x_938_, v___y_939_, lean_box(0));
v___x_943_ = lean_get_set_stderr(v___x_941_);
lean_dec_ref(v___x_943_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_944_, lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_944_, v_x_945_, v___y_946_);
lean_dec_ref(v___y_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_949_, lean_object* v_h_950_, lean_object* v_x_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_950_, v_x_951_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_955_, lean_object* v_h_956_, lean_object* v_x_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_955_, v_h_956_, v_x_957_, v___y_958_);
lean_dec_ref(v___y_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_961_, lean_object* v_x_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_get_set_stdin(v_h_961_);
lean_inc_ref(v___y_963_);
v___x_966_ = lean_apply_2(v_x_962_, v___y_963_, lean_box(0));
v___x_967_ = lean_get_set_stdin(v___x_965_);
lean_dec_ref(v___x_967_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_968_, v_x_969_, v___y_970_);
lean_dec_ref(v___y_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_975_ = lean_panic_fn_borrowed(v___x_974_, v_msg_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_976_, lean_object* v_x_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_get_set_stdout(v_h_976_);
lean_inc_ref(v___y_978_);
v___x_981_ = lean_apply_2(v_x_977_, v___y_978_, lean_box(0));
v___x_982_ = lean_get_set_stdout(v___x_980_);
lean_dec_ref(v___x_982_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_983_, v_x_984_, v___y_985_);
lean_dec_ref(v___y_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_988_, lean_object* v_h_989_, lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_989_, v_x_990_, v___y_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_994_, lean_object* v_h_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_994_, v_h_995_, v_x_996_, v___y_997_);
lean_dec_ref(v___y_997_);
return v_res_999_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = l_ByteArray_empty;
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1006_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1007_ = lean_unsigned_to_nat(46u);
v___x_1008_ = lean_unsigned_to_nat(193u);
v___x_1009_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1010_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1011_ = l_mkPanicMessageWithDecl(v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_, v___x_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1012_, uint8_t v_isolateStderr_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___y_1026_; 
v___x_1020_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1021_ = lean_st_mk_ref(v___x_1020_);
v___x_1022_ = lean_st_mk_ref(v___x_1020_);
v___x_1023_ = l_IO_FS_Stream_ofBuffer(v___x_1021_);
lean_inc(v___x_1022_);
v___x_1024_ = l_IO_FS_Stream_ofBuffer(v___x_1022_);
if (v_isolateStderr_1013_ == 0)
{
v___y_1026_ = v_x_1012_;
goto v___jp_1025_;
}
else
{
lean_object* v___x_1035_; 
lean_inc_ref(v___x_1024_);
v___x_1035_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1035_, 0, lean_box(0));
lean_closure_set(v___x_1035_, 1, v___x_1024_);
lean_closure_set(v___x_1035_, 2, v_x_1012_);
v___y_1026_ = v___x_1035_;
goto v___jp_1025_;
}
v___jp_1016_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_1018_);
lean_ctor_set(v___x_1019_, 1, v___y_1017_);
return v___x_1019_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_data_1030_; uint8_t v___x_1031_; 
v___x_1027_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1027_, 0, lean_box(0));
lean_closure_set(v___x_1027_, 1, v___x_1024_);
lean_closure_set(v___x_1027_, 2, v___y_1026_);
v___x_1028_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1023_, v___x_1027_, v___y_1014_);
v___x_1029_ = lean_st_ref_get(v___x_1022_);
lean_dec(v___x_1022_);
v_data_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_data_1030_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_string_validate_utf8(v_data_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_data_1030_);
v___x_1032_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1033_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1032_);
v___y_1017_ = v___x_1028_;
v___y_1018_ = v___x_1033_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_string_from_utf8_unchecked(v_data_1030_);
v___y_1017_ = v___x_1028_;
v___y_1018_ = v___x_1034_;
goto v___jp_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1036_, lean_object* v_isolateStderr_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_isolateStderr_boxed_1040_; lean_object* v_res_1041_; 
v_isolateStderr_boxed_1040_ = lean_unbox(v_isolateStderr_1037_);
v_res_1041_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1036_, v_isolateStderr_boxed_1040_, v___y_1038_);
lean_dec_ref(v___y_1038_);
return v_res_1041_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = 1;
v___x_1051_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1052_ = l_Lean_Name_toString(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1053_, lean_object* v_cmds_1054_, lean_object* v_cmdState_1055_, lean_object* v_beginPos_1056_, lean_object* v_snap_1057_, lean_object* v_cancelTk_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_env_1061_; lean_object* v_scopes_1062_; lean_object* v_usedQuotCtxts_1063_; lean_object* v_nextMacroScope_1064_; lean_object* v_maxRecDepth_1065_; lean_object* v_ngen_1066_; lean_object* v_auxDeclNGen_1067_; lean_object* v_infoState_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1144_; 
v_env_1061_ = lean_ctor_get(v_cmdState_1055_, 0);
v_scopes_1062_ = lean_ctor_get(v_cmdState_1055_, 2);
v_usedQuotCtxts_1063_ = lean_ctor_get(v_cmdState_1055_, 3);
v_nextMacroScope_1064_ = lean_ctor_get(v_cmdState_1055_, 4);
v_maxRecDepth_1065_ = lean_ctor_get(v_cmdState_1055_, 5);
v_ngen_1066_ = lean_ctor_get(v_cmdState_1055_, 6);
v_auxDeclNGen_1067_ = lean_ctor_get(v_cmdState_1055_, 7);
v_infoState_1068_ = lean_ctor_get(v_cmdState_1055_, 8);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_cmdState_1055_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1145_ = lean_ctor_get(v_cmdState_1055_, 10);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_cmdState_1055_, 9);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_cmdState_1055_, 1);
lean_dec(v_unused_1147_);
v___x_1070_ = v_cmdState_1055_;
v_isShared_1071_ = v_isSharedCheck_1144_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_infoState_1068_);
lean_inc(v_auxDeclNGen_1067_);
lean_inc(v_ngen_1066_);
lean_inc(v_maxRecDepth_1065_);
lean_inc(v_nextMacroScope_1064_);
lean_inc(v_usedQuotCtxts_1063_);
lean_inc(v_scopes_1062_);
lean_inc(v_env_1061_);
lean_dec(v_cmdState_1055_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1144_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1072_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1073_ = l_List_head_x21___redArg(v___x_1072_, v_scopes_1062_);
v___x_1074_ = l_Lean_MessageLog_empty;
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1077_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 10, v___x_1077_);
lean_ctor_set(v___x_1070_, 9, v___x_1076_);
lean_ctor_set(v___x_1070_, 1, v___x_1074_);
v___x_1079_ = v___x_1070_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_env_1061_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_scopes_1062_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_usedQuotCtxts_1063_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_nextMacroScope_1064_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_maxRecDepth_1065_);
lean_ctor_set(v_reuseFailAlloc_1143_, 6, v_ngen_1066_);
lean_ctor_set(v_reuseFailAlloc_1143_, 7, v_auxDeclNGen_1067_);
lean_ctor_set(v_reuseFailAlloc_1143_, 8, v_infoState_1068_);
lean_ctor_set(v_reuseFailAlloc_1143_, 9, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1143_, 10, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v_toProcessingContext_1081_; lean_object* v_fileName_1082_; lean_object* v_fileMap_1083_; lean_object* v_opts_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; lean_object* v___y_1094_; uint8_t v___y_1095_; lean_object* v_messages_1096_; lean_object* v___y_1122_; 
v___x_1080_ = lean_st_mk_ref(v___x_1079_);
v_toProcessingContext_1081_ = lean_ctor_get(v_a_1059_, 0);
v_fileName_1082_ = lean_ctor_get(v_toProcessingContext_1081_, 1);
v_fileMap_1083_ = lean_ctor_get(v_toProcessingContext_1081_, 2);
v_opts_1084_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_opts_1084_);
lean_dec(v___x_1073_);
v___f_1085_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1085_, 0, v_stx_1053_);
lean_closure_set(v___f_1085_, 1, v_cmds_1054_);
v___x_1086_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Lean_firstFrontendMacroScope;
v___x_1090_ = lean_box(0);
v___x_1091_ = l_Lean_internal_cmdlineSnapshots;
v___x_1092_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1084_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1142_; 
lean_inc_ref(v_snap_1057_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_snap_1057_);
v___y_1122_ = v___x_1142_;
goto v___jp_1121_;
}
else
{
v___y_1122_ = v___x_1088_;
goto v___jp_1121_;
}
v___jp_1093_:
{
lean_object* v_new_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v_scopes_1104_; lean_object* v_usedQuotCtxts_1105_; lean_object* v_nextMacroScope_1106_; lean_object* v_maxRecDepth_1107_; lean_object* v_ngen_1108_; lean_object* v_auxDeclNGen_1109_; lean_object* v_infoState_1110_; lean_object* v_traceState_1111_; lean_object* v_snapshotTasks_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_new_1097_ = lean_ctor_get(v_snap_1057_, 1);
lean_inc(v_new_1097_);
lean_dec_ref(v_snap_1057_);
v___x_1098_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1099_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1100_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set(v___x_1100_, 2, v___x_1088_);
lean_ctor_set(v___x_1100_, 3, v___x_1076_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*4, v___y_1095_);
v___x_1101_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1086_, v___x_1100_);
v___x_1102_ = lean_io_promise_resolve(v___x_1101_, v_new_1097_);
lean_dec(v_new_1097_);
v_env_1103_ = lean_ctor_get(v___y_1094_, 0);
v_scopes_1104_ = lean_ctor_get(v___y_1094_, 2);
v_usedQuotCtxts_1105_ = lean_ctor_get(v___y_1094_, 3);
v_nextMacroScope_1106_ = lean_ctor_get(v___y_1094_, 4);
v_maxRecDepth_1107_ = lean_ctor_get(v___y_1094_, 5);
v_ngen_1108_ = lean_ctor_get(v___y_1094_, 6);
v_auxDeclNGen_1109_ = lean_ctor_get(v___y_1094_, 7);
v_infoState_1110_ = lean_ctor_get(v___y_1094_, 8);
v_traceState_1111_ = lean_ctor_get(v___y_1094_, 9);
v_snapshotTasks_1112_ = lean_ctor_get(v___y_1094_, 10);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___y_1094_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v___y_1094_, 1);
lean_dec(v_unused_1120_);
v___x_1114_ = v___y_1094_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snapshotTasks_1112_);
lean_inc(v_traceState_1111_);
lean_inc(v_infoState_1110_);
lean_inc(v_auxDeclNGen_1109_);
lean_inc(v_ngen_1108_);
lean_inc(v_maxRecDepth_1107_);
lean_inc(v_nextMacroScope_1106_);
lean_inc(v_usedQuotCtxts_1105_);
lean_inc(v_scopes_1104_);
lean_inc(v_env_1103_);
lean_dec(v___y_1094_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v_messages_1096_);
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_env_1103_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_messages_1096_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_scopes_1104_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_usedQuotCtxts_1105_);
lean_ctor_set(v_reuseFailAlloc_1118_, 4, v_nextMacroScope_1106_);
lean_ctor_set(v_reuseFailAlloc_1118_, 5, v_maxRecDepth_1107_);
lean_ctor_set(v_reuseFailAlloc_1118_, 6, v_ngen_1108_);
lean_ctor_set(v_reuseFailAlloc_1118_, 7, v_auxDeclNGen_1109_);
lean_ctor_set(v_reuseFailAlloc_1118_, 8, v_infoState_1110_);
lean_ctor_set(v_reuseFailAlloc_1118_, 9, v_traceState_1111_);
lean_ctor_set(v_reuseFailAlloc_1118_, 10, v_snapshotTasks_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
v___jp_1121_:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v_fst_1130_; lean_object* v___x_1131_; lean_object* v_messages_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_cancelTk_1058_);
v___x_1124_ = 0;
lean_inc(v_beginPos_1056_);
lean_inc_ref(v_fileMap_1083_);
lean_inc_ref(v_fileName_1082_);
v___x_1125_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1125_, 0, v_fileName_1082_);
lean_ctor_set(v___x_1125_, 1, v_fileMap_1083_);
lean_ctor_set(v___x_1125_, 2, v___x_1075_);
lean_ctor_set(v___x_1125_, 3, v_beginPos_1056_);
lean_ctor_set(v___x_1125_, 4, v___x_1087_);
lean_ctor_set(v___x_1125_, 5, v___x_1088_);
lean_ctor_set(v___x_1125_, 6, v___x_1089_);
lean_ctor_set(v___x_1125_, 7, v___x_1090_);
lean_ctor_set(v___x_1125_, 8, v___y_1122_);
lean_ctor_set(v___x_1125_, 9, v___x_1123_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*10, v___x_1124_);
lean_inc(v___x_1080_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1126_, 0, v___f_1085_);
lean_closure_set(v___f_1126_, 1, v___x_1125_);
lean_closure_set(v___f_1126_, 2, v___x_1080_);
v___x_1127_ = l_Lean_Core_stderrAsMessages;
v___x_1128_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1084_, v___x_1127_);
lean_dec_ref(v_opts_1084_);
v___x_1129_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1126_, v___x_1128_, v_a_1059_);
v_fst_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_fst_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_st_ref_get(v___x_1080_);
lean_dec(v___x_1080_);
v_messages_1132_ = lean_ctor_get(v___x_1131_, 1);
lean_inc_ref(v_messages_1132_);
v___x_1133_ = lean_string_utf8_byte_size(v_fst_1130_);
v___x_1134_ = lean_nat_dec_eq(v___x_1133_, v___x_1075_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_inc_ref(v_fileMap_1083_);
v___x_1135_ = l_Lean_FileMap_toPosition(v_fileMap_1083_, v_beginPos_1056_);
lean_dec(v_beginPos_1056_);
v___x_1136_ = 0;
v___x_1137_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_fst_1130_);
v___x_1139_ = l_Lean_MessageData_ofFormat(v___x_1138_);
lean_inc_ref(v_fileName_1082_);
v___x_1140_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1140_, 0, v_fileName_1082_);
lean_ctor_set(v___x_1140_, 1, v___x_1135_);
lean_ctor_set(v___x_1140_, 2, v___x_1088_);
lean_ctor_set(v___x_1140_, 3, v___x_1137_);
lean_ctor_set(v___x_1140_, 4, v___x_1139_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*5, v___x_1124_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*5 + 1, v___x_1136_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*5 + 2, v___x_1124_);
v___x_1141_ = l_Lean_MessageLog_add(v___x_1140_, v_messages_1132_);
v___y_1094_ = v___x_1131_;
v___y_1095_ = v___x_1124_;
v_messages_1096_ = v___x_1141_;
goto v___jp_1093_;
}
else
{
lean_dec(v_fst_1130_);
lean_dec(v_beginPos_1056_);
v___y_1094_ = v___x_1131_;
v___y_1095_ = v___x_1124_;
v_messages_1096_ = v_messages_1132_;
goto v___jp_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1148_, lean_object* v_cmds_1149_, lean_object* v_cmdState_1150_, lean_object* v_beginPos_1151_, lean_object* v_snap_1152_, lean_object* v_cancelTk_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1148_, v_cmds_1149_, v_cmdState_1150_, v_beginPos_1151_, v_snap_1152_, v_cancelTk_1153_, v_a_1154_);
lean_dec_ref(v_a_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1157_, lean_object* v_h_1158_, lean_object* v_x_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1158_, v_x_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_h_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1163_, v_h_1164_, v_x_1165_, v___y_1166_);
lean_dec_ref(v___y_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1169_, lean_object* v_x_1170_, uint8_t v_isolateStderr_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1170_, v_isolateStderr_1171_, v___y_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_x_1176_, lean_object* v_isolateStderr_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v_isolateStderr_boxed_1180_; lean_object* v_res_1181_; 
v_isolateStderr_boxed_1180_ = lean_unbox(v_isolateStderr_1177_);
v_res_1181_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1175_, v_x_1176_, v_isolateStderr_boxed_1180_, v___y_1178_);
lean_dec_ref(v___y_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1182_, v___y_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1192_){
_start:
{
lean_object* v_toSnapshotTreeM_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_toSnapshotTreeM_1193_ = lean_ctor_get(v_a_1192_, 1);
lean_inc_ref(v_toSnapshotTreeM_1193_);
lean_dec_ref(v_a_1192_);
v___x_1194_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1195_ = lean_apply_1(v_toSnapshotTreeM_1193_, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1196_){
_start:
{
lean_object* v_toSnapshot_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1207_; 
v_toSnapshot_1197_ = lean_ctor_get(v_a_1196_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1196_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_a_1196_, 1);
lean_dec(v_unused_1208_);
v___x_1199_ = v_a_1196_;
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_toSnapshot_1197_);
lean_dec(v_a_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1201_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1202_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1197_, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1203_);
lean_ctor_set(v___x_1199_, 0, v___x_1202_);
v___x_1205_ = v___x_1199_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1210_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1211_ = l_Lean_Language_Snapshot_transform(v_a_1209_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1214_, lean_object* v_opt_1215_){
_start:
{
lean_object* v_name_1216_; lean_object* v_defValue_1217_; lean_object* v_map_1218_; lean_object* v___x_1219_; 
v_name_1216_ = lean_ctor_get(v_opt_1215_, 0);
v_defValue_1217_ = lean_ctor_get(v_opt_1215_, 1);
v_map_1218_ = lean_ctor_get(v_opts_1214_, 0);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1218_, v_name_1216_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_inc(v_defValue_1217_);
return v_defValue_1217_;
}
else
{
lean_object* v_val_1220_; 
v_val_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_val_1220_);
lean_dec_ref_known(v___x_1219_, 1);
if (lean_obj_tag(v_val_1220_) == 3)
{
lean_object* v_v_1221_; 
v_v_1221_ = lean_ctor_get(v_val_1220_, 0);
lean_inc(v_v_1221_);
lean_dec_ref_known(v_val_1220_, 1);
return v_v_1221_;
}
else
{
lean_dec(v_val_1220_);
lean_inc(v_defValue_1217_);
return v_defValue_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1222_, lean_object* v_opt_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1222_, v_opt_1223_);
lean_dec_ref(v_opt_1223_);
lean_dec_ref(v_opts_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1227_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1225_, v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1234_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1235_ = l_Lean_Name_append(v___x_1234_, v___x_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1236_, lean_object* v___x_1237_, uint8_t v_val_1238_, lean_object* v_val_1239_, lean_object* v_val_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, uint8_t v___x_1243_, lean_object* v_a_1244_, lean_object* v_pos_1245_, lean_object* v_infoSt_1246_){
_start:
{
lean_object* v___y_1249_; lean_object* v_msgLog_1250_; lean_object* v___y_1256_; lean_object* v_trees_1288_; lean_object* v_size_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_trees_1288_ = lean_ctor_get(v_infoSt_1246_, 2);
v_size_1289_ = lean_ctor_get(v_trees_1288_, 2);
v___x_1290_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1291_ = lean_nat_dec_lt(v___x_1242_, v_size_1289_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = l_outOfBounds___redArg(v___x_1290_);
v___y_1256_ = v___x_1292_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1290_, v_trees_1288_, v___x_1242_);
v___y_1256_ = v___x_1293_;
goto v___jp_1255_;
}
v___jp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1250_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___y_1249_);
v___x_1253_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1253_, 0, v___x_1236_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_ctor_set(v___x_1253_, 2, v___x_1252_);
lean_ctor_set(v___x_1253_, 3, v___x_1237_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*4, v_val_1238_);
v___x_1254_ = lean_io_promise_resolve(v___x_1253_, v_val_1239_);
return v___x_1254_;
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v_scopes_1259_; lean_object* v___x_1260_; lean_object* v_opts_1261_; uint8_t v_hasTrace_1262_; lean_object* v___x_1263_; 
v___x_1257_ = l_Lean_inheritedTraceOptions;
v___x_1258_ = lean_st_ref_get(v___x_1257_);
v_scopes_1259_ = lean_ctor_get(v_val_1240_, 2);
v___x_1260_ = l_List_head_x21___redArg(v___x_1241_, v_scopes_1259_);
v_opts_1261_ = lean_ctor_get(v___x_1260_, 1);
lean_inc_ref(v_opts_1261_);
lean_dec(v___x_1260_);
v_hasTrace_1262_ = lean_ctor_get_uint8(v_opts_1261_, sizeof(void*)*1);
v___x_1263_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1262_ == 0)
{
lean_dec_ref(v_opts_1261_);
lean_dec(v___x_1258_);
lean_dec(v___x_1242_);
v___y_1249_ = v___y_1256_;
v_msgLog_1250_ = v___x_1263_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1264_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1265_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1266_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1267_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1258_, v_opts_1261_, v___x_1266_);
lean_dec_ref(v_opts_1261_);
lean_dec(v___x_1258_);
if (v___x_1267_ == 0)
{
lean_dec(v___x_1242_);
v___y_1249_ = v___y_1256_;
v_msgLog_1250_ = v___x_1263_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_box(0);
lean_inc_ref(v___y_1256_);
v___x_1269_ = l_Lean_Elab_InfoTree_format(v___y_1256_, v___x_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; double v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_toProcessingContext_1274_; lean_object* v_fileName_1275_; lean_object* v_fileMap_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_float_of_nat(v___x_1242_);
v___x_1272_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1273_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1273_, 0, v___x_1264_);
lean_ctor_set(v___x_1273_, 1, v___x_1268_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
lean_ctor_set_float(v___x_1273_, sizeof(void*)*3, v___x_1271_);
lean_ctor_set_float(v___x_1273_, sizeof(void*)*3 + 8, v___x_1271_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*3 + 16, v___x_1243_);
v_toProcessingContext_1274_ = lean_ctor_get(v_a_1244_, 0);
v_fileName_1275_ = lean_ctor_get(v_toProcessingContext_1274_, 1);
v_fileMap_1276_ = lean_ctor_get(v_toProcessingContext_1274_, 2);
v___x_1277_ = l_Lean_MessageData_nil;
v___x_1278_ = l_Lean_MessageData_ofFormat(v_a_1270_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1279_);
v___x_1281_ = lean_array_push(v___x_1280_, v___x_1278_);
v___x_1282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1273_);
lean_ctor_set(v___x_1282_, 1, v___x_1277_);
lean_ctor_set(v___x_1282_, 2, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1265_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
lean_inc_ref(v_fileMap_1276_);
v___x_1284_ = l_Lean_FileMap_toPosition(v_fileMap_1276_, v_pos_1245_);
v___x_1285_ = 0;
lean_inc_ref(v_fileName_1275_);
v___x_1286_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1286_, 0, v_fileName_1275_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
lean_ctor_set(v___x_1286_, 2, v___x_1268_);
lean_ctor_set(v___x_1286_, 3, v___x_1272_);
lean_ctor_set(v___x_1286_, 4, v___x_1283_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*5, v_val_1238_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*5 + 1, v___x_1285_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*5 + 2, v_val_1238_);
v___x_1287_ = l_Lean_MessageLog_add(v___x_1286_, v___x_1263_);
v___y_1249_ = v___y_1256_;
v_msgLog_1250_ = v___x_1287_;
goto v___jp_1248_;
}
else
{
lean_dec_ref_known(v___x_1269_, 1);
lean_dec(v___x_1242_);
v___y_1249_ = v___y_1256_;
v_msgLog_1250_ = v___x_1263_;
goto v___jp_1248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v_val_1296_, lean_object* v_val_1297_, lean_object* v_val_1298_, lean_object* v___x_1299_, lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v_a_1302_, lean_object* v_pos_1303_, lean_object* v_infoSt_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v_val_44357__boxed_1306_; uint8_t v___x_44362__boxed_1307_; lean_object* v_res_1308_; 
v_val_44357__boxed_1306_ = lean_unbox(v_val_1296_);
v___x_44362__boxed_1307_ = lean_unbox(v___x_1301_);
v_res_1308_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1294_, v___x_1295_, v_val_44357__boxed_1306_, v_val_1297_, v_val_1298_, v___x_1299_, v___x_1300_, v___x_44362__boxed_1307_, v_a_1302_, v_pos_1303_, v_infoSt_1304_);
lean_dec_ref(v_infoSt_1304_);
lean_dec(v_pos_1303_);
lean_dec_ref(v_a_1302_);
lean_dec_ref(v___x_1299_);
lean_dec_ref(v_val_1298_);
lean_dec(v_val_1297_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, uint8_t v_val_1312_, lean_object* v_as_1313_, size_t v_sz_1314_, size_t v_i_1315_, lean_object* v_b_1316_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1315_, v_sz_1314_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v___x_1311_);
lean_dec_ref(v___x_1309_);
return v_b_1316_;
}
else
{
lean_object* v_snd_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1337_; 
v_snd_1319_ = lean_ctor_get(v_b_1316_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_b_1316_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_b_1316_, 0);
lean_dec(v_unused_1338_);
v___x_1321_ = v_b_1316_;
v_isShared_1322_ = v_isSharedCheck_1337_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snd_1319_);
lean_dec(v_b_1316_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1337_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_a_1323_; lean_object* v_msg_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v_a_1323_ = lean_array_uget_borrowed(v_as_1313_, v_i_1315_);
v_msg_1324_ = lean_ctor_get(v_a_1323_, 1);
v___x_1325_ = lean_box(0);
lean_inc_ref(v___x_1309_);
v___x_1326_ = l_Lean_FileMap_toPosition(v___x_1309_, v___x_1310_);
v___x_1327_ = 0;
v___x_1328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1324_);
lean_inc_ref(v___x_1311_);
v___x_1329_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1329_, 0, v___x_1311_);
lean_ctor_set(v___x_1329_, 1, v___x_1326_);
lean_ctor_set(v___x_1329_, 2, v___x_1325_);
lean_ctor_set(v___x_1329_, 3, v___x_1328_);
lean_ctor_set(v___x_1329_, 4, v_msg_1324_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*5, v_val_1312_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*5 + 1, v___x_1327_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*5 + 2, v_val_1312_);
v___x_1330_ = l_Lean_MessageLog_add(v___x_1329_, v_snd_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1330_);
lean_ctor_set(v___x_1321_, 0, v___x_1325_);
v___x_1332_ = v___x_1321_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
size_t v___x_1333_; size_t v___x_1334_; 
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_add(v_i_1315_, v___x_1333_);
v_i_1315_ = v___x_1334_;
v_b_1316_ = v___x_1332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v_val_1342_, lean_object* v_as_1343_, lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_val_44469__boxed_1348_; size_t v_sz_boxed_1349_; size_t v_i_boxed_1350_; lean_object* v_res_1351_; 
v_val_44469__boxed_1348_ = lean_unbox(v_val_1342_);
v_sz_boxed_1349_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1350_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1339_, v___x_1340_, v___x_1341_, v_val_44469__boxed_1348_, v_as_1343_, v_sz_boxed_1349_, v_i_boxed_1350_, v_b_1346_);
lean_dec_ref(v_as_1343_);
lean_dec(v___x_1340_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1352_, lean_object* v___x_1353_, lean_object* v___x_1354_, uint8_t v_val_1355_, lean_object* v_as_1356_, size_t v_sz_1357_, size_t v_i_1358_, lean_object* v_b_1359_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_usize_dec_lt(v_i_1358_, v_sz_1357_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1352_);
return v_b_1359_;
}
else
{
lean_object* v_snd_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1380_; 
v_snd_1362_ = lean_ctor_get(v_b_1359_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_b_1359_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v_b_1359_, 0);
lean_dec(v_unused_1381_);
v___x_1364_ = v_b_1359_;
v_isShared_1365_ = v_isSharedCheck_1380_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snd_1362_);
lean_dec(v_b_1359_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1380_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_a_1366_; lean_object* v_msg_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v_a_1366_ = lean_array_uget_borrowed(v_as_1356_, v_i_1358_);
v_msg_1367_ = lean_ctor_get(v_a_1366_, 1);
v___x_1368_ = lean_box(0);
lean_inc_ref(v___x_1352_);
v___x_1369_ = l_Lean_FileMap_toPosition(v___x_1352_, v___x_1353_);
v___x_1370_ = 0;
v___x_1371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1367_);
lean_inc_ref(v___x_1354_);
v___x_1372_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1372_, 0, v___x_1354_);
lean_ctor_set(v___x_1372_, 1, v___x_1369_);
lean_ctor_set(v___x_1372_, 2, v___x_1368_);
lean_ctor_set(v___x_1372_, 3, v___x_1371_);
lean_ctor_set(v___x_1372_, 4, v_msg_1367_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*5, v_val_1355_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*5 + 1, v___x_1370_);
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*5 + 2, v_val_1355_);
v___x_1373_ = l_Lean_MessageLog_add(v___x_1372_, v_snd_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1373_);
lean_ctor_set(v___x_1364_, 0, v___x_1368_);
v___x_1375_ = v___x_1364_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1358_, v___x_1376_);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1352_, v___x_1353_, v___x_1354_, v_val_1355_, v_as_1356_, v_sz_1357_, v___x_1377_, v___x_1375_);
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1382_, lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v_val_1385_, lean_object* v_as_1386_, lean_object* v_sz_1387_, lean_object* v_i_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_val_44521__boxed_1391_; size_t v_sz_boxed_1392_; size_t v_i_boxed_1393_; lean_object* v_res_1394_; 
v_val_44521__boxed_1391_ = lean_unbox(v_val_1385_);
v_sz_boxed_1392_ = lean_unbox_usize(v_sz_1387_);
lean_dec(v_sz_1387_);
v_i_boxed_1393_ = lean_unbox_usize(v_i_1388_);
lean_dec(v_i_1388_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1382_, v___x_1383_, v___x_1384_, v_val_44521__boxed_1391_, v_as_1386_, v_sz_boxed_1392_, v_i_boxed_1393_, v_b_1389_);
lean_dec_ref(v_as_1386_);
lean_dec(v___x_1383_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, uint8_t v_val_1399_, lean_object* v_n_1400_, lean_object* v_b_1401_){
_start:
{
if (lean_obj_tag(v_n_1400_) == 0)
{
lean_object* v_cs_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; size_t v_sz_1406_; size_t v___x_1407_; lean_object* v___x_1408_; lean_object* v_fst_1409_; 
v_cs_1403_ = lean_ctor_get(v_n_1400_, 0);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v_b_1401_);
v_sz_1406_ = lean_array_size(v_cs_1403_);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1395_, v___x_1396_, v___x_1397_, v___x_1398_, v_val_1399_, v_cs_1403_, v_sz_1406_, v___x_1407_, v___x_1405_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_fst_1409_);
if (lean_obj_tag(v_fst_1409_) == 0)
{
lean_object* v_snd_1410_; lean_object* v___x_1411_; 
v_snd_1410_ = lean_ctor_get(v___x_1408_, 1);
lean_inc(v_snd_1410_);
lean_dec_ref(v___x_1408_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_snd_1410_);
return v___x_1411_;
}
else
{
lean_object* v_val_1412_; 
lean_dec_ref(v___x_1408_);
v_val_1412_ = lean_ctor_get(v_fst_1409_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v_fst_1409_, 1);
return v_val_1412_;
}
}
else
{
lean_object* v_vs_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; lean_object* v_fst_1419_; 
v_vs_1413_ = lean_ctor_get(v_n_1400_, 0);
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v_b_1401_);
v_sz_1416_ = lean_array_size(v_vs_1413_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1396_, v___x_1397_, v___x_1398_, v_val_1399_, v_vs_1413_, v_sz_1416_, v___x_1417_, v___x_1415_);
v_fst_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_fst_1419_);
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
lean_dec_ref(v___x_1418_);
v_val_1422_ = lean_ctor_get(v_fst_1419_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v_fst_1419_, 1);
return v_val_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, uint8_t v_val_1427_, lean_object* v_as_1428_, size_t v_sz_1429_, size_t v_i_1430_, lean_object* v_b_1431_){
_start:
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_usize_dec_lt(v_i_1430_, v_sz_1429_);
if (v___x_1433_ == 0)
{
lean_dec_ref(v___x_1426_);
lean_dec_ref(v___x_1424_);
return v_b_1431_;
}
else
{
lean_object* v_snd_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1452_; 
v_snd_1434_ = lean_ctor_get(v_b_1431_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_b_1431_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_b_1431_, 0);
lean_dec(v_unused_1453_);
v___x_1436_ = v_b_1431_;
v_isShared_1437_ = v_isSharedCheck_1452_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_snd_1434_);
lean_dec(v_b_1431_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1452_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_array_uget_borrowed(v_as_1428_, v_i_1430_);
lean_inc(v_snd_1434_);
lean_inc_ref(v___x_1426_);
lean_inc_ref(v___x_1424_);
v___x_1439_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1423_, v___x_1424_, v___x_1425_, v___x_1426_, v_val_1427_, v_a_1438_, v_snd_1434_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_dec_ref(v___x_1426_);
lean_dec_ref(v___x_1424_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1440_);
v___x_1442_ = v___x_1436_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_snd_1434_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_dec(v_snd_1434_);
v_a_1444_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1445_ = lean_box(0);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_a_1444_);
lean_ctor_set(v___x_1436_, 0, v___x_1445_);
v___x_1447_ = v___x_1436_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_a_1444_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
size_t v___x_1448_; size_t v___x_1449_; 
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_add(v_i_1430_, v___x_1448_);
v_i_1430_ = v___x_1449_;
v_b_1431_ = v___x_1447_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1454_, lean_object* v___x_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, lean_object* v_val_1458_, lean_object* v_as_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v_val_44572__boxed_1464_; size_t v_sz_boxed_1465_; size_t v_i_boxed_1466_; lean_object* v_res_1467_; 
v_val_44572__boxed_1464_ = lean_unbox(v_val_1458_);
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1454_, v___x_1455_, v___x_1456_, v___x_1457_, v_val_44572__boxed_1464_, v_as_1459_, v_sz_boxed_1465_, v_i_boxed_1466_, v_b_1462_);
lean_dec_ref(v_as_1459_);
lean_dec(v___x_1456_);
lean_dec_ref(v_init_1454_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v_val_1472_, lean_object* v_n_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v_val_44588__boxed_1476_; lean_object* v_res_1477_; 
v_val_44588__boxed_1476_ = lean_unbox(v_val_1472_);
v_res_1477_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1468_, v___x_1469_, v___x_1470_, v___x_1471_, v_val_44588__boxed_1476_, v_n_1473_, v_b_1474_);
lean_dec_ref(v_n_1473_);
lean_dec(v___x_1470_);
lean_dec_ref(v_init_1468_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, uint8_t v_val_1481_, lean_object* v_as_1482_, size_t v_sz_1483_, size_t v_i_1484_, lean_object* v_b_1485_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_usize_dec_lt(v_i_1484_, v_sz_1483_);
if (v___x_1487_ == 0)
{
lean_dec_ref(v___x_1480_);
lean_dec_ref(v___x_1478_);
return v_b_1485_;
}
else
{
lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1506_; 
v_snd_1488_ = lean_ctor_get(v_b_1485_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_b_1485_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_b_1485_, 0);
lean_dec(v_unused_1507_);
v___x_1490_ = v_b_1485_;
v_isShared_1491_ = v_isSharedCheck_1506_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_dec(v_b_1485_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1506_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_a_1492_; lean_object* v_msg_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v_a_1492_ = lean_array_uget_borrowed(v_as_1482_, v_i_1484_);
v_msg_1493_ = lean_ctor_get(v_a_1492_, 1);
v___x_1494_ = lean_box(0);
lean_inc_ref(v___x_1478_);
v___x_1495_ = l_Lean_FileMap_toPosition(v___x_1478_, v___x_1479_);
v___x_1496_ = 0;
v___x_1497_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1493_);
lean_inc_ref(v___x_1480_);
v___x_1498_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1498_, 0, v___x_1480_);
lean_ctor_set(v___x_1498_, 1, v___x_1495_);
lean_ctor_set(v___x_1498_, 2, v___x_1494_);
lean_ctor_set(v___x_1498_, 3, v___x_1497_);
lean_ctor_set(v___x_1498_, 4, v_msg_1493_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5, v_val_1481_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5 + 1, v___x_1496_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5 + 2, v_val_1481_);
v___x_1499_ = l_Lean_MessageLog_add(v___x_1498_, v_snd_1488_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1499_);
lean_ctor_set(v___x_1490_, 0, v___x_1494_);
v___x_1501_ = v___x_1490_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
size_t v___x_1502_; size_t v___x_1503_; 
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = lean_usize_add(v_i_1484_, v___x_1502_);
v_i_1484_ = v___x_1503_;
v_b_1485_ = v___x_1501_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1508_, lean_object* v___x_1509_, lean_object* v___x_1510_, lean_object* v_val_1511_, lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_){
_start:
{
uint8_t v_val_44670__boxed_1517_; size_t v_sz_boxed_1518_; size_t v_i_boxed_1519_; lean_object* v_res_1520_; 
v_val_44670__boxed_1517_ = lean_unbox(v_val_1511_);
v_sz_boxed_1518_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1519_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1508_, v___x_1509_, v___x_1510_, v_val_44670__boxed_1517_, v_as_1512_, v_sz_boxed_1518_, v_i_boxed_1519_, v_b_1515_);
lean_dec_ref(v_as_1512_);
lean_dec(v___x_1509_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v___x_1523_, uint8_t v_val_1524_, lean_object* v_as_1525_, size_t v_sz_1526_, size_t v_i_1527_, lean_object* v_b_1528_){
_start:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_usize_dec_lt(v_i_1527_, v_sz_1526_);
if (v___x_1530_ == 0)
{
lean_dec_ref(v___x_1523_);
lean_dec_ref(v___x_1521_);
return v_b_1528_;
}
else
{
lean_object* v_snd_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1549_; 
v_snd_1531_ = lean_ctor_get(v_b_1528_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_b_1528_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_b_1528_, 0);
lean_dec(v_unused_1550_);
v___x_1533_ = v_b_1528_;
v_isShared_1534_ = v_isSharedCheck_1549_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_snd_1531_);
lean_dec(v_b_1528_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1549_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_a_1535_; lean_object* v_msg_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v_a_1535_ = lean_array_uget_borrowed(v_as_1525_, v_i_1527_);
v_msg_1536_ = lean_ctor_get(v_a_1535_, 1);
v___x_1537_ = lean_box(0);
lean_inc_ref(v___x_1521_);
v___x_1538_ = l_Lean_FileMap_toPosition(v___x_1521_, v___x_1522_);
v___x_1539_ = 0;
v___x_1540_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1536_);
lean_inc_ref(v___x_1523_);
v___x_1541_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1541_, 0, v___x_1523_);
lean_ctor_set(v___x_1541_, 1, v___x_1538_);
lean_ctor_set(v___x_1541_, 2, v___x_1537_);
lean_ctor_set(v___x_1541_, 3, v___x_1540_);
lean_ctor_set(v___x_1541_, 4, v_msg_1536_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*5, v_val_1524_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*5 + 1, v___x_1539_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*5 + 2, v_val_1524_);
v___x_1542_ = l_Lean_MessageLog_add(v___x_1541_, v_snd_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___x_1542_);
lean_ctor_set(v___x_1533_, 0, v___x_1537_);
v___x_1544_ = v___x_1533_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1527_, v___x_1545_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1521_, v___x_1522_, v___x_1523_, v_val_1524_, v_as_1525_, v_sz_1526_, v___x_1546_, v___x_1544_);
return v___x_1547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1551_, lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v_val_1554_, lean_object* v_as_1555_, lean_object* v_sz_1556_, lean_object* v_i_1557_, lean_object* v_b_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_val_44722__boxed_1560_; size_t v_sz_boxed_1561_; size_t v_i_boxed_1562_; lean_object* v_res_1563_; 
v_val_44722__boxed_1560_ = lean_unbox(v_val_1554_);
v_sz_boxed_1561_ = lean_unbox_usize(v_sz_1556_);
lean_dec(v_sz_1556_);
v_i_boxed_1562_ = lean_unbox_usize(v_i_1557_);
lean_dec(v_i_1557_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1551_, v___x_1552_, v___x_1553_, v_val_44722__boxed_1560_, v_as_1555_, v_sz_boxed_1561_, v_i_boxed_1562_, v_b_1558_);
lean_dec_ref(v_as_1555_);
lean_dec(v___x_1552_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1564_, lean_object* v___x_1565_, lean_object* v___x_1566_, uint8_t v_val_1567_, lean_object* v_t_1568_, lean_object* v_init_1569_){
_start:
{
lean_object* v_root_1571_; lean_object* v_tail_1572_; lean_object* v___x_1573_; 
v_root_1571_ = lean_ctor_get(v_t_1568_, 0);
v_tail_1572_ = lean_ctor_get(v_t_1568_, 1);
lean_inc_ref(v___x_1566_);
lean_inc_ref(v___x_1564_);
lean_inc_ref(v_init_1569_);
v___x_1573_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1569_, v___x_1564_, v___x_1565_, v___x_1566_, v_val_1567_, v_root_1571_, v_init_1569_);
lean_dec_ref(v_init_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; 
lean_dec_ref(v___x_1566_);
lean_dec_ref(v___x_1564_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
return v_a_1574_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; lean_object* v_fst_1581_; 
v_a_1575_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v_a_1575_);
v_sz_1578_ = lean_array_size(v_tail_1572_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1564_, v___x_1565_, v___x_1566_, v_val_1567_, v_tail_1572_, v_sz_1578_, v___x_1579_, v___x_1577_);
v_fst_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_fst_1581_);
if (lean_obj_tag(v_fst_1581_) == 0)
{
lean_object* v_snd_1582_; 
v_snd_1582_ = lean_ctor_get(v___x_1580_, 1);
lean_inc(v_snd_1582_);
lean_dec_ref(v___x_1580_);
return v_snd_1582_;
}
else
{
lean_object* v_val_1583_; 
lean_dec_ref(v___x_1580_);
v_val_1583_ = lean_ctor_get(v_fst_1581_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v_fst_1581_, 1);
return v_val_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v_val_1587_, lean_object* v_t_1588_, lean_object* v_init_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_val_44773__boxed_1591_; lean_object* v_res_1592_; 
v_val_44773__boxed_1591_ = lean_unbox(v_val_1587_);
v_res_1592_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1584_, v___x_1585_, v___x_1586_, v_val_44773__boxed_1591_, v_t_1588_, v_init_1589_);
lean_dec_ref(v_t_1588_);
lean_dec(v___x_1585_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = l_Lean_firstFrontendMacroScope;
v___x_1595_ = lean_nat_add(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1602_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, size_t v___x_1610_, uint8_t v___x_1611_, lean_object* v_env_1612_, lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_a_1615_, lean_object* v_opts_1616_, lean_object* v___x_1617_, lean_object* v_pos_1618_, uint8_t v_val_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, uint8_t v___x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_toProcessingContext_1646_; lean_object* v_fileName_1647_; lean_object* v_fileMap_1648_; lean_object* v_env_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v_fileName_1655_; lean_object* v_fileMap_1656_; lean_object* v_currRecDepth_1657_; lean_object* v_ref_1658_; lean_object* v_currNamespace_1659_; lean_object* v_openDecls_1660_; lean_object* v_initHeartbeats_1661_; lean_object* v_maxHeartbeats_1662_; lean_object* v_quotContext_1663_; lean_object* v_currMacroScope_1664_; lean_object* v_cancelTk_x3f_1665_; uint8_t v_suppressElabErrors_1666_; lean_object* v_inheritedTraceOptions_1667_; lean_object* v___y_1668_; uint8_t v___y_1685_; uint8_t v___x_1705_; 
v___x_1627_ = l_Lean_firstFrontendMacroScope;
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1630_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_1631_ = lean_box(0);
lean_inc(v___x_1607_);
v___x_1632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1607_);
lean_ctor_set(v___x_1632_, 1, v___x_1628_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
v___x_1633_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1634_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6);
v___x_1635_ = lean_mk_empty_array_with_capacity(v___x_1608_);
lean_inc_ref(v___x_1635_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_inc_n(v___x_1609_, 2);
v___x_1637_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1635_);
lean_ctor_set(v___x_1637_, 2, v___x_1609_);
lean_ctor_set(v___x_1637_, 3, v___x_1609_);
lean_ctor_set_usize(v___x_1637_, 4, v___x_1610_);
v___x_1638_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1637_, 2);
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1637_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1640_, 0, v___x_1633_);
lean_ctor_set(v___x_1640_, 1, v___x_1633_);
lean_ctor_set(v___x_1640_, 2, v___x_1637_);
lean_ctor_set_uint8(v___x_1640_, sizeof(void*)*3, v___x_1611_);
v___x_1641_ = lean_mk_empty_array_with_capacity(v___x_1609_);
lean_inc_ref(v___x_1641_);
lean_inc_ref(v___x_1613_);
v___x_1642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1642_, 0, v_env_1612_);
lean_ctor_set(v___x_1642_, 1, v___x_1629_);
lean_ctor_set(v___x_1642_, 2, v___x_1630_);
lean_ctor_set(v___x_1642_, 3, v___x_1632_);
lean_ctor_set(v___x_1642_, 4, v___x_1613_);
lean_ctor_set(v___x_1642_, 5, v___x_1634_);
lean_ctor_set(v___x_1642_, 6, v___x_1639_);
lean_ctor_set(v___x_1642_, 7, v___x_1640_);
lean_ctor_set(v___x_1642_, 8, v___x_1641_);
v___x_1643_ = lean_st_mk_ref(v___x_1642_);
v___x_1644_ = lean_st_ref_get(v___x_1614_);
v___x_1645_ = lean_st_ref_get(v___x_1643_);
v_toProcessingContext_1646_ = lean_ctor_get(v_a_1615_, 0);
v_fileName_1647_ = lean_ctor_get(v_toProcessingContext_1646_, 1);
v_fileMap_1648_ = lean_ctor_get(v_toProcessingContext_1646_, 2);
v_env_1649_ = lean_ctor_get(v___x_1645_, 0);
lean_inc_ref(v_env_1649_);
lean_dec(v___x_1645_);
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Lean_Core_getMaxHeartbeats(v_opts_1616_);
v___x_1652_ = l_Lean_diagnostics;
v___x_1653_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1616_, v___x_1652_);
v___x_1705_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1649_);
lean_dec_ref(v_env_1649_);
if (v___x_1705_ == 0)
{
if (v___x_1653_ == 0)
{
v___y_1685_ = v___x_1624_;
goto v___jp_1684_;
}
else
{
v___y_1685_ = v___x_1705_;
goto v___jp_1684_;
}
}
else
{
v___y_1685_ = v___x_1653_;
goto v___jp_1684_;
}
v___jp_1654_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = l_Lean_maxRecDepth;
v___x_1670_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1616_, v___x_1669_);
lean_inc(v_currMacroScope_1664_);
lean_inc(v_openDecls_1660_);
lean_inc(v_ref_1658_);
v___x_1671_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1671_, 0, v_fileName_1655_);
lean_ctor_set(v___x_1671_, 1, v_fileMap_1656_);
lean_ctor_set(v___x_1671_, 2, v_opts_1616_);
lean_ctor_set(v___x_1671_, 3, v_currRecDepth_1657_);
lean_ctor_set(v___x_1671_, 4, v___x_1670_);
lean_ctor_set(v___x_1671_, 5, v_ref_1658_);
lean_ctor_set(v___x_1671_, 6, v_currNamespace_1659_);
lean_ctor_set(v___x_1671_, 7, v_openDecls_1660_);
lean_ctor_set(v___x_1671_, 8, v_initHeartbeats_1661_);
lean_ctor_set(v___x_1671_, 9, v_maxHeartbeats_1662_);
lean_ctor_set(v___x_1671_, 10, v_quotContext_1663_);
lean_ctor_set(v___x_1671_, 11, v_currMacroScope_1664_);
lean_ctor_set(v___x_1671_, 12, v_cancelTk_x3f_1665_);
lean_ctor_set(v___x_1671_, 13, v_inheritedTraceOptions_1667_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*14, v___x_1653_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*14 + 1, v_suppressElabErrors_1666_);
v___x_1672_ = l_Lean_Language_SnapshotTree_trace(v___x_1617_, v___x_1671_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref_known(v___x_1671_, 14);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v___x_1673_; lean_object* v_traceState_1674_; lean_object* v_traces_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref_known(v___x_1672_, 1);
lean_dec_ref(v___x_1622_);
v___x_1673_ = lean_st_ref_get(v___x_1643_);
lean_dec(v___x_1643_);
v_traceState_1674_ = lean_ctor_get(v___x_1673_, 4);
lean_inc_ref(v_traceState_1674_);
lean_dec(v___x_1673_);
v_traces_1675_ = lean_ctor_get(v_traceState_1674_, 0);
lean_inc_ref(v_traces_1675_);
lean_dec_ref(v_traceState_1674_);
v___x_1676_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1647_);
lean_inc_ref(v_fileMap_1648_);
v___x_1677_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1648_, v_pos_1618_, v_fileName_1647_, v_val_1619_, v_traces_1675_, v___x_1676_);
lean_dec_ref(v_traces_1675_);
v___x_1678_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1679_, 0, v___x_1620_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
lean_ctor_set(v___x_1679_, 2, v___x_1621_);
lean_ctor_set(v___x_1679_, 3, v___x_1613_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*4, v_val_1619_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1641_);
v___x_1681_ = lean_task_pure(v___x_1680_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec_ref_known(v___x_1672_, 1);
lean_dec(v___x_1643_);
lean_dec(v___x_1621_);
lean_dec_ref(v___x_1620_);
lean_dec_ref(v___x_1613_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1622_);
lean_ctor_set(v___x_1682_, 1, v___x_1641_);
v___x_1683_ = lean_task_pure(v___x_1682_);
return v___x_1683_;
}
}
v___jp_1684_:
{
if (v___y_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v_env_1687_; lean_object* v_nextMacroScope_1688_; lean_object* v_ngen_1689_; lean_object* v_auxDeclNGen_1690_; lean_object* v_traceState_1691_; lean_object* v_messages_1692_; lean_object* v_infoState_1693_; lean_object* v_snapshotTasks_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
v___x_1686_ = lean_st_ref_take(v___x_1643_);
v_env_1687_ = lean_ctor_get(v___x_1686_, 0);
v_nextMacroScope_1688_ = lean_ctor_get(v___x_1686_, 1);
v_ngen_1689_ = lean_ctor_get(v___x_1686_, 2);
v_auxDeclNGen_1690_ = lean_ctor_get(v___x_1686_, 3);
v_traceState_1691_ = lean_ctor_get(v___x_1686_, 4);
v_messages_1692_ = lean_ctor_get(v___x_1686_, 6);
v_infoState_1693_ = lean_ctor_get(v___x_1686_, 7);
v_snapshotTasks_1694_ = lean_ctor_get(v___x_1686_, 8);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v___x_1686_, 5);
lean_dec(v_unused_1704_);
v___x_1696_ = v___x_1686_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_snapshotTasks_1694_);
lean_inc(v_infoState_1693_);
lean_inc(v_messages_1692_);
lean_inc(v_traceState_1691_);
lean_inc(v_auxDeclNGen_1690_);
lean_inc(v_ngen_1689_);
lean_inc(v_nextMacroScope_1688_);
lean_inc(v_env_1687_);
lean_dec(v___x_1686_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = l_Lean_Kernel_enableDiag(v_env_1687_, v___x_1653_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 5, v___x_1634_);
lean_ctor_set(v___x_1696_, 0, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_nextMacroScope_1688_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_ngen_1689_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_auxDeclNGen_1690_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_traceState_1691_);
lean_ctor_set(v_reuseFailAlloc_1702_, 5, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1702_, 6, v_messages_1692_);
lean_ctor_set(v_reuseFailAlloc_1702_, 7, v_infoState_1693_);
lean_ctor_set(v_reuseFailAlloc_1702_, 8, v_snapshotTasks_1694_);
v___x_1700_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_st_ref_set(v___x_1643_, v___x_1700_);
lean_inc(v___x_1643_);
lean_inc(v___x_1607_);
lean_inc(v___x_1609_);
lean_inc_ref(v_fileMap_1648_);
lean_inc_ref(v_fileName_1647_);
v_fileName_1655_ = v_fileName_1647_;
v_fileMap_1656_ = v_fileMap_1648_;
v_currRecDepth_1657_ = v___x_1609_;
v_ref_1658_ = v___x_1650_;
v_currNamespace_1659_ = v___x_1607_;
v_openDecls_1660_ = v___x_1631_;
v_initHeartbeats_1661_ = v___x_1609_;
v_maxHeartbeats_1662_ = v___x_1651_;
v_quotContext_1663_ = v___x_1607_;
v_currMacroScope_1664_ = v___x_1627_;
v_cancelTk_x3f_1665_ = v___x_1623_;
v_suppressElabErrors_1666_ = v_val_1619_;
v_inheritedTraceOptions_1667_ = v___x_1644_;
v___y_1668_ = v___x_1643_;
goto v___jp_1654_;
}
}
}
else
{
lean_inc(v___x_1643_);
lean_inc(v___x_1607_);
lean_inc(v___x_1609_);
lean_inc_ref(v_fileMap_1648_);
lean_inc_ref(v_fileName_1647_);
v_fileName_1655_ = v_fileName_1647_;
v_fileMap_1656_ = v_fileMap_1648_;
v_currRecDepth_1657_ = v___x_1609_;
v_ref_1658_ = v___x_1650_;
v_currNamespace_1659_ = v___x_1607_;
v_openDecls_1660_ = v___x_1631_;
v_initHeartbeats_1661_ = v___x_1609_;
v_maxHeartbeats_1662_ = v___x_1651_;
v_quotContext_1663_ = v___x_1607_;
v_currMacroScope_1664_ = v___x_1627_;
v_cancelTk_x3f_1665_ = v___x_1623_;
v_suppressElabErrors_1666_ = v_val_1619_;
v_inheritedTraceOptions_1667_ = v___x_1644_;
v___y_1668_ = v___x_1643_;
goto v___jp_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v___x_1706_ = _args[0];
lean_object* v___x_1707_ = _args[1];
lean_object* v___x_1708_ = _args[2];
lean_object* v___x_1709_ = _args[3];
lean_object* v___x_1710_ = _args[4];
lean_object* v_env_1711_ = _args[5];
lean_object* v___x_1712_ = _args[6];
lean_object* v___x_1713_ = _args[7];
lean_object* v_a_1714_ = _args[8];
lean_object* v_opts_1715_ = _args[9];
lean_object* v___x_1716_ = _args[10];
lean_object* v_pos_1717_ = _args[11];
lean_object* v_val_1718_ = _args[12];
lean_object* v___x_1719_ = _args[13];
lean_object* v___x_1720_ = _args[14];
lean_object* v___x_1721_ = _args[15];
lean_object* v___x_1722_ = _args[16];
lean_object* v___x_1723_ = _args[17];
lean_object* v_x_1724_ = _args[18];
lean_object* v___y_1725_ = _args[19];
_start:
{
size_t v___x_44834__boxed_1726_; uint8_t v___x_44835__boxed_1727_; uint8_t v_val_44839__boxed_1728_; uint8_t v___x_44844__boxed_1729_; lean_object* v_res_1730_; 
v___x_44834__boxed_1726_ = lean_unbox_usize(v___x_1709_);
lean_dec(v___x_1709_);
v___x_44835__boxed_1727_ = lean_unbox(v___x_1710_);
v_val_44839__boxed_1728_ = lean_unbox(v_val_1718_);
v___x_44844__boxed_1729_ = lean_unbox(v___x_1723_);
v_res_1730_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v___x_1706_, v___x_1707_, v___x_1708_, v___x_44834__boxed_1726_, v___x_44835__boxed_1727_, v_env_1711_, v___x_1712_, v___x_1713_, v_a_1714_, v_opts_1715_, v___x_1716_, v_pos_1717_, v_val_44839__boxed_1728_, v___x_1719_, v___x_1720_, v___x_1721_, v___x_1722_, v___x_44844__boxed_1729_, v_x_1724_);
lean_dec(v_pos_1717_);
lean_dec_ref(v_a_1714_);
lean_dec(v___x_1713_);
lean_dec(v___x_1707_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1731_, lean_object* v___x_1732_, lean_object* v_parserState_1733_, lean_object* v_x_1734_){
_start:
{
lean_object* v_toProcessingContext_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_toProcessingContext_1735_ = lean_ctor_get(v_a_1731_, 0);
v___x_1736_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1735_);
v___x_1737_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1735_, v___x_1732_, v_parserState_1733_, v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1738_, lean_object* v___x_1739_, lean_object* v_parserState_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1738_, v___x_1739_, v_parserState_1740_, v_x_1741_);
lean_dec_ref(v_a_1738_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1744_, size_t v_i_1745_, size_t v_stop_1746_, lean_object* v_b_1747_){
_start:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_usize_dec_eq(v_i_1745_, v_stop_1746_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; size_t v___x_1753_; size_t v___x_1754_; 
v___x_1750_ = lean_array_uget_borrowed(v_as_1744_, v_i_1745_);
v___f_1751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
lean_inc(v___x_1750_);
v___x_1752_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1751_, v___x_1750_);
v___x_1753_ = ((size_t)1ULL);
v___x_1754_ = lean_usize_add(v_i_1745_, v___x_1753_);
v_i_1745_ = v___x_1754_;
v_b_1747_ = v___x_1752_;
goto _start;
}
else
{
return v_b_1747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1756_, lean_object* v_i_1757_, lean_object* v_stop_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_i_boxed_1761_; size_t v_stop_boxed_1762_; lean_object* v_res_1763_; 
v_i_boxed_1761_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_stop_boxed_1762_ = lean_unbox_usize(v_stop_1758_);
lean_dec(v_stop_1758_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1756_, v_i_boxed_1761_, v_stop_boxed_1762_, v_b_1759_);
lean_dec_ref(v_as_1756_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1764_, lean_object* v_cmds_1765_, lean_object* v_stx_1766_, lean_object* v_newParserState_1767_, lean_object* v_val_1768_, lean_object* v_sync_1769_, lean_object* v_val_1770_, lean_object* v_a_1771_, lean_object* v_oldNext_1772_, lean_object* v___y_1773_){
_start:
{
uint8_t v_sync_boxed_1774_; lean_object* v_res_1775_; 
v_sync_boxed_1774_ = lean_unbox(v_sync_1769_);
v_res_1775_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1764_, v_cmds_1765_, v_stx_1766_, v_newParserState_1767_, v_val_1768_, v_sync_boxed_1774_, v_val_1770_, v_a_1771_, v_oldNext_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1776_, lean_object* v_cmds_1777_, lean_object* v_stx_1778_, lean_object* v_newParserState_1779_, lean_object* v_val_1780_, uint8_t v_sync_1781_, lean_object* v_val_1782_, lean_object* v_a_1783_, lean_object* v_oldResult_1784_){
_start:
{
lean_object* v_task_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v_task_1786_ = lean_ctor_get(v_val_1776_, 3);
lean_inc_ref(v_task_1786_);
lean_dec_ref(v_val_1776_);
v___x_1787_ = lean_box(v_sync_1781_);
lean_inc_ref(v_a_1783_);
v___f_1788_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1788_, 0, v_oldResult_1784_);
lean_closure_set(v___f_1788_, 1, v_cmds_1777_);
lean_closure_set(v___f_1788_, 2, v_stx_1778_);
lean_closure_set(v___f_1788_, 3, v_newParserState_1779_);
lean_closure_set(v___f_1788_, 4, v_val_1780_);
lean_closure_set(v___f_1788_, 5, v___x_1787_);
lean_closure_set(v___f_1788_, 6, v_val_1782_);
lean_closure_set(v___f_1788_, 7, v_a_1783_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = 1;
v___x_1791_ = l_BaseIO_chainTask___redArg(v_task_1786_, v___f_1788_, v___x_1789_, v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1792_, lean_object* v_cmds_1793_, lean_object* v_stx_1794_, lean_object* v_newParserState_1795_, lean_object* v_val_1796_, lean_object* v_sync_1797_, lean_object* v_val_1798_, lean_object* v_a_1799_, lean_object* v_oldResult_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v_sync_boxed_1802_; lean_object* v_res_1803_; 
v_sync_boxed_1802_ = lean_unbox(v_sync_1797_);
v_res_1803_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1792_, v_cmds_1793_, v_stx_1794_, v_newParserState_1795_, v_val_1796_, v_sync_boxed_1802_, v_val_1798_, v_a_1799_, v_oldResult_1800_);
lean_dec_ref(v_a_1799_);
return v_res_1803_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1806_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1805_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1808_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1817_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1818_ = l_Lean_Name_append(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1822_, lean_object* v_val_1823_, lean_object* v_cmds_1824_, lean_object* v_fst_1825_, lean_object* v_fst_1826_, uint8_t v_val_1827_, lean_object* v_a_1828_, lean_object* v_snd_1829_, lean_object* v___x_1830_, uint8_t v___x_1831_, lean_object* v_fst_1832_, lean_object* v_val_1833_, lean_object* v_val_1834_, lean_object* v_val_1835_, lean_object* v_snd_1836_, lean_object* v_prom_1837_, lean_object* v___x_1838_, lean_object* v___f_1839_, lean_object* v___f_1840_, lean_object* v___f_1841_, lean_object* v_pos_1842_, lean_object* v_cmdState_1843_, lean_object* v_opts_1844_, lean_object* v___x_1845_, lean_object* v_old_x3f_1846_, lean_object* v_parseCancelTk_1847_, lean_object* v_next_x3f_1848_){
_start:
{
lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v_snapshotTasks_1856_; lean_object* v_traceTask_1857_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1879_; size_t v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v_env_1893_; lean_object* v_messages_1894_; lean_object* v_scopes_1895_; lean_object* v_infoState_1896_; lean_object* v_traceState_1897_; lean_object* v_snapshotTasks_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v_reportedCmdState_1907_; lean_object* v___y_1942_; size_t v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v_reportedCmdState_1964_; lean_object* v___y_1972_; size_t v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; size_t v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_2027_; 
if (lean_obj_tag(v_next_x3f_1848_) == 0)
{
lean_object* v___x_2080_; 
lean_dec_ref(v_parseCancelTk_1847_);
v___x_2080_ = lean_box(0);
v___y_2027_ = v___x_2080_;
goto v___jp_2026_;
}
else
{
lean_object* v_toProcessingContext_2081_; lean_object* v_val_2082_; lean_object* v_pos_2083_; lean_object* v_endPos_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_toProcessingContext_2081_ = lean_ctor_get(v_a_1828_, 0);
v_val_2082_ = lean_ctor_get(v_next_x3f_1848_, 0);
v_pos_2083_ = lean_ctor_get(v_fst_1826_, 0);
v_endPos_2084_ = lean_ctor_get(v_toProcessingContext_2081_, 3);
v___x_2085_ = lean_box(0);
lean_inc(v_endPos_2084_);
lean_inc(v_pos_2083_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v_pos_2083_);
lean_ctor_set(v___x_2086_, 1, v_endPos_2084_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_parseCancelTk_1847_);
v___x_2089_ = l_IO_Promise_result_x21___redArg(v_val_2082_);
v___x_2090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2085_);
lean_ctor_set(v___x_2090_, 1, v___x_2087_);
lean_ctor_set(v___x_2090_, 2, v___x_2088_);
lean_ctor_set(v___x_2090_, 3, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___y_2027_ = v___x_2091_;
goto v___jp_2026_;
}
v___jp_1850_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1858_, 0, v___y_1853_);
lean_ctor_set(v___x_1858_, 1, v___x_1822_);
lean_ctor_set(v___x_1858_, 2, v___y_1851_);
lean_ctor_set(v___x_1858_, 3, v_traceTask_1857_);
v___x_1859_ = lean_array_push(v_snapshotTasks_1856_, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1852_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_io_promise_resolve(v___x_1860_, v_val_1823_);
if (lean_obj_tag(v_next_x3f_1848_) == 1)
{
lean_object* v_val_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_val_1862_ = lean_ctor_get(v_next_x3f_1848_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_next_x3f_1848_, 1);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_array_push(v_cmds_1824_, v_fst_1825_);
v___x_1865_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1863_, v_fst_1826_, v___y_1855_, v_val_1862_, v_val_1827_, v___y_1854_, v___x_1864_, v_a_1828_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; 
lean_dec_ref(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_next_x3f_1848_);
lean_dec_ref(v_fst_1826_);
lean_dec(v_fst_1825_);
lean_dec_ref(v_cmds_1824_);
v___x_1866_ = lean_box(0);
return v___x_1866_;
}
}
v___jp_1867_:
{
lean_object* v_snapshotTasks_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_snapshotTasks_1874_ = lean_ctor_get(v___y_1873_, 10);
lean_inc_ref(v_snapshotTasks_1874_);
v___x_1875_ = lean_mk_empty_array_with_capacity(v___y_1872_);
lean_dec(v___y_1872_);
lean_inc_ref(v___y_1869_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___y_1869_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_task_pure(v___x_1876_);
v___y_1851_ = v___y_1868_;
v___y_1852_ = v___y_1869_;
v___y_1853_ = v___y_1870_;
v___y_1854_ = v___y_1871_;
v___y_1855_ = v___y_1873_;
v_snapshotTasks_1856_ = v_snapshotTasks_1874_;
v_traceTask_1857_ = v___x_1877_;
goto v___jp_1850_;
}
v___jp_1878_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v_opts_1917_; uint8_t v_hasTrace_1918_; 
v___x_1908_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1894_);
v___x_1909_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1909_, 0, v___y_1890_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
lean_ctor_set(v___x_1909_, 2, v___y_1900_);
lean_ctor_set(v___x_1909_, 3, v_traceState_1897_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*4, v_val_1827_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_reportedCmdState_1907_);
v___x_1911_ = lean_io_promise_resolve(v___x_1910_, v_val_1834_);
v___x_1912_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1896_);
lean_inc(v___y_1905_);
v___x_1913_ = l_BaseIO_chainTask___redArg(v___x_1912_, v___y_1906_, v___y_1905_, v___x_1831_);
v___x_1914_ = l_Lean_inheritedTraceOptions;
v___x_1915_ = lean_st_ref_get(v___x_1914_);
v___x_1916_ = l_List_head_x21___redArg(v___x_1838_, v_scopes_1895_);
lean_dec(v_scopes_1895_);
lean_dec_ref(v___x_1838_);
v_opts_1917_ = lean_ctor_get(v___x_1916_, 1);
lean_inc_ref(v_opts_1917_);
lean_dec(v___x_1916_);
v_hasTrace_1918_ = lean_ctor_get_uint8(v_opts_1917_, sizeof(void*)*1);
if (v_hasTrace_1918_ == 0)
{
lean_dec_ref(v_opts_1917_);
lean_dec(v___x_1915_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1899_);
lean_dec_ref(v_snapshotTasks_1898_);
lean_dec_ref(v_env_1893_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1879_);
lean_dec(v_pos_1842_);
lean_dec_ref(v___f_1841_);
lean_dec_ref(v___f_1840_);
lean_dec_ref(v___f_1839_);
lean_dec(v___x_1830_);
v___y_1868_ = v___y_1887_;
v___y_1869_ = v___y_1902_;
v___y_1870_ = v___y_1888_;
v___y_1871_ = v___y_1904_;
v___y_1872_ = v___y_1905_;
v___y_1873_ = v___y_1892_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1915_, v_opts_1917_, v___x_1919_);
lean_dec(v___x_1915_);
if (v___x_1920_ == 0)
{
lean_dec_ref(v_opts_1917_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1899_);
lean_dec_ref(v_snapshotTasks_1898_);
lean_dec_ref(v_env_1893_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1879_);
lean_dec(v_pos_1842_);
lean_dec_ref(v___f_1841_);
lean_dec_ref(v___f_1840_);
lean_dec_ref(v___f_1839_);
lean_dec(v___x_1830_);
v___y_1868_ = v___y_1887_;
v___y_1869_ = v___y_1902_;
v___y_1870_ = v___y_1888_;
v___y_1871_ = v___y_1904_;
v___y_1872_ = v___y_1905_;
v___y_1873_ = v___y_1892_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; lean_object* v___x_1940_; 
lean_inc_n(v___y_1905_, 3);
v___x_1921_ = lean_task_map(v___f_1839_, v___y_1889_, v___y_1905_, v___x_1831_);
lean_inc_n(v___y_1887_, 3);
lean_inc_n(v___y_1903_, 2);
lean_inc_n(v___y_1899_, 2);
v___x_1922_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1899_);
lean_ctor_set(v___x_1922_, 1, v___y_1903_);
lean_ctor_set(v___x_1922_, 2, v___y_1887_);
lean_ctor_set(v___x_1922_, 3, v___x_1921_);
v___x_1923_ = lean_task_map(v___f_1840_, v___y_1891_, v___y_1905_, v___x_1831_);
v___x_1924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1924_, 0, v___y_1899_);
lean_ctor_set(v___x_1924_, 1, v___y_1903_);
lean_ctor_set(v___x_1924_, 2, v___y_1887_);
lean_ctor_set(v___x_1924_, 3, v___x_1923_);
v___x_1925_ = lean_task_map(v___f_1841_, v___y_1901_, v___y_1905_, v___x_1831_);
v___x_1926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1899_);
lean_ctor_set(v___x_1926_, 1, v___y_1903_);
lean_ctor_set(v___x_1926_, 2, v___y_1887_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = lean_unsigned_to_nat(3u);
v___x_1928_ = lean_mk_empty_array_with_capacity(v___x_1927_);
v___x_1929_ = lean_array_push(v___x_1928_, v___x_1922_);
v___x_1930_ = lean_array_push(v___x_1929_, v___x_1924_);
v___x_1931_ = lean_array_push(v___x_1930_, v___x_1926_);
v___x_1932_ = l_Array_append___redArg(v___x_1931_, v_snapshotTasks_1898_);
lean_inc_ref(v___y_1902_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___y_1902_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
lean_inc_ref(v___x_1933_);
v___x_1934_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1933_);
v___x_1935_ = lean_box_usize(v___y_1880_);
v___x_1936_ = lean_box(v___x_1831_);
v___x_1937_ = lean_box(v_val_1827_);
v___x_1938_ = lean_box(v___x_1920_);
lean_inc_ref(v_a_1828_);
lean_inc_ref(v___y_1883_);
v___f_1939_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1939_, 0, v___x_1830_);
lean_closure_set(v___f_1939_, 1, v___y_1882_);
lean_closure_set(v___f_1939_, 2, v___y_1885_);
lean_closure_set(v___f_1939_, 3, v___x_1935_);
lean_closure_set(v___f_1939_, 4, v___x_1936_);
lean_closure_set(v___f_1939_, 5, v_env_1893_);
lean_closure_set(v___f_1939_, 6, v___y_1883_);
lean_closure_set(v___f_1939_, 7, v___x_1914_);
lean_closure_set(v___f_1939_, 8, v_a_1828_);
lean_closure_set(v___f_1939_, 9, v_opts_1917_);
lean_closure_set(v___f_1939_, 10, v___x_1933_);
lean_closure_set(v___f_1939_, 11, v_pos_1842_);
lean_closure_set(v___f_1939_, 12, v___x_1937_);
lean_closure_set(v___f_1939_, 13, v___y_1886_);
lean_closure_set(v___f_1939_, 14, v___y_1884_);
lean_closure_set(v___f_1939_, 15, v___y_1879_);
lean_closure_set(v___f_1939_, 16, v___y_1881_);
lean_closure_set(v___f_1939_, 17, v___x_1938_);
v___x_1940_ = lean_io_bind_task(v___x_1934_, v___f_1939_, v___y_1905_, v_val_1827_);
v___y_1851_ = v___y_1887_;
v___y_1852_ = v___y_1902_;
v___y_1853_ = v___y_1888_;
v___y_1854_ = v___y_1904_;
v___y_1855_ = v___y_1892_;
v_snapshotTasks_1856_ = v_snapshotTasks_1898_;
v_traceTask_1857_ = v___x_1940_;
goto v___jp_1850_;
}
}
}
v___jp_1941_:
{
lean_object* v_env_1965_; lean_object* v_messages_1966_; lean_object* v_scopes_1967_; lean_object* v_infoState_1968_; lean_object* v_traceState_1969_; lean_object* v_snapshotTasks_1970_; 
v_env_1965_ = lean_ctor_get(v___y_1955_, 0);
lean_inc_ref(v_env_1965_);
v_messages_1966_ = lean_ctor_get(v___y_1955_, 1);
lean_inc_ref(v_messages_1966_);
v_scopes_1967_ = lean_ctor_get(v___y_1955_, 2);
lean_inc(v_scopes_1967_);
v_infoState_1968_ = lean_ctor_get(v___y_1955_, 8);
lean_inc_ref(v_infoState_1968_);
v_traceState_1969_ = lean_ctor_get(v___y_1955_, 9);
lean_inc_ref(v_traceState_1969_);
v_snapshotTasks_1970_ = lean_ctor_get(v___y_1955_, 10);
lean_inc_ref(v_snapshotTasks_1970_);
v___y_1879_ = v___y_1942_;
v___y_1880_ = v___y_1943_;
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
v_env_1893_ = v_env_1965_;
v_messages_1894_ = v_messages_1966_;
v_scopes_1895_ = v_scopes_1967_;
v_infoState_1896_ = v_infoState_1968_;
v_traceState_1897_ = v_traceState_1969_;
v_snapshotTasks_1898_ = v_snapshotTasks_1970_;
v___y_1899_ = v___y_1956_;
v___y_1900_ = v___y_1957_;
v___y_1901_ = v___y_1958_;
v___y_1902_ = v___y_1959_;
v___y_1903_ = v___y_1960_;
v___y_1904_ = v___y_1961_;
v___y_1905_ = v___y_1962_;
v___y_1906_ = v___y_1963_;
v_reportedCmdState_1907_ = v_reportedCmdState_1964_;
goto v___jp_1878_;
}
v___jp_1971_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___f_2000_; uint8_t v___x_2001_; 
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___y_1995_);
lean_ctor_set(v___x_1996_, 1, v_val_1833_);
lean_inc_ref(v___y_1992_);
lean_inc_n(v_pos_1842_, 2);
lean_inc_ref(v_cmds_1824_);
lean_inc(v_fst_1825_);
v___x_1997_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1825_, v_cmds_1824_, v_cmdState_1843_, v_pos_1842_, v___x_1996_, v___y_1992_, v_a_1828_);
v___x_1998_ = lean_box(v_val_1827_);
v___x_1999_ = lean_box(v___x_1831_);
lean_inc_ref(v_a_1828_);
lean_inc(v___y_1978_);
lean_inc_ref(v___x_1838_);
lean_inc_ref(v___x_1997_);
lean_inc_ref(v___y_1976_);
lean_inc_ref(v___y_1979_);
v___f_2000_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 12, 10);
lean_closure_set(v___f_2000_, 0, v___y_1979_);
lean_closure_set(v___f_2000_, 1, v___y_1976_);
lean_closure_set(v___f_2000_, 2, v___x_1998_);
lean_closure_set(v___f_2000_, 3, v_val_1835_);
lean_closure_set(v___f_2000_, 4, v___x_1997_);
lean_closure_set(v___f_2000_, 5, v___x_1838_);
lean_closure_set(v___f_2000_, 6, v___y_1978_);
lean_closure_set(v___f_2000_, 7, v___x_1999_);
lean_closure_set(v___f_2000_, 8, v_a_1828_);
lean_closure_set(v___f_2000_, 9, v_pos_1842_);
v___x_2001_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1844_, v___x_1845_);
if (v___x_2001_ == 0)
{
lean_dec(v___y_1981_);
lean_inc_ref(v___x_1997_);
v___y_1942_ = v___y_1972_;
v___y_1943_ = v___y_1973_;
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1978_;
v___y_1948_ = v___y_1977_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1982_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___x_1997_;
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___f_2000_;
v_reportedCmdState_1964_ = v___x_1997_;
goto v___jp_1941_;
}
else
{
uint8_t v___x_2002_; 
lean_inc(v_fst_1825_);
v___x_2002_ = l_Lean_Parser_isTerminalCommand(v_fst_1825_);
if (v___x_2002_ == 0)
{
if (v___x_2001_ == 0)
{
lean_dec(v___y_1981_);
lean_inc_ref(v___x_1997_);
v___y_1942_ = v___y_1972_;
v___y_1943_ = v___y_1973_;
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1978_;
v___y_1948_ = v___y_1977_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1982_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___x_1997_;
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___f_2000_;
v_reportedCmdState_1964_ = v___x_1997_;
goto v___jp_1941_;
}
else
{
lean_object* v_env_2003_; lean_object* v_messages_2004_; lean_object* v_scopes_2005_; lean_object* v_infoState_2006_; lean_object* v_traceState_2007_; lean_object* v_snapshotTasks_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_env_2003_ = lean_ctor_get(v___x_1997_, 0);
lean_inc_ref_n(v_env_2003_, 2);
v_messages_2004_ = lean_ctor_get(v___x_1997_, 1);
lean_inc_ref(v_messages_2004_);
v_scopes_2005_ = lean_ctor_get(v___x_1997_, 2);
lean_inc(v_scopes_2005_);
v_infoState_2006_ = lean_ctor_get(v___x_1997_, 8);
lean_inc_ref(v_infoState_2006_);
v_traceState_2007_ = lean_ctor_get(v___x_1997_, 9);
lean_inc_ref(v_traceState_2007_);
v_snapshotTasks_2008_ = lean_ctor_get(v___x_1997_, 10);
lean_inc_ref(v_snapshotTasks_2008_);
v___x_2009_ = lean_mk_empty_array_with_capacity(v___y_1981_);
lean_dec(v___y_1981_);
lean_inc_ref(v___x_2009_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_inc_n(v___y_1993_, 3);
v___x_2011_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
lean_ctor_set(v___x_2011_, 2, v___y_1993_);
lean_ctor_set(v___x_2011_, 3, v___y_1993_);
lean_ctor_set_usize(v___x_2011_, 4, v___y_1994_);
v___x_2012_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2011_, 2);
v___x_2013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2011_);
lean_ctor_set(v___x_2013_, 2, v___x_2012_);
v___x_2014_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2015_ = l_Lean_Options_empty;
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_mk_empty_array_with_capacity(v___y_1993_);
lean_inc_ref_n(v___x_2017_, 2);
lean_inc_n(v___x_1830_, 2);
v___x_2018_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2018_, 0, v___x_2014_);
lean_ctor_set(v___x_2018_, 1, v___x_2015_);
lean_ctor_set(v___x_2018_, 2, v___x_1830_);
lean_ctor_set(v___x_2018_, 3, v___x_2016_);
lean_ctor_set(v___x_2018_, 4, v___x_2016_);
lean_ctor_set(v___x_2018_, 5, v___x_2017_);
lean_ctor_set(v___x_2018_, 6, v___x_2017_);
lean_ctor_set(v___x_2018_, 7, v___x_2016_);
lean_ctor_set(v___x_2018_, 8, v___x_2016_);
lean_ctor_set(v___x_2018_, 9, v___x_2016_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*10, v_val_1827_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*10 + 1, v_val_1827_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*10 + 2, v_val_1827_);
v___x_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2016_);
v___x_2020_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2021_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2022_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1830_);
v___x_2023_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2024_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
lean_ctor_set(v___x_2024_, 2, v___x_2011_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*3, v___x_1831_);
lean_inc_ref(v___y_1986_);
v___x_2025_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2025_, 0, v_env_2003_);
lean_ctor_set(v___x_2025_, 1, v___x_2013_);
lean_ctor_set(v___x_2025_, 2, v___x_2019_);
lean_ctor_set(v___x_2025_, 3, v___x_2012_);
lean_ctor_set(v___x_2025_, 4, v___x_2020_);
lean_ctor_set(v___x_2025_, 5, v___y_1993_);
lean_ctor_set(v___x_2025_, 6, v___x_2021_);
lean_ctor_set(v___x_2025_, 7, v___x_2022_);
lean_ctor_set(v___x_2025_, 8, v___x_2024_);
lean_ctor_set(v___x_2025_, 9, v___y_1986_);
lean_ctor_set(v___x_2025_, 10, v___x_2017_);
v___y_1879_ = v___y_1972_;
v___y_1880_ = v___y_1973_;
v___y_1881_ = v___y_1974_;
v___y_1882_ = v___y_1975_;
v___y_1883_ = v___y_1976_;
v___y_1884_ = v___y_1977_;
v___y_1885_ = v___y_1978_;
v___y_1886_ = v___y_1979_;
v___y_1887_ = v___y_1980_;
v___y_1888_ = v___y_1982_;
v___y_1889_ = v___y_1983_;
v___y_1890_ = v___y_1984_;
v___y_1891_ = v___y_1985_;
v___y_1892_ = v___x_1997_;
v_env_1893_ = v_env_2003_;
v_messages_1894_ = v_messages_2004_;
v_scopes_1895_ = v_scopes_2005_;
v_infoState_1896_ = v_infoState_2006_;
v_traceState_1897_ = v_traceState_2007_;
v_snapshotTasks_1898_ = v_snapshotTasks_2008_;
v___y_1899_ = v___y_1987_;
v___y_1900_ = v___y_1988_;
v___y_1901_ = v___y_1989_;
v___y_1902_ = v___y_1990_;
v___y_1903_ = v___y_1991_;
v___y_1904_ = v___y_1992_;
v___y_1905_ = v___y_1993_;
v___y_1906_ = v___f_2000_;
v_reportedCmdState_1907_ = v___x_2025_;
goto v___jp_1878_;
}
}
else
{
lean_dec(v___y_1981_);
lean_inc_ref(v___x_1997_);
v___y_1942_ = v___y_1972_;
v___y_1943_ = v___y_1973_;
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1975_;
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1978_;
v___y_1948_ = v___y_1977_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1982_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___x_1997_;
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___f_2000_;
v_reportedCmdState_1964_ = v___x_1997_;
goto v___jp_1941_;
}
}
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2028_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1829_);
v___x_2029_ = l_IO_CancelToken_new();
v___x_2030_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1830_);
v___x_2031_ = l_Lean_Name_str___override(v___x_1830_, v___x_2030_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2033_ = l_Lean_Name_str___override(v___x_2031_, v___x_2032_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2035_ = l_Lean_Name_str___override(v___x_2033_, v___x_2034_);
v___x_2036_ = l_Lean_Name_str___override(v___x_2035_, v___x_2032_);
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = l_Lean_Name_num___override(v___x_2036_, v___x_2037_);
v___x_2039_ = l_Lean_Name_str___override(v___x_2038_, v___x_2032_);
v___x_2040_ = l_Lean_Name_str___override(v___x_2039_, v___x_2034_);
v___x_2041_ = l_Lean_Name_str___override(v___x_2040_, v___x_2032_);
v___x_2042_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2043_ = l_Lean_Name_str___override(v___x_2041_, v___x_2042_);
v___x_2044_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2045_ = l_Lean_Name_str___override(v___x_2043_, v___x_2044_);
v___x_2046_ = l_Lean_Name_toString(v___x_2045_, v___x_1831_);
v___x_2047_ = lean_box(0);
v___x_2048_ = lean_unsigned_to_nat(32u);
v___x_2049_ = ((size_t)5ULL);
v___x_2050_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2046_, 2);
v___x_2051_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2051_, 0, v___x_2046_);
lean_ctor_set(v___x_2051_, 1, v___x_2028_);
lean_ctor_set(v___x_2051_, 2, v___x_2047_);
lean_ctor_set(v___x_2051_, 3, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*4, v_val_1827_);
v___x_2052_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2053_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2053_, 0, v___x_2046_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_ctor_set(v___x_2053_, 2, v___x_2047_);
lean_ctor_set(v___x_2053_, 3, v___x_2050_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*4, v_val_1827_);
lean_inc(v_fst_1832_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_fst_1832_);
v___x_2055_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2054_);
lean_inc_ref(v___x_2029_);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2029_);
v___x_2057_ = l_IO_Promise_result_x21___redArg(v_val_1833_);
lean_inc_ref(v___x_2057_);
lean_inc(v___x_2055_);
lean_inc_ref_n(v___x_2054_, 3);
v___x_2058_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2054_);
lean_ctor_set(v___x_2058_, 1, v___x_2055_);
lean_ctor_set(v___x_2058_, 2, v___x_2056_);
lean_ctor_set(v___x_2058_, 3, v___x_2057_);
v___x_2059_ = l_IO_Promise_result_x21___redArg(v_val_1834_);
lean_inc_ref(v___x_2059_);
lean_inc_n(v___x_1822_, 3);
v___x_2060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2054_);
lean_ctor_set(v___x_2060_, 1, v___x_1822_);
lean_ctor_set(v___x_2060_, 2, v___x_2047_);
lean_ctor_set(v___x_2060_, 3, v___x_2059_);
v___x_2061_ = l_IO_Promise_result_x21___redArg(v_val_1835_);
lean_inc_ref(v___x_2061_);
v___x_2062_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2054_);
lean_ctor_set(v___x_2062_, 1, v___x_1822_);
lean_ctor_set(v___x_2062_, 2, v___x_2047_);
lean_ctor_set(v___x_2062_, 3, v___x_2061_);
v___x_2063_ = l_IO_Promise_result_x21___redArg(v_val_1823_);
v___x_2064_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2047_);
lean_ctor_set(v___x_2064_, 1, v___x_1822_);
lean_ctor_set(v___x_2064_, 2, v___x_2047_);
lean_ctor_set(v___x_2064_, 3, v___x_2063_);
lean_inc_ref(v___x_2053_);
v___x_2065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2053_);
lean_ctor_set(v___x_2065_, 1, v___x_2058_);
lean_ctor_set(v___x_2065_, 2, v___x_2060_);
lean_ctor_set(v___x_2065_, 3, v___x_2062_);
lean_ctor_set(v___x_2065_, 4, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2051_);
lean_ctor_set(v___x_2066_, 1, v_fst_1832_);
lean_ctor_set(v___x_2066_, 2, v_snd_1836_);
lean_ctor_set(v___x_2066_, 3, v___x_2065_);
lean_ctor_set(v___x_2066_, 4, v___y_2027_);
v___x_2067_ = lean_io_promise_resolve(v___x_2066_, v_prom_1837_);
if (lean_obj_tag(v_old_x3f_1846_) == 0)
{
lean_inc_ref(v___x_2046_);
lean_inc_ref(v___x_2053_);
v___y_1972_ = v___x_2053_;
v___y_1973_ = v___x_2049_;
v___y_1974_ = v___x_2047_;
v___y_1975_ = v___x_2048_;
v___y_1976_ = v___x_2050_;
v___y_1977_ = v___x_2047_;
v___y_1978_ = v___x_2037_;
v___y_1979_ = v___x_2046_;
v___y_1980_ = v___x_2047_;
v___y_1981_ = v___x_2048_;
v___y_1982_ = v___x_2047_;
v___y_1983_ = v___x_2057_;
v___y_1984_ = v___x_2046_;
v___y_1985_ = v___x_2059_;
v___y_1986_ = v___x_2050_;
v___y_1987_ = v___x_2054_;
v___y_1988_ = v___x_2047_;
v___y_1989_ = v___x_2061_;
v___y_1990_ = v___x_2053_;
v___y_1991_ = v___x_2055_;
v___y_1992_ = v___x_2029_;
v___y_1993_ = v___x_2037_;
v___y_1994_ = v___x_2049_;
v___y_1995_ = v___x_2047_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2079_; 
v_val_2068_ = lean_ctor_get(v_old_x3f_1846_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_old_x3f_1846_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2070_ = v_old_x3f_1846_;
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v_old_x3f_1846_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_elabSnap_2072_; lean_object* v_stx_2073_; lean_object* v_elabSnap_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v_elabSnap_2072_ = lean_ctor_get(v_val_2068_, 3);
lean_inc_ref(v_elabSnap_2072_);
v_stx_2073_ = lean_ctor_get(v_val_2068_, 1);
lean_inc(v_stx_2073_);
lean_dec(v_val_2068_);
v_elabSnap_2074_ = lean_ctor_get(v_elabSnap_2072_, 1);
lean_inc_ref(v_elabSnap_2074_);
lean_dec_ref(v_elabSnap_2072_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_stx_2073_);
lean_ctor_set(v___x_2075_, 1, v_elabSnap_2074_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2075_);
v___x_2077_ = v___x_2070_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_inc_ref(v___x_2046_);
lean_inc_ref(v___x_2053_);
v___y_1972_ = v___x_2053_;
v___y_1973_ = v___x_2049_;
v___y_1974_ = v___x_2047_;
v___y_1975_ = v___x_2048_;
v___y_1976_ = v___x_2050_;
v___y_1977_ = v___x_2047_;
v___y_1978_ = v___x_2037_;
v___y_1979_ = v___x_2046_;
v___y_1980_ = v___x_2047_;
v___y_1981_ = v___x_2048_;
v___y_1982_ = v___x_2047_;
v___y_1983_ = v___x_2057_;
v___y_1984_ = v___x_2046_;
v___y_1985_ = v___x_2059_;
v___y_1986_ = v___x_2050_;
v___y_1987_ = v___x_2054_;
v___y_1988_ = v___x_2047_;
v___y_1989_ = v___x_2061_;
v___y_1990_ = v___x_2053_;
v___y_1991_ = v___x_2055_;
v___y_1992_ = v___x_2029_;
v___y_1993_ = v___x_2037_;
v___y_1994_ = v___x_2049_;
v___y_1995_ = v___x_2077_;
goto v___jp_1971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_cmds_2092_, lean_object* v_fst_2093_, lean_object* v_fst_2094_, uint8_t v_val_2095_, lean_object* v_a_2096_, lean_object* v_snd_2097_, lean_object* v___x_2098_, uint8_t v___x_2099_, lean_object* v_prom_2100_, lean_object* v___x_2101_, lean_object* v___f_2102_, lean_object* v___f_2103_, lean_object* v___f_2104_, lean_object* v_pos_2105_, lean_object* v_cmdState_2106_, lean_object* v_opts_2107_, lean_object* v_old_x3f_2108_, lean_object* v_parseCancelTk_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v_snapshotTasks_2122_; lean_object* v___y_2123_; lean_object* v_traceTask_2124_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2148_; size_t v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v_env_2170_; lean_object* v_messages_2171_; lean_object* v_scopes_2172_; lean_object* v_infoState_2173_; lean_object* v_traceState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v_reportedCmdState_2178_; lean_object* v___y_2213_; size_t v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v_reportedCmdState_2237_; lean_object* v___x_2244_; lean_object* v___y_2246_; size_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; size_t v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v_fst_2381_; lean_object* v_snd_2382_; uint8_t v___y_2395_; uint8_t v___x_2398_; 
v___x_2111_ = lean_io_promise_new();
v___x_2112_ = lean_io_promise_new();
v___x_2113_ = lean_io_promise_new();
v___x_2114_ = lean_io_promise_new();
v___x_2244_ = l_Lean_internal_cmdlineSnapshots;
v___x_2398_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2107_, v___x_2244_);
if (v___x_2398_ == 0)
{
v___y_2395_ = v___x_2398_;
goto v___jp_2394_;
}
else
{
uint8_t v___x_2399_; 
lean_inc(v_fst_2093_);
v___x_2399_ = l_Lean_Parser_isTerminalCommand(v_fst_2093_);
if (v___x_2399_ == 0)
{
v___y_2395_ = v___x_2398_;
goto v___jp_2394_;
}
else
{
lean_inc_ref(v_fst_2094_);
lean_inc(v_fst_2093_);
v_fst_2381_ = v_fst_2093_;
v_snd_2382_ = v_fst_2094_;
goto v___jp_2380_;
}
}
v___jp_2115_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2125_, 0, v___y_2119_);
lean_ctor_set(v___x_2125_, 1, v___y_2123_);
lean_ctor_set(v___x_2125_, 2, v___y_2120_);
lean_ctor_set(v___x_2125_, 3, v_traceTask_2124_);
v___x_2126_ = lean_array_push(v_snapshotTasks_2122_, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___y_2116_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_io_promise_resolve(v___x_2127_, v___x_2114_);
lean_dec(v___x_2114_);
if (lean_obj_tag(v___y_2118_) == 1)
{
lean_object* v_val_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_val_2129_ = lean_ctor_get(v___y_2118_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v___y_2118_, 1);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_array_push(v_cmds_2092_, v_fst_2093_);
v___x_2132_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2130_, v_fst_2094_, v___y_2121_, v_val_2129_, v_val_2095_, v___y_2117_, v___x_2131_, v_a_2096_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_fst_2094_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_cmds_2092_);
v___x_2133_ = lean_box(0);
return v___x_2133_;
}
}
v___jp_2134_:
{
lean_object* v_snapshotTasks_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_snapshotTasks_2143_ = lean_ctor_get(v___y_2140_, 10);
lean_inc_ref(v_snapshotTasks_2143_);
v___x_2144_ = lean_mk_empty_array_with_capacity(v___y_2141_);
lean_dec(v___y_2141_);
lean_inc_ref(v___y_2135_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___y_2135_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_task_pure(v___x_2145_);
v___y_2116_ = v___y_2135_;
v___y_2117_ = v___y_2137_;
v___y_2118_ = v___y_2136_;
v___y_2119_ = v___y_2138_;
v___y_2120_ = v___y_2139_;
v___y_2121_ = v___y_2140_;
v_snapshotTasks_2122_ = v_snapshotTasks_2143_;
v___y_2123_ = v___y_2142_;
v_traceTask_2124_ = v___x_2146_;
goto v___jp_2115_;
}
v___jp_2147_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_opts_2188_; uint8_t v_hasTrace_2189_; 
v___x_2179_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2171_);
v___x_2180_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2180_, 0, v___y_2156_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
lean_ctor_set(v___x_2180_, 2, v___y_2167_);
lean_ctor_set(v___x_2180_, 3, v_traceState_2174_);
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*4, v_val_2095_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v_reportedCmdState_2178_);
v___x_2182_ = lean_io_promise_resolve(v___x_2181_, v___x_2112_);
lean_dec(v___x_2112_);
v___x_2183_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2173_);
lean_inc(v___y_2176_);
v___x_2184_ = l_BaseIO_chainTask___redArg(v___x_2183_, v___y_2168_, v___y_2176_, v___x_2099_);
v___x_2185_ = l_Lean_inheritedTraceOptions;
v___x_2186_ = lean_st_ref_get(v___x_2185_);
v___x_2187_ = l_List_head_x21___redArg(v___x_2101_, v_scopes_2172_);
lean_dec(v_scopes_2172_);
lean_dec_ref(v___x_2101_);
v_opts_2188_ = lean_ctor_get(v___x_2187_, 1);
lean_inc_ref(v_opts_2188_);
lean_dec(v___x_2187_);
v_hasTrace_2189_ = lean_ctor_get_uint8(v_opts_2188_, sizeof(void*)*1);
if (v_hasTrace_2189_ == 0)
{
lean_dec_ref(v_opts_2188_);
lean_dec(v___x_2186_);
lean_dec_ref(v___y_2177_);
lean_dec_ref(v_snapshotTasks_2175_);
lean_dec_ref(v_env_2170_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v_pos_2105_);
lean_dec_ref(v___f_2104_);
lean_dec_ref(v___f_2103_);
lean_dec_ref(v___f_2102_);
lean_dec(v___x_2098_);
v___y_2135_ = v___y_2157_;
v___y_2136_ = v___y_2158_;
v___y_2137_ = v___y_2166_;
v___y_2138_ = v___y_2159_;
v___y_2139_ = v___y_2163_;
v___y_2140_ = v___y_2169_;
v___y_2141_ = v___y_2176_;
v___y_2142_ = v___y_2164_;
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
lean_dec_ref(v___y_2177_);
lean_dec_ref(v_snapshotTasks_2175_);
lean_dec_ref(v_env_2170_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v_pos_2105_);
lean_dec_ref(v___f_2104_);
lean_dec_ref(v___f_2103_);
lean_dec_ref(v___f_2102_);
lean_dec(v___x_2098_);
v___y_2135_ = v___y_2157_;
v___y_2136_ = v___y_2158_;
v___y_2137_ = v___y_2166_;
v___y_2138_ = v___y_2159_;
v___y_2139_ = v___y_2163_;
v___y_2140_ = v___y_2169_;
v___y_2141_ = v___y_2176_;
v___y_2142_ = v___y_2164_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; 
lean_inc_n(v___y_2176_, 3);
v___x_2192_ = lean_task_map(v___f_2102_, v___y_2177_, v___y_2176_, v___x_2099_);
lean_inc_n(v___y_2163_, 3);
lean_inc_n(v___y_2161_, 2);
lean_inc_n(v___y_2165_, 2);
v___x_2193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2193_, 0, v___y_2165_);
lean_ctor_set(v___x_2193_, 1, v___y_2161_);
lean_ctor_set(v___x_2193_, 2, v___y_2163_);
lean_ctor_set(v___x_2193_, 3, v___x_2192_);
v___x_2194_ = lean_task_map(v___f_2103_, v___y_2162_, v___y_2176_, v___x_2099_);
v___x_2195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2195_, 0, v___y_2165_);
lean_ctor_set(v___x_2195_, 1, v___y_2161_);
lean_ctor_set(v___x_2195_, 2, v___y_2163_);
lean_ctor_set(v___x_2195_, 3, v___x_2194_);
v___x_2196_ = lean_task_map(v___f_2104_, v___y_2160_, v___y_2176_, v___x_2099_);
v___x_2197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2165_);
lean_ctor_set(v___x_2197_, 1, v___y_2161_);
lean_ctor_set(v___x_2197_, 2, v___y_2163_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
v___x_2198_ = lean_unsigned_to_nat(3u);
v___x_2199_ = lean_mk_empty_array_with_capacity(v___x_2198_);
v___x_2200_ = lean_array_push(v___x_2199_, v___x_2193_);
v___x_2201_ = lean_array_push(v___x_2200_, v___x_2195_);
v___x_2202_ = lean_array_push(v___x_2201_, v___x_2197_);
v___x_2203_ = l_Array_append___redArg(v___x_2202_, v_snapshotTasks_2175_);
lean_inc_ref(v___y_2157_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___y_2157_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_inc_ref(v___x_2204_);
v___x_2205_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2204_);
v___x_2206_ = lean_box_usize(v___y_2149_);
v___x_2207_ = lean_box(v___x_2099_);
v___x_2208_ = lean_box(v_val_2095_);
v___x_2209_ = lean_box(v___x_2191_);
lean_inc_ref(v_a_2096_);
lean_inc_ref(v___y_2148_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2210_, 0, v___x_2098_);
lean_closure_set(v___f_2210_, 1, v___y_2152_);
lean_closure_set(v___f_2210_, 2, v___y_2150_);
lean_closure_set(v___f_2210_, 3, v___x_2206_);
lean_closure_set(v___f_2210_, 4, v___x_2207_);
lean_closure_set(v___f_2210_, 5, v_env_2170_);
lean_closure_set(v___f_2210_, 6, v___y_2148_);
lean_closure_set(v___f_2210_, 7, v___x_2185_);
lean_closure_set(v___f_2210_, 8, v_a_2096_);
lean_closure_set(v___f_2210_, 9, v_opts_2188_);
lean_closure_set(v___f_2210_, 10, v___x_2204_);
lean_closure_set(v___f_2210_, 11, v_pos_2105_);
lean_closure_set(v___f_2210_, 12, v___x_2208_);
lean_closure_set(v___f_2210_, 13, v___y_2155_);
lean_closure_set(v___f_2210_, 14, v___y_2154_);
lean_closure_set(v___f_2210_, 15, v___y_2151_);
lean_closure_set(v___f_2210_, 16, v___y_2153_);
lean_closure_set(v___f_2210_, 17, v___x_2209_);
v___x_2211_ = lean_io_bind_task(v___x_2205_, v___f_2210_, v___y_2176_, v_val_2095_);
v___y_2116_ = v___y_2157_;
v___y_2117_ = v___y_2166_;
v___y_2118_ = v___y_2158_;
v___y_2119_ = v___y_2159_;
v___y_2120_ = v___y_2163_;
v___y_2121_ = v___y_2169_;
v_snapshotTasks_2122_ = v_snapshotTasks_2175_;
v___y_2123_ = v___y_2164_;
v_traceTask_2124_ = v___x_2211_;
goto v___jp_2115_;
}
}
}
v___jp_2212_:
{
lean_object* v_env_2238_; lean_object* v_messages_2239_; lean_object* v_scopes_2240_; lean_object* v_infoState_2241_; lean_object* v_traceState_2242_; lean_object* v_snapshotTasks_2243_; 
v_env_2238_ = lean_ctor_get(v___y_2234_, 0);
lean_inc_ref(v_env_2238_);
v_messages_2239_ = lean_ctor_get(v___y_2234_, 1);
lean_inc_ref(v_messages_2239_);
v_scopes_2240_ = lean_ctor_get(v___y_2234_, 2);
lean_inc(v_scopes_2240_);
v_infoState_2241_ = lean_ctor_get(v___y_2234_, 8);
lean_inc_ref(v_infoState_2241_);
v_traceState_2242_ = lean_ctor_get(v___y_2234_, 9);
lean_inc_ref(v_traceState_2242_);
v_snapshotTasks_2243_ = lean_ctor_get(v___y_2234_, 10);
lean_inc_ref(v_snapshotTasks_2243_);
v___y_2148_ = v___y_2213_;
v___y_2149_ = v___y_2214_;
v___y_2150_ = v___y_2215_;
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
v___y_2164_ = v___y_2229_;
v___y_2165_ = v___y_2230_;
v___y_2166_ = v___y_2231_;
v___y_2167_ = v___y_2232_;
v___y_2168_ = v___y_2233_;
v___y_2169_ = v___y_2234_;
v_env_2170_ = v_env_2238_;
v_messages_2171_ = v_messages_2239_;
v_scopes_2172_ = v_scopes_2240_;
v_infoState_2173_ = v_infoState_2241_;
v_traceState_2174_ = v_traceState_2242_;
v_snapshotTasks_2175_ = v_snapshotTasks_2243_;
v___y_2176_ = v___y_2235_;
v___y_2177_ = v___y_2236_;
v_reportedCmdState_2178_ = v_reportedCmdState_2237_;
goto v___jp_2147_;
}
v___jp_2245_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; uint8_t v___x_2277_; 
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___y_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2111_);
lean_inc_ref(v___y_2265_);
lean_inc_n(v_pos_2105_, 2);
lean_inc_ref(v_cmds_2092_);
lean_inc(v_fst_2093_);
v___x_2273_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2093_, v_cmds_2092_, v_cmdState_2106_, v_pos_2105_, v___x_2272_, v___y_2265_, v_a_2096_);
v___x_2274_ = lean_box(v_val_2095_);
v___x_2275_ = lean_box(v___x_2099_);
lean_inc_ref(v_a_2096_);
lean_inc(v___y_2248_);
lean_inc_ref(v___x_2101_);
lean_inc_ref(v___x_2273_);
lean_inc_ref(v___y_2246_);
lean_inc_ref(v___y_2253_);
v___f_2276_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 12, 10);
lean_closure_set(v___f_2276_, 0, v___y_2253_);
lean_closure_set(v___f_2276_, 1, v___y_2246_);
lean_closure_set(v___f_2276_, 2, v___x_2274_);
lean_closure_set(v___f_2276_, 3, v___x_2113_);
lean_closure_set(v___f_2276_, 4, v___x_2273_);
lean_closure_set(v___f_2276_, 5, v___x_2101_);
lean_closure_set(v___f_2276_, 6, v___y_2248_);
lean_closure_set(v___f_2276_, 7, v___x_2275_);
lean_closure_set(v___f_2276_, 8, v_a_2096_);
lean_closure_set(v___f_2276_, 9, v_pos_2105_);
v___x_2277_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2107_, v___x_2244_);
if (v___x_2277_ == 0)
{
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2273_);
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2254_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2261_;
v___y_2228_ = v___y_2260_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2264_;
v___y_2231_ = v___y_2265_;
v___y_2232_ = v___y_2266_;
v___y_2233_ = v___f_2276_;
v___y_2234_ = v___x_2273_;
v___y_2235_ = v___y_2267_;
v___y_2236_ = v___y_2269_;
v_reportedCmdState_2237_ = v___x_2273_;
goto v___jp_2212_;
}
else
{
uint8_t v___x_2278_; 
lean_inc(v_fst_2093_);
v___x_2278_ = l_Lean_Parser_isTerminalCommand(v_fst_2093_);
if (v___x_2278_ == 0)
{
if (v___x_2277_ == 0)
{
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2273_);
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2254_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2261_;
v___y_2228_ = v___y_2260_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2264_;
v___y_2231_ = v___y_2265_;
v___y_2232_ = v___y_2266_;
v___y_2233_ = v___f_2276_;
v___y_2234_ = v___x_2273_;
v___y_2235_ = v___y_2267_;
v___y_2236_ = v___y_2269_;
v_reportedCmdState_2237_ = v___x_2273_;
goto v___jp_2212_;
}
else
{
lean_object* v_env_2279_; lean_object* v_messages_2280_; lean_object* v_scopes_2281_; lean_object* v_infoState_2282_; lean_object* v_traceState_2283_; lean_object* v_snapshotTasks_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_env_2279_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_ref_n(v_env_2279_, 2);
v_messages_2280_ = lean_ctor_get(v___x_2273_, 1);
lean_inc_ref(v_messages_2280_);
v_scopes_2281_ = lean_ctor_get(v___x_2273_, 2);
lean_inc(v_scopes_2281_);
v_infoState_2282_ = lean_ctor_get(v___x_2273_, 8);
lean_inc_ref(v_infoState_2282_);
v_traceState_2283_ = lean_ctor_get(v___x_2273_, 9);
lean_inc_ref(v_traceState_2283_);
v_snapshotTasks_2284_ = lean_ctor_get(v___x_2273_, 10);
lean_inc_ref(v_snapshotTasks_2284_);
v___x_2285_ = lean_mk_empty_array_with_capacity(v___y_2262_);
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2285_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_inc_n(v___y_2267_, 3);
v___x_2287_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___x_2285_);
lean_ctor_set(v___x_2287_, 2, v___y_2267_);
lean_ctor_set(v___x_2287_, 3, v___y_2267_);
lean_ctor_set_usize(v___x_2287_, 4, v___y_2270_);
v___x_2288_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2287_, 2);
v___x_2289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2287_);
lean_ctor_set(v___x_2289_, 2, v___x_2288_);
v___x_2290_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2291_ = l_Lean_Options_empty;
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_mk_empty_array_with_capacity(v___y_2267_);
lean_inc_ref_n(v___x_2293_, 2);
lean_inc_n(v___x_2098_, 2);
v___x_2294_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2294_, 0, v___x_2290_);
lean_ctor_set(v___x_2294_, 1, v___x_2291_);
lean_ctor_set(v___x_2294_, 2, v___x_2098_);
lean_ctor_set(v___x_2294_, 3, v___x_2292_);
lean_ctor_set(v___x_2294_, 4, v___x_2292_);
lean_ctor_set(v___x_2294_, 5, v___x_2293_);
lean_ctor_set(v___x_2294_, 6, v___x_2293_);
lean_ctor_set(v___x_2294_, 7, v___x_2292_);
lean_ctor_set(v___x_2294_, 8, v___x_2292_);
lean_ctor_set(v___x_2294_, 9, v___x_2292_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*10, v_val_2095_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*10 + 1, v_val_2095_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*10 + 2, v_val_2095_);
v___x_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v___x_2292_);
v___x_2296_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2297_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2298_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2098_);
v___x_2299_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2300_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
lean_ctor_set(v___x_2300_, 2, v___x_2287_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*3, v___x_2099_);
lean_inc_ref(v___y_2268_);
v___x_2301_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2301_, 0, v_env_2279_);
lean_ctor_set(v___x_2301_, 1, v___x_2289_);
lean_ctor_set(v___x_2301_, 2, v___x_2295_);
lean_ctor_set(v___x_2301_, 3, v___x_2288_);
lean_ctor_set(v___x_2301_, 4, v___x_2296_);
lean_ctor_set(v___x_2301_, 5, v___y_2267_);
lean_ctor_set(v___x_2301_, 6, v___x_2297_);
lean_ctor_set(v___x_2301_, 7, v___x_2298_);
lean_ctor_set(v___x_2301_, 8, v___x_2300_);
lean_ctor_set(v___x_2301_, 9, v___y_2268_);
lean_ctor_set(v___x_2301_, 10, v___x_2293_);
v___y_2148_ = v___y_2246_;
v___y_2149_ = v___y_2247_;
v___y_2150_ = v___y_2248_;
v___y_2151_ = v___y_2249_;
v___y_2152_ = v___y_2250_;
v___y_2153_ = v___y_2251_;
v___y_2154_ = v___y_2252_;
v___y_2155_ = v___y_2253_;
v___y_2156_ = v___y_2255_;
v___y_2157_ = v___y_2254_;
v___y_2158_ = v___y_2256_;
v___y_2159_ = v___y_2257_;
v___y_2160_ = v___y_2258_;
v___y_2161_ = v___y_2259_;
v___y_2162_ = v___y_2261_;
v___y_2163_ = v___y_2260_;
v___y_2164_ = v___y_2263_;
v___y_2165_ = v___y_2264_;
v___y_2166_ = v___y_2265_;
v___y_2167_ = v___y_2266_;
v___y_2168_ = v___f_2276_;
v___y_2169_ = v___x_2273_;
v_env_2170_ = v_env_2279_;
v_messages_2171_ = v_messages_2280_;
v_scopes_2172_ = v_scopes_2281_;
v_infoState_2173_ = v_infoState_2282_;
v_traceState_2174_ = v_traceState_2283_;
v_snapshotTasks_2175_ = v_snapshotTasks_2284_;
v___y_2176_ = v___y_2267_;
v___y_2177_ = v___y_2269_;
v_reportedCmdState_2178_ = v___x_2301_;
goto v___jp_2147_;
}
}
else
{
lean_dec(v___y_2262_);
lean_inc_ref(v___x_2273_);
v___y_2213_ = v___y_2246_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2252_;
v___y_2220_ = v___y_2253_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2254_;
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2261_;
v___y_2228_ = v___y_2260_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2264_;
v___y_2231_ = v___y_2265_;
v___y_2232_ = v___y_2266_;
v___y_2233_ = v___f_2276_;
v___y_2234_ = v___x_2273_;
v___y_2235_ = v___y_2267_;
v___y_2236_ = v___y_2269_;
v_reportedCmdState_2237_ = v___x_2273_;
goto v___jp_2212_;
}
}
}
v___jp_2302_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; size_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2308_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2097_);
v___x_2309_ = l_IO_CancelToken_new();
v___x_2310_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2098_);
v___x_2311_ = l_Lean_Name_str___override(v___x_2098_, v___x_2310_);
v___x_2312_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2313_ = l_Lean_Name_str___override(v___x_2311_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2315_ = l_Lean_Name_str___override(v___x_2313_, v___x_2314_);
v___x_2316_ = l_Lean_Name_str___override(v___x_2315_, v___x_2312_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = l_Lean_Name_num___override(v___x_2316_, v___x_2317_);
v___x_2319_ = l_Lean_Name_str___override(v___x_2318_, v___x_2312_);
v___x_2320_ = l_Lean_Name_str___override(v___x_2319_, v___x_2314_);
v___x_2321_ = l_Lean_Name_str___override(v___x_2320_, v___x_2312_);
v___x_2322_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2323_ = l_Lean_Name_str___override(v___x_2321_, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2325_ = l_Lean_Name_str___override(v___x_2323_, v___x_2324_);
v___x_2326_ = l_Lean_Name_toString(v___x_2325_, v___x_2099_);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_unsigned_to_nat(32u);
v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2328_);
lean_dec_ref(v___x_2329_);
v___x_2330_ = ((size_t)5ULL);
v___x_2331_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2326_, 2);
v___x_2332_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2326_);
lean_ctor_set(v___x_2332_, 1, v___x_2308_);
lean_ctor_set(v___x_2332_, 2, v___x_2327_);
lean_ctor_set(v___x_2332_, 3, v___x_2331_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*4, v_val_2095_);
v___x_2333_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2334_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2334_, 0, v___x_2326_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
lean_ctor_set(v___x_2334_, 2, v___x_2327_);
lean_ctor_set(v___x_2334_, 3, v___x_2331_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*4, v_val_2095_);
lean_inc(v___y_2305_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___y_2305_);
v___x_2336_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2335_);
lean_inc_ref(v___x_2309_);
v___x_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2309_);
v___x_2338_ = l_IO_Promise_result_x21___redArg(v___x_2111_);
lean_inc_ref(v___x_2338_);
lean_inc(v___x_2336_);
lean_inc_ref_n(v___x_2335_, 3);
v___x_2339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2335_);
lean_ctor_set(v___x_2339_, 1, v___x_2336_);
lean_ctor_set(v___x_2339_, 2, v___x_2337_);
lean_ctor_set(v___x_2339_, 3, v___x_2338_);
v___x_2340_ = l_IO_Promise_result_x21___redArg(v___x_2112_);
lean_inc_ref(v___x_2340_);
lean_inc_n(v___y_2306_, 3);
v___x_2341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2335_);
lean_ctor_set(v___x_2341_, 1, v___y_2306_);
lean_ctor_set(v___x_2341_, 2, v___x_2327_);
lean_ctor_set(v___x_2341_, 3, v___x_2340_);
v___x_2342_ = l_IO_Promise_result_x21___redArg(v___x_2113_);
lean_inc_ref(v___x_2342_);
v___x_2343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2335_);
lean_ctor_set(v___x_2343_, 1, v___y_2306_);
lean_ctor_set(v___x_2343_, 2, v___x_2327_);
lean_ctor_set(v___x_2343_, 3, v___x_2342_);
v___x_2344_ = l_IO_Promise_result_x21___redArg(v___x_2114_);
v___x_2345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2327_);
lean_ctor_set(v___x_2345_, 1, v___y_2306_);
lean_ctor_set(v___x_2345_, 2, v___x_2327_);
lean_ctor_set(v___x_2345_, 3, v___x_2344_);
lean_inc_ref(v___x_2334_);
v___x_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2334_);
lean_ctor_set(v___x_2346_, 1, v___x_2339_);
lean_ctor_set(v___x_2346_, 2, v___x_2341_);
lean_ctor_set(v___x_2346_, 3, v___x_2343_);
lean_ctor_set(v___x_2346_, 4, v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2332_);
lean_ctor_set(v___x_2347_, 1, v___y_2305_);
lean_ctor_set(v___x_2347_, 2, v___y_2304_);
lean_ctor_set(v___x_2347_, 3, v___x_2346_);
lean_ctor_set(v___x_2347_, 4, v___y_2307_);
v___x_2348_ = lean_io_promise_resolve(v___x_2347_, v_prom_2100_);
if (lean_obj_tag(v_old_x3f_2108_) == 0)
{
lean_inc_ref(v___x_2326_);
lean_inc_ref(v___x_2334_);
v___y_2246_ = v___x_2331_;
v___y_2247_ = v___x_2330_;
v___y_2248_ = v___x_2317_;
v___y_2249_ = v___x_2334_;
v___y_2250_ = v___x_2328_;
v___y_2251_ = v___x_2327_;
v___y_2252_ = v___x_2327_;
v___y_2253_ = v___x_2326_;
v___y_2254_ = v___x_2334_;
v___y_2255_ = v___x_2326_;
v___y_2256_ = v___y_2303_;
v___y_2257_ = v___x_2327_;
v___y_2258_ = v___x_2342_;
v___y_2259_ = v___x_2336_;
v___y_2260_ = v___x_2327_;
v___y_2261_ = v___x_2340_;
v___y_2262_ = v___x_2328_;
v___y_2263_ = v___y_2306_;
v___y_2264_ = v___x_2335_;
v___y_2265_ = v___x_2309_;
v___y_2266_ = v___x_2327_;
v___y_2267_ = v___x_2317_;
v___y_2268_ = v___x_2331_;
v___y_2269_ = v___x_2338_;
v___y_2270_ = v___x_2330_;
v___y_2271_ = v___x_2327_;
goto v___jp_2245_;
}
else
{
lean_object* v_val_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2360_; 
v_val_2349_ = lean_ctor_get(v_old_x3f_2108_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_old_x3f_2108_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2351_ = v_old_x3f_2108_;
v_isShared_2352_ = v_isSharedCheck_2360_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_val_2349_);
lean_dec(v_old_x3f_2108_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2360_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_elabSnap_2353_; lean_object* v_stx_2354_; lean_object* v_elabSnap_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v_elabSnap_2353_ = lean_ctor_get(v_val_2349_, 3);
lean_inc_ref(v_elabSnap_2353_);
v_stx_2354_ = lean_ctor_get(v_val_2349_, 1);
lean_inc(v_stx_2354_);
lean_dec(v_val_2349_);
v_elabSnap_2355_ = lean_ctor_get(v_elabSnap_2353_, 1);
lean_inc_ref(v_elabSnap_2355_);
lean_dec_ref(v_elabSnap_2353_);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v_stx_2354_);
lean_ctor_set(v___x_2356_, 1, v_elabSnap_2355_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2356_);
v___x_2358_ = v___x_2351_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_inc_ref(v___x_2326_);
lean_inc_ref(v___x_2334_);
v___y_2246_ = v___x_2331_;
v___y_2247_ = v___x_2330_;
v___y_2248_ = v___x_2317_;
v___y_2249_ = v___x_2334_;
v___y_2250_ = v___x_2328_;
v___y_2251_ = v___x_2327_;
v___y_2252_ = v___x_2327_;
v___y_2253_ = v___x_2326_;
v___y_2254_ = v___x_2334_;
v___y_2255_ = v___x_2326_;
v___y_2256_ = v___y_2303_;
v___y_2257_ = v___x_2327_;
v___y_2258_ = v___x_2342_;
v___y_2259_ = v___x_2336_;
v___y_2260_ = v___x_2327_;
v___y_2261_ = v___x_2340_;
v___y_2262_ = v___x_2328_;
v___y_2263_ = v___y_2306_;
v___y_2264_ = v___x_2335_;
v___y_2265_ = v___x_2309_;
v___y_2266_ = v___x_2327_;
v___y_2267_ = v___x_2317_;
v___y_2268_ = v___x_2331_;
v___y_2269_ = v___x_2338_;
v___y_2270_ = v___x_2330_;
v___y_2271_ = v___x_2358_;
goto v___jp_2245_;
}
}
}
}
v___jp_2361_:
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2364_);
lean_inc(v_fst_2093_);
v___x_2366_ = l_Lean_Parser_isTerminalCommand(v_fst_2093_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v_toProcessingContext_2368_; lean_object* v_pos_2369_; lean_object* v_endPos_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2367_ = lean_io_promise_new();
v_toProcessingContext_2368_ = lean_ctor_get(v_a_2096_, 0);
v_pos_2369_ = lean_ctor_get(v_fst_2094_, 0);
v_endPos_2370_ = lean_ctor_get(v_toProcessingContext_2368_, 3);
lean_inc(v___x_2367_);
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2367_);
v___x_2372_ = lean_box(0);
lean_inc(v_endPos_2370_);
lean_inc(v_pos_2369_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_pos_2369_);
lean_ctor_set(v___x_2373_, 1, v_endPos_2370_);
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_parseCancelTk_2109_);
v___x_2376_ = l_IO_Promise_result_x21___redArg(v___x_2367_);
lean_dec(v___x_2367_);
v___x_2377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2372_);
lean_ctor_set(v___x_2377_, 1, v___x_2374_);
lean_ctor_set(v___x_2377_, 2, v___x_2375_);
lean_ctor_set(v___x_2377_, 3, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___y_2303_ = v___x_2371_;
v___y_2304_ = v___y_2362_;
v___y_2305_ = v___y_2363_;
v___y_2306_ = v___x_2365_;
v___y_2307_ = v___x_2378_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2379_; 
lean_dec_ref(v_parseCancelTk_2109_);
v___x_2379_ = lean_box(0);
v___y_2303_ = v___x_2379_;
v___y_2304_ = v___y_2362_;
v___y_2305_ = v___y_2363_;
v___y_2306_ = v___x_2365_;
v___y_2307_ = v___x_2379_;
goto v___jp_2302_;
}
}
v___jp_2380_:
{
lean_object* v___x_2383_; 
lean_inc(v_fst_2093_);
v___x_2383_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2093_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_box(0);
v___y_2362_ = v_snd_2382_;
v___y_2363_ = v_fst_2381_;
v___y_2364_ = v___x_2384_;
goto v___jp_2361_;
}
else
{
lean_object* v_val_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
v_val_2385_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2387_ = v___x_2383_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_val_2385_);
lean_dec(v___x_2383_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_inc(v_val_2385_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_val_2385_);
lean_ctor_set(v___x_2389_, 1, v_val_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2389_);
v___x_2391_ = v___x_2387_;
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
v___y_2362_ = v_snd_2382_;
v___y_2363_ = v_fst_2381_;
v___y_2364_ = v___x_2391_;
goto v___jp_2361_;
}
}
}
}
v___jp_2394_:
{
if (v___y_2395_ == 0)
{
lean_inc_ref(v_fst_2094_);
lean_inc(v_fst_2093_);
v_fst_2381_ = v_fst_2093_;
v_snd_2382_ = v_fst_2094_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_box(0);
v___x_2397_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2381_ = v___x_2396_;
v_snd_2382_ = v___x_2397_;
goto v___jp_2380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_cmds_2400_ = _args[0];
lean_object* v_fst_2401_ = _args[1];
lean_object* v_fst_2402_ = _args[2];
lean_object* v_val_2403_ = _args[3];
lean_object* v_a_2404_ = _args[4];
lean_object* v_snd_2405_ = _args[5];
lean_object* v___x_2406_ = _args[6];
lean_object* v___x_2407_ = _args[7];
lean_object* v_prom_2408_ = _args[8];
lean_object* v___x_2409_ = _args[9];
lean_object* v___f_2410_ = _args[10];
lean_object* v___f_2411_ = _args[11];
lean_object* v___f_2412_ = _args[12];
lean_object* v_pos_2413_ = _args[13];
lean_object* v_cmdState_2414_ = _args[14];
lean_object* v_opts_2415_ = _args[15];
lean_object* v_old_x3f_2416_ = _args[16];
lean_object* v_parseCancelTk_2417_ = _args[17];
lean_object* v___y_2418_ = _args[18];
_start:
{
uint8_t v_val_45485__boxed_2419_; uint8_t v___x_45488__boxed_2420_; lean_object* v_res_2421_; 
v_val_45485__boxed_2419_ = lean_unbox(v_val_2403_);
v___x_45488__boxed_2420_ = lean_unbox(v___x_2407_);
v_res_2421_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_cmds_2400_, v_fst_2401_, v_fst_2402_, v_val_45485__boxed_2419_, v_a_2404_, v_snd_2405_, v___x_2406_, v___x_45488__boxed_2420_, v_prom_2408_, v___x_2409_, v___f_2410_, v___f_2411_, v___f_2412_, v_pos_2413_, v_cmdState_2414_, v_opts_2415_, v_old_x3f_2416_, v_parseCancelTk_2417_);
lean_dec_ref(v_opts_2415_);
lean_dec(v_prom_2408_);
lean_dec_ref(v_a_2404_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2424_, lean_object* v_parserState_2425_, lean_object* v_cmdState_2426_, lean_object* v_prom_2427_, uint8_t v_sync_2428_, lean_object* v_parseCancelTk_2429_, lean_object* v_cmds_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_toSnapshot_2434_; lean_object* v_stx_2435_; lean_object* v_parserState_2436_; lean_object* v_elabSnap_2437_; lean_object* v_val_2438_; lean_object* v_newParserState_2439_; lean_object* v___y_2473_; lean_object* v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2477_; lean_object* v___y_2511_; lean_object* v___y_2512_; uint8_t v___y_2513_; lean_object* v___y_2514_; lean_object* v___f_2515_; lean_object* v___f_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; uint8_t v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; uint8_t v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; uint8_t v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; uint8_t v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; uint8_t v___y_2588_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; 
v___f_2515_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2516_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2517_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2518_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2424_) == 1)
{
lean_object* v_val_2663_; lean_object* v_nextCmdSnap_x3f_2664_; 
v_val_2663_ = lean_ctor_get(v_old_x3f_2424_, 0);
v_nextCmdSnap_x3f_2664_ = lean_ctor_get(v_val_2663_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2664_) == 0)
{
goto v___jp_2630_;
}
else
{
lean_object* v_toSnapshot_2665_; lean_object* v_stx_2666_; lean_object* v_parserState_2667_; lean_object* v_elabSnap_2668_; lean_object* v_val_2669_; lean_object* v___x_2670_; 
v_toSnapshot_2665_ = lean_ctor_get(v_val_2663_, 0);
v_stx_2666_ = lean_ctor_get(v_val_2663_, 1);
v_parserState_2667_ = lean_ctor_get(v_val_2663_, 2);
v_elabSnap_2668_ = lean_ctor_get(v_val_2663_, 3);
v_val_2669_ = lean_ctor_get(v_nextCmdSnap_x3f_2664_, 0);
lean_inc(v_val_2669_);
v___x_2670_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2669_);
if (lean_obj_tag(v___x_2670_) == 1)
{
lean_object* v_val_2671_; lean_object* v_nextCmdSnap_x3f_2672_; 
v_val_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_val_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v_nextCmdSnap_x3f_2672_ = lean_ctor_get(v_val_2671_, 4);
lean_inc(v_nextCmdSnap_x3f_2672_);
lean_dec(v_val_2671_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2672_) == 0)
{
goto v___jp_2630_;
}
else
{
lean_object* v_val_2673_; lean_object* v___x_2674_; 
v_val_2673_ = lean_ctor_get(v_nextCmdSnap_x3f_2672_, 0);
lean_inc(v_val_2673_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2672_, 1);
v___x_2674_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2673_);
if (lean_obj_tag(v___x_2674_) == 1)
{
lean_object* v_val_2675_; lean_object* v_parserState_2676_; lean_object* v_pos_2677_; uint8_t v___x_2678_; 
v_val_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v_parserState_2676_ = lean_ctor_get(v_val_2675_, 2);
lean_inc_ref(v_parserState_2676_);
lean_dec(v_val_2675_);
v_pos_2677_ = lean_ctor_get(v_parserState_2676_, 0);
lean_inc(v_pos_2677_);
lean_dec_ref(v_parserState_2676_);
v___x_2678_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2677_, v_a_2431_);
lean_dec(v_pos_2677_);
if (v___x_2678_ == 0)
{
goto v___jp_2630_;
}
else
{
lean_inc(v_val_2669_);
lean_inc_ref(v_elabSnap_2668_);
lean_inc_ref_n(v_parserState_2667_, 2);
lean_inc(v_stx_2666_);
lean_inc_ref(v_toSnapshot_2665_);
lean_dec_ref_known(v_old_x3f_2424_, 1);
lean_dec_ref(v_parseCancelTk_2429_);
lean_dec_ref(v_cmdState_2426_);
lean_dec_ref(v_parserState_2425_);
v_toSnapshot_2434_ = v_toSnapshot_2665_;
v_stx_2435_ = v_stx_2666_;
v_parserState_2436_ = v_parserState_2667_;
v_elabSnap_2437_ = v_elabSnap_2668_;
v_val_2438_ = v_val_2669_;
v_newParserState_2439_ = v_parserState_2667_;
goto v___jp_2433_;
}
}
else
{
lean_dec(v___x_2674_);
goto v___jp_2630_;
}
}
}
else
{
lean_dec(v___x_2670_);
goto v___jp_2630_;
}
}
}
else
{
goto v___jp_2630_;
}
v___jp_2433_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_resultSnap_2442_; lean_object* v_task_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2466_; 
v___x_2440_ = lean_io_promise_new();
v___x_2441_ = l_IO_CancelToken_new();
v_resultSnap_2442_ = lean_ctor_get(v_elabSnap_2437_, 2);
lean_inc_ref(v_resultSnap_2442_);
v_task_2443_ = lean_ctor_get(v_resultSnap_2442_, 3);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_resultSnap_2442_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; 
v_unused_2467_ = lean_ctor_get(v_resultSnap_2442_, 2);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v_resultSnap_2442_, 1);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_resultSnap_2442_, 0);
lean_dec(v_unused_2469_);
v___x_2445_ = v_resultSnap_2442_;
v_isShared_2446_ = v_isSharedCheck_2466_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_task_2443_);
lean_dec(v_resultSnap_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2466_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v_toProcessingContext_2452_; lean_object* v_pos_2453_; lean_object* v_endPos_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2447_ = lean_box(v_sync_2428_);
lean_inc_ref(v_a_2431_);
lean_inc_ref(v___x_2441_);
lean_inc(v___x_2440_);
lean_inc_ref(v_newParserState_2439_);
lean_inc(v_stx_2435_);
v___f_2448_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2448_, 0, v_val_2438_);
lean_closure_set(v___f_2448_, 1, v_cmds_2430_);
lean_closure_set(v___f_2448_, 2, v_stx_2435_);
lean_closure_set(v___f_2448_, 3, v_newParserState_2439_);
lean_closure_set(v___f_2448_, 4, v___x_2440_);
lean_closure_set(v___f_2448_, 5, v___x_2447_);
lean_closure_set(v___f_2448_, 6, v___x_2441_);
lean_closure_set(v___f_2448_, 7, v_a_2431_);
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = 1;
v___x_2451_ = l_BaseIO_chainTask___redArg(v_task_2443_, v___f_2448_, v___x_2449_, v___x_2450_);
v_toProcessingContext_2452_ = lean_ctor_get(v_a_2431_, 0);
v_pos_2453_ = lean_ctor_get(v_newParserState_2439_, 0);
lean_inc(v_pos_2453_);
lean_dec_ref(v_newParserState_2439_);
v_endPos_2454_ = lean_ctor_get(v_toProcessingContext_2452_, 3);
v___x_2455_ = lean_box(0);
lean_inc(v_endPos_2454_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_pos_2453_);
lean_ctor_set(v___x_2456_, 1, v_endPos_2454_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2441_);
v___x_2459_ = l_IO_Promise_result_x21___redArg(v___x_2440_);
lean_dec(v___x_2440_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 3, v___x_2459_);
lean_ctor_set(v___x_2445_, 2, v___x_2458_);
lean_ctor_set(v___x_2445_, 1, v___x_2457_);
lean_ctor_set(v___x_2445_, 0, v___x_2455_);
v___x_2461_ = v___x_2445_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2463_, 0, v_toSnapshot_2434_);
lean_ctor_set(v___x_2463_, 1, v_stx_2435_);
lean_ctor_set(v___x_2463_, 2, v_parserState_2436_);
lean_ctor_set(v___x_2463_, 3, v_elabSnap_2437_);
lean_ctor_set(v___x_2463_, 4, v___x_2462_);
v___x_2464_ = lean_io_promise_resolve(v___x_2463_, v_prom_2427_);
lean_dec(v_prom_2427_);
return v___x_2464_;
}
}
}
v___jp_2470_:
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_box(0);
return v___x_2471_;
}
v___jp_2472_:
{
goto v___jp_2470_;
}
v___jp_2474_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2478_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2479_ = l_Lean_Name_str___override(v___y_2475_, v___x_2478_);
v___x_2480_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2481_ = l_Lean_Name_str___override(v___x_2479_, v___x_2480_);
v___x_2482_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2483_ = l_Lean_Name_str___override(v___x_2481_, v___x_2482_);
v___x_2484_ = l_Lean_Name_str___override(v___x_2483_, v___x_2480_);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = l_Lean_Name_num___override(v___x_2484_, v___x_2485_);
v___x_2487_ = l_Lean_Name_str___override(v___x_2486_, v___x_2480_);
v___x_2488_ = l_Lean_Name_str___override(v___x_2487_, v___x_2482_);
v___x_2489_ = l_Lean_Name_str___override(v___x_2488_, v___x_2480_);
v___x_2490_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2491_ = l_Lean_Name_str___override(v___x_2489_, v___x_2490_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2493_ = l_Lean_Name_str___override(v___x_2491_, v___x_2492_);
v___x_2494_ = l_Lean_Name_toString(v___x_2493_, v___y_2477_);
v___x_2495_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2498_ = 0;
v___x_2499_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2499_, 0, v___x_2494_);
lean_ctor_set(v___x_2499_, 1, v___x_2495_);
lean_ctor_set(v___x_2499_, 2, v___x_2496_);
lean_ctor_set(v___x_2499_, 3, v___x_2497_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*4, v___x_2498_);
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2499_, 3);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2499_);
lean_ctor_set(v___x_2502_, 1, v_cmdState_2426_);
v___x_2503_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2496_, v___x_2502_);
v___x_2504_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2496_, v___x_2499_);
v___x_2505_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2499_);
lean_ctor_set(v___x_2506_, 1, v___x_2501_);
lean_ctor_set(v___x_2506_, 2, v___x_2503_);
lean_ctor_set(v___x_2506_, 3, v___x_2504_);
lean_ctor_set(v___x_2506_, 4, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2499_);
lean_ctor_set(v___x_2507_, 1, v___x_2500_);
lean_ctor_set(v___x_2507_, 2, v___y_2476_);
lean_ctor_set(v___x_2507_, 3, v___x_2506_);
lean_ctor_set(v___x_2507_, 4, v___x_2496_);
v___x_2508_ = lean_io_promise_resolve(v___x_2507_, v_prom_2427_);
lean_dec(v_prom_2427_);
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
v___jp_2510_:
{
v___y_2475_ = v___y_2511_;
v___y_2476_ = v___y_2512_;
v___y_2477_ = v___y_2513_;
goto v___jp_2474_;
}
v___jp_2519_:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2536_);
v___x_2538_ = l_Lean_Parser_isTerminalCommand(v___y_2525_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_io_promise_new();
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
v___x_2541_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2537_, v___y_2523_, v_cmds_2430_, v___y_2534_, v___y_2531_, v___y_2520_, v_a_2431_, v___y_2533_, v___y_2529_, v___y_2527_, v___y_2530_, v___y_2532_, v___y_2521_, v___y_2526_, v___y_2535_, v_prom_2427_, v___x_2518_, v___f_2515_, v___f_2516_, v___f_2517_, v___y_2522_, v_cmdState_2426_, v___y_2528_, v___y_2524_, v_old_x3f_2424_, v_parseCancelTk_2429_, v___x_2540_);
lean_dec_ref(v___y_2528_);
lean_dec(v_prom_2427_);
lean_dec(v___y_2521_);
lean_dec(v___y_2523_);
v___y_2473_ = v___x_2541_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_box(0);
v___x_2543_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2537_, v___y_2523_, v_cmds_2430_, v___y_2534_, v___y_2531_, v___y_2520_, v_a_2431_, v___y_2533_, v___y_2529_, v___y_2527_, v___y_2530_, v___y_2532_, v___y_2521_, v___y_2526_, v___y_2535_, v_prom_2427_, v___x_2518_, v___f_2515_, v___f_2516_, v___f_2517_, v___y_2522_, v_cmdState_2426_, v___y_2528_, v___y_2524_, v_old_x3f_2424_, v_parseCancelTk_2429_, v___x_2542_);
lean_dec_ref(v___y_2528_);
lean_dec(v_prom_2427_);
lean_dec(v___y_2521_);
lean_dec(v___y_2523_);
v___y_2473_ = v___x_2543_;
goto v___jp_2472_;
}
}
v___jp_2544_:
{
lean_object* v___x_2561_; 
lean_inc(v___y_2558_);
v___x_2561_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2558_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_box(0);
v___y_2520_ = v___y_2545_;
v___y_2521_ = v___y_2546_;
v___y_2522_ = v___y_2547_;
v___y_2523_ = v___y_2548_;
v___y_2524_ = v___y_2549_;
v___y_2525_ = v___y_2558_;
v___y_2526_ = v___y_2550_;
v___y_2527_ = v___y_2551_;
v___y_2528_ = v___y_2552_;
v___y_2529_ = v___y_2553_;
v___y_2530_ = v_fst_2559_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2555_;
v___y_2533_ = v___y_2556_;
v___y_2534_ = v___y_2557_;
v___y_2535_ = v_snd_2560_;
v___y_2536_ = v___x_2562_;
goto v___jp_2519_;
}
else
{
lean_object* v_val_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2571_; 
v_val_2563_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2565_ = v___x_2561_;
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_val_2563_);
lean_dec(v___x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_inc(v_val_2563_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_val_2563_);
lean_ctor_set(v___x_2567_, 1, v_val_2563_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
v___y_2520_ = v___y_2545_;
v___y_2521_ = v___y_2546_;
v___y_2522_ = v___y_2547_;
v___y_2523_ = v___y_2548_;
v___y_2524_ = v___y_2549_;
v___y_2525_ = v___y_2558_;
v___y_2526_ = v___y_2550_;
v___y_2527_ = v___y_2551_;
v___y_2528_ = v___y_2552_;
v___y_2529_ = v___y_2553_;
v___y_2530_ = v_fst_2559_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2555_;
v___y_2533_ = v___y_2556_;
v___y_2534_ = v___y_2557_;
v___y_2535_ = v_snd_2560_;
v___y_2536_ = v___x_2569_;
goto v___jp_2519_;
}
}
}
}
v___jp_2572_:
{
if (v___y_2588_ == 0)
{
lean_inc(v___y_2587_);
v___y_2545_ = v___y_2573_;
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2577_;
v___y_2550_ = v___y_2578_;
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2580_;
v___y_2553_ = v___y_2581_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v___y_2587_;
v_fst_2559_ = v___y_2587_;
v_snd_2560_ = v___y_2586_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref(v___y_2586_);
v___x_2589_ = lean_box(0);
v___x_2590_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2545_ = v___y_2573_;
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2577_;
v___y_2550_ = v___y_2578_;
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2580_;
v___y_2553_ = v___y_2581_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___y_2584_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v___y_2587_;
v_fst_2559_ = v___x_2589_;
v_snd_2560_ = v___x_2590_;
goto v___jp_2544_;
}
}
v___jp_2591_:
{
uint8_t v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = l_IO_CancelToken_isSet(v_parseCancelTk_2429_);
v___x_2603_ = 1;
if (v___x_2602_ == 0)
{
lean_dec(v___y_2599_);
if (v_sync_2428_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2604_ = lean_io_promise_new();
v___x_2605_ = lean_io_promise_new();
v___x_2606_ = lean_io_promise_new();
v___x_2607_ = lean_io_promise_new();
v___x_2608_ = l_Lean_internal_cmdlineSnapshots;
v___x_2609_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2598_, v___x_2608_);
lean_dec_ref(v___y_2598_);
if (v___x_2609_ == 0)
{
v___y_2573_ = v___x_2602_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___y_2592_;
v___y_2576_ = v___x_2607_;
v___y_2577_ = v___x_2608_;
v___y_2578_ = v___x_2606_;
v___y_2579_ = v___x_2603_;
v___y_2580_ = v___y_2593_;
v___y_2581_ = v___y_2594_;
v___y_2582_ = v___y_2595_;
v___y_2583_ = v___x_2604_;
v___y_2584_ = v___y_2596_;
v___y_2585_ = v___y_2597_;
v___y_2586_ = v___y_2600_;
v___y_2587_ = v___y_2601_;
v___y_2588_ = v___x_2609_;
goto v___jp_2572_;
}
else
{
uint8_t v___x_2610_; 
lean_inc(v___y_2601_);
v___x_2610_ = l_Lean_Parser_isTerminalCommand(v___y_2601_);
if (v___x_2610_ == 0)
{
v___y_2573_ = v___x_2602_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___y_2592_;
v___y_2576_ = v___x_2607_;
v___y_2577_ = v___x_2608_;
v___y_2578_ = v___x_2606_;
v___y_2579_ = v___x_2603_;
v___y_2580_ = v___y_2593_;
v___y_2581_ = v___y_2594_;
v___y_2582_ = v___y_2595_;
v___y_2583_ = v___x_2604_;
v___y_2584_ = v___y_2596_;
v___y_2585_ = v___y_2597_;
v___y_2586_ = v___y_2600_;
v___y_2587_ = v___y_2601_;
v___y_2588_ = v___x_2609_;
goto v___jp_2572_;
}
else
{
lean_inc(v___y_2601_);
v___y_2545_ = v___x_2602_;
v___y_2546_ = v___x_2605_;
v___y_2547_ = v___y_2592_;
v___y_2548_ = v___x_2607_;
v___y_2549_ = v___x_2608_;
v___y_2550_ = v___x_2606_;
v___y_2551_ = v___x_2603_;
v___y_2552_ = v___y_2593_;
v___y_2553_ = v___y_2594_;
v___y_2554_ = v___y_2595_;
v___y_2555_ = v___x_2604_;
v___y_2556_ = v___y_2596_;
v___y_2557_ = v___y_2597_;
v___y_2558_ = v___y_2601_;
v_fst_2559_ = v___y_2601_;
v_snd_2560_ = v___y_2600_;
goto v___jp_2544_;
}
}
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v___y_2598_);
v___x_2611_ = lean_box(v___x_2602_);
v___x_2612_ = lean_box(v___x_2603_);
lean_inc_ref(v_a_2431_);
v___f_2613_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 19, 18);
lean_closure_set(v___f_2613_, 0, v_cmds_2430_);
lean_closure_set(v___f_2613_, 1, v___y_2597_);
lean_closure_set(v___f_2613_, 2, v___y_2595_);
lean_closure_set(v___f_2613_, 3, v___x_2611_);
lean_closure_set(v___f_2613_, 4, v_a_2431_);
lean_closure_set(v___f_2613_, 5, v___y_2596_);
lean_closure_set(v___f_2613_, 6, v___y_2594_);
lean_closure_set(v___f_2613_, 7, v___x_2612_);
lean_closure_set(v___f_2613_, 8, v_prom_2427_);
lean_closure_set(v___f_2613_, 9, v___x_2518_);
lean_closure_set(v___f_2613_, 10, v___f_2515_);
lean_closure_set(v___f_2613_, 11, v___f_2516_);
lean_closure_set(v___f_2613_, 12, v___f_2517_);
lean_closure_set(v___f_2613_, 13, v___y_2592_);
lean_closure_set(v___f_2613_, 14, v_cmdState_2426_);
lean_closure_set(v___f_2613_, 15, v___y_2593_);
lean_closure_set(v___f_2613_, 16, v_old_x3f_2424_);
lean_closure_set(v___f_2613_, 17, v_parseCancelTk_2429_);
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = lean_io_as_task(v___f_2613_, v___x_2614_);
lean_dec_ref(v___x_2615_);
goto v___jp_2470_;
}
}
else
{
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v_cmds_2430_);
lean_dec_ref(v_parseCancelTk_2429_);
if (lean_obj_tag(v_old_x3f_2424_) == 1)
{
lean_object* v_val_2616_; lean_object* v___x_2617_; lean_object* v_children_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_val_2616_ = lean_ctor_get(v_old_x3f_2424_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v_old_x3f_2424_, 1);
v___x_2617_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2616_);
v_children_2618_ = lean_ctor_get(v___x_2617_, 1);
lean_inc_ref(v_children_2618_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = lean_array_get_size(v_children_2618_);
v___x_2621_ = lean_nat_dec_lt(v___x_2619_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_dec_ref(v_children_2618_);
v___y_2475_ = v___y_2599_;
v___y_2476_ = v___y_2600_;
v___y_2477_ = v___x_2603_;
goto v___jp_2474_;
}
else
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_nat_dec_le(v___x_2620_, v___x_2620_);
if (v___x_2623_ == 0)
{
if (v___x_2621_ == 0)
{
lean_dec_ref(v_children_2618_);
v___y_2475_ = v___y_2599_;
v___y_2476_ = v___y_2600_;
v___y_2477_ = v___x_2603_;
goto v___jp_2474_;
}
else
{
size_t v___x_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = lean_usize_of_nat(v___x_2620_);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2618_, v___x_2624_, v___x_2625_, v___x_2622_);
lean_dec_ref(v_children_2618_);
v___y_2511_ = v___y_2599_;
v___y_2512_ = v___y_2600_;
v___y_2513_ = v___x_2603_;
v___y_2514_ = v___x_2626_;
goto v___jp_2510_;
}
}
else
{
size_t v___x_2627_; size_t v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = lean_usize_of_nat(v___x_2620_);
v___x_2629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2618_, v___x_2627_, v___x_2628_, v___x_2622_);
lean_dec_ref(v_children_2618_);
v___y_2511_ = v___y_2599_;
v___y_2512_ = v___y_2600_;
v___y_2513_ = v___x_2603_;
v___y_2514_ = v___x_2629_;
goto v___jp_2510_;
}
}
}
else
{
lean_dec(v_old_x3f_2424_);
v___y_2475_ = v___y_2599_;
v___y_2476_ = v___y_2600_;
v___y_2477_ = v___x_2603_;
goto v___jp_2474_;
}
}
}
v___jp_2630_:
{
lean_object* v_env_2631_; lean_object* v_scopes_2632_; lean_object* v___x_2633_; lean_object* v_opts_2634_; lean_object* v_currNamespace_2635_; lean_object* v_openDecls_2636_; lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_snd_2642_; 
v_env_2631_ = lean_ctor_get(v_cmdState_2426_, 0);
v_scopes_2632_ = lean_ctor_get(v_cmdState_2426_, 2);
v___x_2633_ = l_List_head_x21___redArg(v___x_2518_, v_scopes_2632_);
v_opts_2634_ = lean_ctor_get(v___x_2633_, 1);
lean_inc_ref_n(v_opts_2634_, 2);
v_currNamespace_2635_ = lean_ctor_get(v___x_2633_, 2);
lean_inc(v_currNamespace_2635_);
v_openDecls_2636_ = lean_ctor_get(v___x_2633_, 3);
lean_inc(v_openDecls_2636_);
lean_dec(v___x_2633_);
lean_inc_ref(v_env_2631_);
v___x_2637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2637_, 0, v_env_2631_);
lean_ctor_set(v___x_2637_, 1, v_opts_2634_);
lean_ctor_set(v___x_2637_, 2, v_currNamespace_2635_);
lean_ctor_set(v___x_2637_, 3, v_openDecls_2636_);
lean_inc_ref(v_parserState_2425_);
lean_inc_ref(v_a_2431_);
v___f_2638_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2638_, 0, v_a_2431_);
lean_closure_set(v___f_2638_, 1, v___x_2637_);
lean_closure_set(v___f_2638_, 2, v_parserState_2425_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_profileit(v___x_2639_, v_opts_2634_, v___f_2638_, v___x_2640_);
v_snd_2642_ = lean_ctor_get(v___x_2641_, 1);
lean_inc(v_snd_2642_);
if (lean_obj_tag(v_old_x3f_2424_) == 1)
{
lean_object* v_val_2643_; lean_object* v_fst_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v_pos_2647_; lean_object* v_toSnapshot_2648_; lean_object* v_stx_2649_; lean_object* v_parserState_2650_; lean_object* v_elabSnap_2651_; lean_object* v_nextCmdSnap_x3f_2652_; uint8_t v___x_2653_; 
v_val_2643_ = lean_ctor_get(v_old_x3f_2424_, 0);
v_fst_2644_ = lean_ctor_get(v___x_2641_, 0);
lean_inc_n(v_fst_2644_, 2);
lean_dec(v___x_2641_);
v_fst_2645_ = lean_ctor_get(v_snd_2642_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v_snd_2642_, 1);
lean_inc(v_snd_2646_);
lean_dec(v_snd_2642_);
v_pos_2647_ = lean_ctor_get(v_parserState_2425_, 0);
lean_inc(v_pos_2647_);
lean_dec_ref(v_parserState_2425_);
v_toSnapshot_2648_ = lean_ctor_get(v_val_2643_, 0);
v_stx_2649_ = lean_ctor_get(v_val_2643_, 1);
v_parserState_2650_ = lean_ctor_get(v_val_2643_, 2);
v_elabSnap_2651_ = lean_ctor_get(v_val_2643_, 3);
v_nextCmdSnap_x3f_2652_ = lean_ctor_get(v_val_2643_, 4);
lean_inc(v_stx_2649_);
v___x_2653_ = l_Lean_Syntax_eqWithInfo(v_fst_2644_, v_stx_2649_);
if (v___x_2653_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2652_) == 0)
{
lean_inc(v_fst_2644_);
lean_inc(v_fst_2645_);
lean_inc_ref(v_opts_2634_);
v___y_2592_ = v_pos_2647_;
v___y_2593_ = v_opts_2634_;
v___y_2594_ = v___x_2640_;
v___y_2595_ = v_fst_2645_;
v___y_2596_ = v_snd_2646_;
v___y_2597_ = v_fst_2644_;
v___y_2598_ = v_opts_2634_;
v___y_2599_ = v___x_2640_;
v___y_2600_ = v_fst_2645_;
v___y_2601_ = v_fst_2644_;
goto v___jp_2591_;
}
else
{
lean_object* v_val_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_val_2654_ = lean_ctor_get(v_nextCmdSnap_x3f_2652_, 0);
v___x_2655_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2654_);
v___x_2656_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2655_, v_val_2654_);
lean_inc(v_fst_2644_);
lean_inc(v_fst_2645_);
lean_inc_ref(v_opts_2634_);
v___y_2592_ = v_pos_2647_;
v___y_2593_ = v_opts_2634_;
v___y_2594_ = v___x_2640_;
v___y_2595_ = v_fst_2645_;
v___y_2596_ = v_snd_2646_;
v___y_2597_ = v_fst_2644_;
v___y_2598_ = v_opts_2634_;
v___y_2599_ = v___x_2640_;
v___y_2600_ = v_fst_2645_;
v___y_2601_ = v_fst_2644_;
goto v___jp_2591_;
}
}
else
{
lean_inc(v_val_2643_);
lean_dec(v_pos_2647_);
lean_dec(v_snd_2646_);
lean_dec(v_fst_2644_);
lean_dec_ref_known(v_old_x3f_2424_, 1);
lean_dec_ref(v_opts_2634_);
lean_dec_ref(v_parseCancelTk_2429_);
lean_dec_ref(v_cmdState_2426_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2652_) == 1)
{
lean_object* v_val_2657_; 
lean_inc_ref(v_nextCmdSnap_x3f_2652_);
lean_inc_ref(v_elabSnap_2651_);
lean_inc_ref(v_parserState_2650_);
lean_inc(v_stx_2649_);
lean_inc_ref(v_toSnapshot_2648_);
lean_dec(v_val_2643_);
v_val_2657_ = lean_ctor_get(v_nextCmdSnap_x3f_2652_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2652_, 1);
v_toSnapshot_2434_ = v_toSnapshot_2648_;
v_stx_2435_ = v_stx_2649_;
v_parserState_2436_ = v_parserState_2650_;
v_elabSnap_2437_ = v_elabSnap_2651_;
v_val_2438_ = v_val_2657_;
v_newParserState_2439_ = v_fst_2645_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2658_; 
lean_dec(v_fst_2645_);
lean_dec_ref(v_cmds_2430_);
v___x_2658_ = lean_io_promise_resolve(v_val_2643_, v_prom_2427_);
lean_dec(v_prom_2427_);
return v___x_2658_;
}
}
}
else
{
lean_object* v_fst_2659_; lean_object* v_fst_2660_; lean_object* v_snd_2661_; lean_object* v_pos_2662_; 
v_fst_2659_ = lean_ctor_get(v___x_2641_, 0);
lean_inc_n(v_fst_2659_, 2);
lean_dec(v___x_2641_);
v_fst_2660_ = lean_ctor_get(v_snd_2642_, 0);
lean_inc_n(v_fst_2660_, 2);
v_snd_2661_ = lean_ctor_get(v_snd_2642_, 1);
lean_inc(v_snd_2661_);
lean_dec(v_snd_2642_);
v_pos_2662_ = lean_ctor_get(v_parserState_2425_, 0);
lean_inc(v_pos_2662_);
lean_dec_ref(v_parserState_2425_);
lean_inc_ref(v_opts_2634_);
v___y_2592_ = v_pos_2662_;
v___y_2593_ = v_opts_2634_;
v___y_2594_ = v___x_2640_;
v___y_2595_ = v_fst_2660_;
v___y_2596_ = v_snd_2661_;
v___y_2597_ = v_fst_2659_;
v___y_2598_ = v_opts_2634_;
v___y_2599_ = v___x_2640_;
v___y_2600_ = v_fst_2660_;
v___y_2601_ = v_fst_2659_;
goto v___jp_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2679_, lean_object* v_cmds_2680_, lean_object* v_stx_2681_, lean_object* v_newParserState_2682_, lean_object* v_val_2683_, uint8_t v_sync_2684_, lean_object* v_val_2685_, lean_object* v_a_2686_, lean_object* v_oldNext_2687_){
_start:
{
lean_object* v_cmdState_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_cmdState_2689_ = lean_ctor_get(v_oldResult_2679_, 1);
lean_inc_ref(v_cmdState_2689_);
lean_dec_ref(v_oldResult_2679_);
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_oldNext_2687_);
v___x_2691_ = lean_array_push(v_cmds_2680_, v_stx_2681_);
v___x_2692_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2690_, v_newParserState_2682_, v_cmdState_2689_, v_val_2683_, v_sync_2684_, v_val_2685_, v___x_2691_, v_a_2686_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2693_ = _args[0];
lean_object* v_val_2694_ = _args[1];
lean_object* v_cmds_2695_ = _args[2];
lean_object* v_fst_2696_ = _args[3];
lean_object* v_fst_2697_ = _args[4];
lean_object* v_val_2698_ = _args[5];
lean_object* v_a_2699_ = _args[6];
lean_object* v_snd_2700_ = _args[7];
lean_object* v___x_2701_ = _args[8];
lean_object* v___x_2702_ = _args[9];
lean_object* v_fst_2703_ = _args[10];
lean_object* v_val_2704_ = _args[11];
lean_object* v_val_2705_ = _args[12];
lean_object* v_val_2706_ = _args[13];
lean_object* v_snd_2707_ = _args[14];
lean_object* v_prom_2708_ = _args[15];
lean_object* v___x_2709_ = _args[16];
lean_object* v___f_2710_ = _args[17];
lean_object* v___f_2711_ = _args[18];
lean_object* v___f_2712_ = _args[19];
lean_object* v_pos_2713_ = _args[20];
lean_object* v_cmdState_2714_ = _args[21];
lean_object* v_opts_2715_ = _args[22];
lean_object* v___x_2716_ = _args[23];
lean_object* v_old_x3f_2717_ = _args[24];
lean_object* v_parseCancelTk_2718_ = _args[25];
lean_object* v_next_x3f_2719_ = _args[26];
lean_object* v___y_2720_ = _args[27];
_start:
{
uint8_t v_val_45269__boxed_2721_; uint8_t v___x_45272__boxed_2722_; lean_object* v_res_2723_; 
v_val_45269__boxed_2721_ = lean_unbox(v_val_2698_);
v___x_45272__boxed_2722_ = lean_unbox(v___x_2702_);
v_res_2723_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2693_, v_val_2694_, v_cmds_2695_, v_fst_2696_, v_fst_2697_, v_val_45269__boxed_2721_, v_a_2699_, v_snd_2700_, v___x_2701_, v___x_45272__boxed_2722_, v_fst_2703_, v_val_2704_, v_val_2705_, v_val_2706_, v_snd_2707_, v_prom_2708_, v___x_2709_, v___f_2710_, v___f_2711_, v___f_2712_, v_pos_2713_, v_cmdState_2714_, v_opts_2715_, v___x_2716_, v_old_x3f_2717_, v_parseCancelTk_2718_, v_next_x3f_2719_);
lean_dec_ref(v___x_2716_);
lean_dec_ref(v_opts_2715_);
lean_dec(v_prom_2708_);
lean_dec(v_val_2705_);
lean_dec_ref(v_a_2699_);
lean_dec(v_val_2694_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2724_, lean_object* v_parserState_2725_, lean_object* v_cmdState_2726_, lean_object* v_prom_2727_, lean_object* v_sync_2728_, lean_object* v_parseCancelTk_2729_, lean_object* v_cmds_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
uint8_t v_sync_boxed_2733_; lean_object* v_res_2734_; 
v_sync_boxed_2733_ = lean_unbox(v_sync_2728_);
v_res_2734_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2724_, v_parserState_2725_, v_cmdState_2726_, v_prom_2727_, v_sync_boxed_2733_, v_parseCancelTk_2729_, v_cmds_2730_, v_a_2731_);
lean_dec_ref(v_a_2731_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2735_, size_t v_i_2736_, size_t v_stop_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2735_, v_i_2736_, v_stop_2737_, v_b_2738_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2742_, lean_object* v_i_2743_, lean_object* v_stop_2744_, lean_object* v_b_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
size_t v_i_boxed_2748_; size_t v_stop_boxed_2749_; lean_object* v_res_2750_; 
v_i_boxed_2748_ = lean_unbox_usize(v_i_2743_);
lean_dec(v_i_2743_);
v_stop_boxed_2749_ = lean_unbox_usize(v_stop_2744_);
lean_dec(v_stop_2744_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2742_, v_i_boxed_2748_, v_stop_boxed_2749_, v_b_2745_, v___y_2746_);
lean_dec_ref(v___y_2746_);
lean_dec_ref(v_as_2742_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2751_, lean_object* v_opt_2752_){
_start:
{
lean_object* v_name_2753_; lean_object* v_map_2754_; lean_object* v___x_2755_; 
v_name_2753_ = lean_ctor_get(v_opt_2752_, 0);
v_map_2754_ = lean_ctor_get(v_opts_2751_, 0);
v___x_2755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2754_, v_name_2753_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
else
{
lean_object* v_val_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2766_; 
v_val_2757_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2759_ = v___x_2755_;
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_val_2757_);
lean_dec(v___x_2755_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
if (lean_obj_tag(v_val_2757_) == 0)
{
lean_object* v_v_2761_; lean_object* v___x_2763_; 
v_v_2761_ = lean_ctor_get(v_val_2757_, 0);
lean_inc_ref(v_v_2761_);
lean_dec_ref_known(v_val_2757_, 1);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v_v_2761_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_v_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
else
{
lean_object* v___x_2765_; 
lean_del_object(v___x_2759_);
lean_dec(v_val_2757_);
v___x_2765_ = lean_box(0);
return v___x_2765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2767_, lean_object* v_opt_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2767_, v_opt_2768_);
lean_dec_ref(v_opt_2768_);
lean_dec_ref(v_opts_2767_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2770_);
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2774_, 0, v_x_2771_);
lean_ctor_set(v___x_2774_, 1, v___x_2772_);
lean_ctor_set(v___x_2774_, 2, v___x_2773_);
return v___x_2774_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2781_ = l_Lean_Array_toPArray_x27___redArg(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
if (lean_obj_tag(v_a_2782_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = l_List_reverse___redArg(v_a_2783_);
return v___x_2784_;
}
else
{
lean_object* v_head_2785_; lean_object* v_tail_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2799_; 
v_head_2785_ = lean_ctor_get(v_a_2782_, 0);
v_tail_2786_ = lean_ctor_get(v_a_2782_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_a_2782_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2788_ = v_a_2782_;
v_isShared_2789_ = v_isSharedCheck_2799_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_tail_2786_);
lean_inc(v_head_2785_);
lean_dec(v_a_2782_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2799_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2790_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v_head_2785_);
v___x_2792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
v___x_2793_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v_a_2783_);
lean_ctor_set(v___x_2788_, 0, v___x_2794_);
v___x_2796_ = v___x_2788_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_a_2783_);
v___x_2796_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
v_a_2782_ = v_tail_2786_;
v_a_2783_ = v___x_2796_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2810_; double v___x_2811_; 
v___x_2810_ = lean_unsigned_to_nat(1000000000u);
v___x_2811_ = lean_float_of_nat(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2819_ = l_Lean_MessageData_ofFormat(v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2820_, lean_object* v_stx_2821_, lean_object* v_origStx_2822_, lean_object* v_toProcessingContext_2823_, lean_object* v___x_2824_, lean_object* v_fileMap_2825_, lean_object* v_parserState_2826_, lean_object* v_a_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_toProcessingContext_2832_; lean_object* v___x_2833_; 
v_toProcessingContext_2832_ = lean_ctor_get(v___y_2830_, 0);
lean_inc_ref(v_toProcessingContext_2832_);
lean_inc(v_stx_2821_);
v___x_2833_ = lean_apply_3(v_setupImports_2820_, v_stx_2821_, v_toProcessingContext_2832_, lean_box(0));
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_3046_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_3046_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_3046_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
if (lean_obj_tag(v_a_2834_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; 
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2828_);
lean_dec_ref(v_parserState_2826_);
lean_dec_ref(v_fileMap_2825_);
lean_dec(v___x_2824_);
lean_dec_ref(v_toProcessingContext_2823_);
lean_dec(v_origStx_2822_);
lean_dec(v_stx_2821_);
v_a_2838_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v_a_2834_, 1);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_a_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_3045_; 
v_a_2842_ = lean_ctor_get(v_a_2834_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_a_2834_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_2844_ = v_a_2834_;
v_isShared_2845_ = v_isSharedCheck_3045_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v_a_2834_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_3045_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v_mainModuleName_2847_; lean_object* v_package_x3f_2848_; uint8_t v_isModule_2849_; lean_object* v_imports_2850_; lean_object* v_opts_2851_; uint32_t v_trustLevel_2852_; lean_object* v_importArts_2853_; lean_object* v_plugins_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2859_; 
v___x_2846_ = lean_io_mono_nanos_now();
v_mainModuleName_2847_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_mainModuleName_2847_);
v_package_x3f_2848_ = lean_ctor_get(v_a_2842_, 1);
lean_inc(v_package_x3f_2848_);
v_isModule_2849_ = lean_ctor_get_uint8(v_a_2842_, sizeof(void*)*6 + 4);
v_imports_2850_ = lean_ctor_get(v_a_2842_, 2);
lean_inc_ref(v_imports_2850_);
v_opts_2851_ = lean_ctor_get(v_a_2842_, 3);
lean_inc_ref(v_opts_2851_);
v_trustLevel_2852_ = lean_ctor_get_uint32(v_a_2842_, sizeof(void*)*6);
v_importArts_2853_ = lean_ctor_get(v_a_2842_, 4);
lean_inc(v_importArts_2853_);
v_plugins_2854_ = lean_ctor_get(v_a_2842_, 5);
lean_inc_ref(v_plugins_2854_);
lean_dec(v_a_2842_);
v___x_2855_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2821_);
v___x_2856_ = l_Lean_MessageLog_empty;
v___x_2857_ = 1;
lean_inc(v_stx_2821_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_stx_2821_);
v___x_2859_ = v___x_2844_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_stx_2821_);
v___x_2859_ = v_reuseFailAlloc_3044_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_origStx_2822_);
lean_inc_ref(v___x_2859_);
lean_inc_ref(v_opts_2851_);
v___x_2861_ = l_Lean_Elab_processHeaderCore(v___x_2855_, v_imports_2850_, v_isModule_2849_, v_opts_2851_, v___x_2856_, v_toProcessingContext_2823_, v_trustLevel_2852_, v_plugins_2854_, v___x_2857_, v_mainModuleName_2847_, v_package_x3f_2848_, v_importArts_2853_, v___x_2859_, v___x_2860_);
lean_dec(v___x_2855_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_3035_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_3035_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_3035_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_fst_2866_; lean_object* v_snd_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_3034_; 
v_fst_2866_ = lean_ctor_get(v_a_2862_, 0);
v_snd_2867_ = lean_ctor_get(v_a_2862_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_2869_ = v_a_2862_;
v_isShared_2870_ = v_isSharedCheck_3034_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_snd_2867_);
lean_inc(v_fst_2866_);
lean_dec(v_a_2862_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_3034_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v_traceState_2889_; 
v___x_2871_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2867_);
v___x_2872_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2867_);
v___x_2873_ = l_Lean_MessageLog_hasErrors(v_snd_2867_);
if (v___x_2873_ == 0)
{
double v___x_2982_; double v___x_2983_; double v___x_2984_; double v___x_2985_; double v___x_2986_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_del_object(v___x_2836_);
lean_dec_ref(v___x_2829_);
v___x_2982_ = lean_float_of_nat(v___x_2846_);
v___x_2983_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2984_ = lean_float_div(v___x_2982_, v___x_2983_);
v___x_2985_ = lean_float_of_nat(v___x_2871_);
v___x_2986_ = lean_float_div(v___x_2985_, v___x_2983_);
v___x_3003_ = l_Lean_trace_profiler_output;
v___x_3004_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2851_, v___x_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = l_Lean_trace_profiler_serve;
v___x_3006_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2851_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2889_ = v___x_3007_;
goto v___jp_2888_;
}
else
{
goto v___jp_2987_;
}
}
else
{
lean_dec_ref_known(v___x_3004_, 1);
goto v___jp_2987_;
}
v___jp_2987_:
{
uint64_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2988_ = 0ULL;
v___x_2989_ = lean_box(0);
v___x_2990_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2991_ = lean_box(0);
v___x_2992_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2993_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2993_, 0, v___x_2990_);
lean_ctor_set(v___x_2993_, 1, v___x_2991_);
lean_ctor_set(v___x_2993_, 2, v___x_2992_);
lean_ctor_set_float(v___x_2993_, sizeof(void*)*3, v___x_2984_);
lean_ctor_set_float(v___x_2993_, sizeof(void*)*3 + 8, v___x_2986_);
lean_ctor_set_uint8(v___x_2993_, sizeof(void*)*3 + 16, v___x_2857_);
v___x_2994_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2995_ = lean_mk_empty_array_with_capacity(v___x_2824_);
v___x_2996_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2993_);
lean_ctor_set(v___x_2996_, 1, v___x_2994_);
lean_ctor_set(v___x_2996_, 2, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2989_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = lean_unsigned_to_nat(1u);
v___x_2999_ = lean_mk_empty_array_with_capacity(v___x_2998_);
v___x_3000_ = lean_array_push(v___x_2999_, v___x_2997_);
v___x_3001_ = l_Lean_Array_toPArray_x27___redArg(v___x_3000_);
lean_dec_ref(v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set_uint64(v___x_3002_, sizeof(void*)*1, v___x_2988_);
v_traceState_2889_ = v___x_3002_;
goto v___jp_2888_;
}
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint64_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
lean_dec(v___x_2871_);
lean_del_object(v___x_2869_);
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_del_object(v___x_2864_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_opts_2851_);
lean_dec(v___x_2846_);
lean_dec(v___x_2828_);
lean_dec_ref(v_parserState_2826_);
lean_dec_ref(v_fileMap_2825_);
lean_dec(v_stx_2821_);
v___x_3008_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3009_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3010_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2824_, 2);
v___x_3011_ = l_Lean_Name_num___override(v___x_3010_, v___x_2824_);
v___x_3012_ = l_Lean_Name_str___override(v___x_3011_, v___x_3008_);
v___x_3013_ = l_Lean_Name_str___override(v___x_3012_, v___x_3009_);
v___x_3014_ = l_Lean_Name_str___override(v___x_3013_, v___x_3008_);
v___x_3015_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3016_ = l_Lean_Name_str___override(v___x_3014_, v___x_3015_);
v___x_3017_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3018_ = l_Lean_Name_str___override(v___x_3016_, v___x_3017_);
v___x_3019_ = l_Lean_Name_toString(v___x_3018_, v___x_2857_);
v___x_3020_ = lean_box(0);
v___x_3021_ = 0ULL;
v___x_3022_ = lean_unsigned_to_nat(32u);
v___x_3023_ = lean_mk_empty_array_with_capacity(v___x_3022_);
v___x_3024_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3025_ = ((size_t)5ULL);
v___x_3026_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3023_);
lean_ctor_set(v___x_3026_, 2, v___x_2824_);
lean_ctor_set(v___x_3026_, 3, v___x_2824_);
lean_ctor_set_usize(v___x_3026_, 4, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set_uint64(v___x_3027_, sizeof(void*)*1, v___x_3021_);
v___x_3028_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3028_, 0, v___x_3019_);
lean_ctor_set(v___x_3028_, 1, v___x_2872_);
lean_ctor_set(v___x_3028_, 2, v___x_3020_);
lean_ctor_set(v___x_3028_, 3, v___x_3027_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*4, v___x_2873_);
v___x_3029_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2829_);
v___x_3030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
lean_ctor_set(v___x_3030_, 2, v___x_3020_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_3030_);
v___x_3032_ = v___x_2836_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
v___jp_2874_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___y_2880_);
v___x_2882_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2882_, 0, v___y_2878_);
lean_ctor_set(v___x_2882_, 1, v___x_2872_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
lean_ctor_set(v___x_2882_, 3, v___y_2879_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*4, v___x_2873_);
v___x_2883_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2875_, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2884_, 0, v___y_2876_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
lean_ctor_set(v___x_2884_, 2, v___y_2877_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2884_);
v___x_2886_ = v___x_2864_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
v___jp_2888_:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Language_Lean_reparseOptions(v_opts_2851_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_env_2897_; lean_object* v_messages_2898_; lean_object* v_scopes_2899_; lean_object* v_usedQuotCtxts_2900_; lean_object* v_nextMacroScope_2901_; lean_object* v_maxRecDepth_2902_; lean_object* v_ngen_2903_; lean_object* v_auxDeclNGen_2904_; lean_object* v_snapshotTasks_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2971_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2824_, 4);
v___x_2893_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2824_);
lean_ctor_set(v___x_2893_, 1, v___x_2824_);
lean_ctor_set(v___x_2893_, 2, v___x_2824_);
lean_ctor_set(v___x_2893_, 3, v___x_2824_);
lean_ctor_set(v___x_2893_, 4, v___x_2892_);
lean_ctor_set(v___x_2893_, 5, v___x_2892_);
lean_ctor_set(v___x_2893_, 6, v___x_2892_);
lean_ctor_set(v___x_2893_, 7, v___x_2892_);
lean_ctor_set(v___x_2893_, 8, v___x_2892_);
lean_ctor_set(v___x_2893_, 9, v___x_2892_);
v___x_2894_ = lean_io_promise_new();
v___x_2895_ = l_IO_CancelToken_new();
lean_inc(v_fst_2866_);
v___x_2896_ = l_Lean_Elab_Command_mkState(v_fst_2866_, v_snd_2867_, v_a_2891_);
v_env_2897_ = lean_ctor_get(v___x_2896_, 0);
v_messages_2898_ = lean_ctor_get(v___x_2896_, 1);
v_scopes_2899_ = lean_ctor_get(v___x_2896_, 2);
v_usedQuotCtxts_2900_ = lean_ctor_get(v___x_2896_, 3);
v_nextMacroScope_2901_ = lean_ctor_get(v___x_2896_, 4);
v_maxRecDepth_2902_ = lean_ctor_get(v___x_2896_, 5);
v_ngen_2903_ = lean_ctor_get(v___x_2896_, 6);
v_auxDeclNGen_2904_ = lean_ctor_get(v___x_2896_, 7);
v_snapshotTasks_2905_ = lean_ctor_get(v___x_2896_, 10);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; lean_object* v_unused_2973_; 
v_unused_2972_ = lean_ctor_get(v___x_2896_, 9);
lean_dec(v_unused_2972_);
v_unused_2973_ = lean_ctor_get(v___x_2896_, 8);
lean_dec(v_unused_2973_);
v___x_2907_ = v___x_2896_;
v_isShared_2908_ = v_isSharedCheck_2971_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snapshotTasks_2905_);
lean_inc(v_auxDeclNGen_2904_);
lean_inc(v_ngen_2903_);
lean_inc(v_maxRecDepth_2902_);
lean_inc(v_nextMacroScope_2901_);
lean_inc(v_usedQuotCtxts_2900_);
lean_inc(v_scopes_2899_);
lean_inc(v_messages_2898_);
lean_inc(v_env_2897_);
lean_dec(v___x_2896_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2971_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = l_Lean_Options_empty;
v___x_2911_ = lean_box(0);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2915_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2915_, 0, v_fst_2866_);
lean_ctor_set(v___x_2915_, 1, v___x_2909_);
lean_ctor_set(v___x_2915_, 2, v_fileMap_2825_);
lean_ctor_set(v___x_2915_, 3, v___x_2893_);
lean_ctor_set(v___x_2915_, 4, v___x_2910_);
lean_ctor_set(v___x_2915_, 5, v___x_2911_);
lean_ctor_set(v___x_2915_, 6, v___x_2912_);
lean_ctor_set(v___x_2915_, 7, v___x_2914_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
v___x_2917_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2821_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v_stx_2821_);
lean_ctor_set(v___x_2869_, 0, v___x_2917_);
v___x_2919_ = v___x_2869_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_stx_2821_);
v___x_2919_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
v___x_2921_ = lean_unsigned_to_nat(2u);
v___x_2922_ = l_Lean_Syntax_getArg(v_stx_2821_, v___x_2921_);
lean_dec(v_stx_2821_);
v___x_2923_ = l_Lean_Syntax_getArgs(v___x_2922_);
lean_dec(v___x_2922_);
v___x_2924_ = lean_array_to_list(v___x_2923_);
v___x_2925_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2924_, v___x_2912_);
v___x_2926_ = l_Lean_List_toPArray_x27___redArg(v___x_2925_);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2920_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2916_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = lean_mk_empty_array_with_capacity(v___x_2913_);
v___x_2930_ = lean_array_push(v___x_2929_, v___x_2928_);
v___x_2931_ = l_Lean_Array_toPArray_x27___redArg(v___x_2930_);
lean_dec_ref(v___x_2930_);
lean_inc_ref(v___x_2931_);
v___x_2932_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2932_, 0, v___x_2892_);
lean_ctor_set(v___x_2932_, 1, v___x_2892_);
lean_ctor_set(v___x_2932_, 2, v___x_2931_);
lean_ctor_set_uint8(v___x_2932_, sizeof(void*)*3, v___x_2857_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 9, v_traceState_2889_);
lean_ctor_set(v___x_2907_, 8, v___x_2932_);
v___x_2934_ = v___x_2907_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_env_2897_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_messages_2898_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_scopes_2899_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_usedQuotCtxts_2900_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_nextMacroScope_2901_);
lean_ctor_set(v_reuseFailAlloc_2969_, 5, v_maxRecDepth_2902_);
lean_ctor_set(v_reuseFailAlloc_2969_, 6, v_ngen_2903_);
lean_ctor_set(v_reuseFailAlloc_2969_, 7, v_auxDeclNGen_2904_);
lean_ctor_set(v_reuseFailAlloc_2969_, 8, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2969_, 9, v_traceState_2889_);
lean_ctor_set(v_reuseFailAlloc_2969_, 10, v_snapshotTasks_2905_);
v___x_2934_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; size_t v___x_2944_; lean_object* v___x_2945_; lean_object* v_size_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint64_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2824_);
lean_inc_ref(v___x_2895_);
lean_inc(v___x_2894_);
lean_inc_ref(v___x_2934_);
v___x_2936_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2909_, v_parserState_2826_, v___x_2934_, v___x_2894_, v___x_2857_, v___x_2895_, v___x_2935_, v_a_2827_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2938_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2939_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2824_, 3);
v___x_2940_ = l_Lean_Name_num___override(v___x_2939_, v___x_2824_);
v___x_2941_ = lean_unsigned_to_nat(32u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
v___x_2943_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2944_ = ((size_t)5ULL);
v___x_2945_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2942_);
lean_ctor_set(v___x_2945_, 2, v___x_2824_);
lean_ctor_set(v___x_2945_, 3, v___x_2824_);
lean_ctor_set_usize(v___x_2945_, 4, v___x_2944_);
v_size_2946_ = lean_ctor_get(v___x_2931_, 2);
lean_inc(v_size_2946_);
v___x_2947_ = l_Lean_Name_str___override(v___x_2940_, v___x_2937_);
v___x_2948_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2828_);
v___x_2949_ = l_Lean_Name_str___override(v___x_2947_, v___x_2938_);
v___x_2950_ = l_Lean_Name_str___override(v___x_2949_, v___x_2937_);
v___x_2951_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2952_ = l_Lean_Name_str___override(v___x_2950_, v___x_2951_);
v___x_2953_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2954_ = l_Lean_Name_str___override(v___x_2952_, v___x_2953_);
v___x_2955_ = l_Lean_Name_toString(v___x_2954_, v___x_2857_);
v___x_2956_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2957_ = 0ULL;
v___x_2958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2958_, 0, v___x_2945_);
lean_ctor_set_uint64(v___x_2958_, sizeof(void*)*1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2895_);
v___x_2960_ = l_IO_Promise_result_x21___redArg(v___x_2894_);
lean_dec(v___x_2894_);
v___x_2961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2828_);
lean_ctor_set(v___x_2961_, 1, v___x_2948_);
lean_ctor_set(v___x_2961_, 2, v___x_2959_);
lean_ctor_set(v___x_2961_, 3, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2934_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_inc_ref(v___x_2958_);
lean_inc_ref(v___x_2955_);
v___x_2964_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2964_, 0, v___x_2955_);
lean_ctor_set(v___x_2964_, 1, v___x_2956_);
lean_ctor_set(v___x_2964_, 2, v___x_2909_);
lean_ctor_set(v___x_2964_, 3, v___x_2958_);
lean_ctor_set_uint8(v___x_2964_, sizeof(void*)*4, v___x_2873_);
v___x_2965_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2966_ = lean_nat_dec_lt(v___x_2824_, v_size_2946_);
lean_dec(v_size_2946_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_dec_ref(v___x_2931_);
lean_dec(v___x_2824_);
v___x_2967_ = l_outOfBounds___redArg(v___x_2965_);
v___y_2875_ = v___x_2859_;
v___y_2876_ = v___x_2964_;
v___y_2877_ = v___x_2963_;
v___y_2878_ = v___x_2955_;
v___y_2879_ = v___x_2958_;
v___y_2880_ = v___x_2967_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2965_, v___x_2931_, v___x_2824_);
lean_dec(v___x_2824_);
lean_dec_ref(v___x_2931_);
v___y_2875_ = v___x_2859_;
v___y_2876_ = v___x_2964_;
v___y_2877_ = v___x_2963_;
v___y_2878_ = v___x_2955_;
v___y_2879_ = v___x_2958_;
v___y_2880_ = v___x_2968_;
goto v___jp_2874_;
}
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v_traceState_2889_);
lean_dec_ref(v___x_2872_);
lean_del_object(v___x_2869_);
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_del_object(v___x_2864_);
lean_dec_ref(v___x_2859_);
lean_dec(v___x_2828_);
lean_dec_ref(v_parserState_2826_);
lean_dec_ref(v_fileMap_2825_);
lean_dec(v___x_2824_);
lean_dec(v_stx_2821_);
v_a_2974_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2890_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2890_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
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
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_opts_2851_);
lean_dec(v___x_2846_);
lean_del_object(v___x_2836_);
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2828_);
lean_dec_ref(v_parserState_2826_);
lean_dec_ref(v_fileMap_2825_);
lean_dec(v___x_2824_);
lean_dec(v_stx_2821_);
v_a_3036_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2861_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2861_);
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
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2828_);
lean_dec_ref(v_parserState_2826_);
lean_dec_ref(v_fileMap_2825_);
lean_dec(v___x_2824_);
lean_dec_ref(v_toProcessingContext_2823_);
lean_dec(v_origStx_2822_);
lean_dec(v_stx_2821_);
v_a_3047_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_2833_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_2833_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3055_, lean_object* v_stx_3056_, lean_object* v_origStx_3057_, lean_object* v_toProcessingContext_3058_, lean_object* v___x_3059_, lean_object* v_fileMap_3060_, lean_object* v_parserState_3061_, lean_object* v_a_3062_, lean_object* v___x_3063_, lean_object* v___x_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3055_, v_stx_3056_, v_origStx_3057_, v_toProcessingContext_3058_, v___x_3059_, v_fileMap_3060_, v_parserState_3061_, v_a_3062_, v___x_3063_, v___x_3064_, v___y_3065_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_a_3062_);
return v_res_3067_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___f_3069_; 
v___x_3068_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3069_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3069_, 0, v___x_3068_);
return v___f_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3070_, lean_object* v_stx_3071_, lean_object* v_origStx_3072_, lean_object* v_parserState_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_toProcessingContext_3076_; lean_object* v_fileMap_3077_; lean_object* v_endPos_3078_; lean_object* v___x_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_toProcessingContext_3076_ = lean_ctor_get(v_a_3074_, 0);
v_fileMap_3077_ = lean_ctor_get(v_toProcessingContext_3076_, 2);
v_endPos_3078_ = lean_ctor_get(v_toProcessingContext_3076_, 3);
v___x_3079_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3080_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3074_, 2);
lean_inc_ref(v_fileMap_3077_);
lean_inc_ref(v_toProcessingContext_3076_);
v___f_3083_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3083_, 0, v_setupImports_3070_);
lean_closure_set(v___f_3083_, 1, v_stx_3071_);
lean_closure_set(v___f_3083_, 2, v_origStx_3072_);
lean_closure_set(v___f_3083_, 3, v_toProcessingContext_3076_);
lean_closure_set(v___f_3083_, 4, v___x_3082_);
lean_closure_set(v___f_3083_, 5, v_fileMap_3077_);
lean_closure_set(v___f_3083_, 6, v_parserState_3073_);
lean_closure_set(v___f_3083_, 7, v_a_3074_);
lean_closure_set(v___f_3083_, 8, v___x_3081_);
lean_closure_set(v___f_3083_, 9, v___x_3079_);
lean_inc(v_endPos_3078_);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v_endPos_3078_);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
v___x_3086_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3086_, 0, lean_box(0));
lean_closure_set(v___x_3086_, 1, v___f_3080_);
lean_closure_set(v___x_3086_, 2, v___f_3083_);
lean_closure_set(v___x_3086_, 3, v_a_3074_);
v___x_3087_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3081_, v___x_3081_, v___x_3085_, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3088_, lean_object* v_stx_3089_, lean_object* v_origStx_3090_, lean_object* v_parserState_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3088_, v_stx_3089_, v_origStx_3090_, v_parserState_3091_, v_a_3092_);
lean_dec_ref(v_a_3092_);
return v_res_3094_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3097_);
return v___x_3098_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = 1;
v___x_3104_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3105_ = l_Lean_Name_toString(v___x_3104_, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = 0;
v___x_3107_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3110_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3111_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v___x_3109_);
lean_ctor_set(v___x_3111_, 2, v___x_3108_);
lean_ctor_set(v___x_3111_, 3, v___x_3107_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*4, v___x_3106_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3112_, lean_object* v_cmdState_3113_, lean_object* v_a_3114_, lean_object* v_toSnapshot_3115_, lean_object* v_newStx_3116_, lean_object* v_oldCmd_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v_diagnostics_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3147_; 
v___x_3119_ = lean_io_promise_new();
v___x_3120_ = l_IO_CancelToken_new();
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_oldCmd_3117_);
v___x_3122_ = 1;
v___x_3123_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3120_);
lean_inc(v___x_3119_);
lean_inc_ref(v_cmdState_3113_);
v___x_3124_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3121_, v_newParserState_3112_, v_cmdState_3113_, v___x_3119_, v___x_3122_, v___x_3120_, v___x_3123_, v_a_3114_);
v_diagnostics_3125_ = lean_ctor_get(v_toSnapshot_3115_, 1);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_toSnapshot_3115_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3148_ = lean_ctor_get(v_toSnapshot_3115_, 3);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_toSnapshot_3115_, 2);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_toSnapshot_3115_, 0);
lean_dec(v_unused_3150_);
v___x_3127_ = v_toSnapshot_3115_;
v_isShared_3128_ = v_isSharedCheck_3147_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_diagnostics_3125_);
lean_dec(v_toSnapshot_3115_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3147_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3131_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3132_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3120_);
v___x_3134_ = l_IO_Promise_result_x21___redArg(v___x_3119_);
lean_dec(v___x_3119_);
v___x_3135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3129_);
lean_ctor_set(v___x_3135_, 1, v___x_3130_);
lean_ctor_set(v___x_3135_, 2, v___x_3133_);
lean_ctor_set(v___x_3135_, 3, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v_cmdState_3113_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___x_3138_ = 0;
v___x_3139_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_newStx_3116_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 3, v___x_3132_);
lean_ctor_set(v___x_3127_, 2, v___x_3129_);
lean_ctor_set(v___x_3127_, 0, v___x_3131_);
v___x_3142_ = v___x_3127_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_diagnostics_3125_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v___x_3132_);
v___x_3142_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_ctor_set_uint8(v___x_3142_, sizeof(void*)*4, v___x_3138_);
v___x_3143_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3140_, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3139_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
lean_ctor_set(v___x_3144_, 2, v___x_3137_);
v___x_3145_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3129_, v___x_3144_);
return v___x_3145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3151_, lean_object* v_cmdState_3152_, lean_object* v_a_3153_, lean_object* v_toSnapshot_3154_, lean_object* v_newStx_3155_, lean_object* v_oldCmd_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3151_, v_cmdState_3152_, v_a_3153_, v_toSnapshot_3154_, v_newStx_3155_, v_oldCmd_3156_);
lean_dec_ref(v_a_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3159_, lean_object* v_a_3160_, lean_object* v_newStx_3161_, lean_object* v___x_3162_, lean_object* v_oldProcessed_3163_){
_start:
{
lean_object* v_result_x3f_3165_; 
v_result_x3f_3165_ = lean_ctor_get(v_oldProcessed_3163_, 2);
if (lean_obj_tag(v_result_x3f_3165_) == 1)
{
lean_object* v_val_3166_; lean_object* v_firstCmdSnap_3167_; lean_object* v_toSnapshot_3168_; lean_object* v_cmdState_3169_; lean_object* v_stx_x3f_3170_; lean_object* v___f_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; 
v_val_3166_ = lean_ctor_get(v_result_x3f_3165_, 0);
lean_inc(v_val_3166_);
v_firstCmdSnap_3167_ = lean_ctor_get(v_val_3166_, 1);
lean_inc_ref(v_firstCmdSnap_3167_);
v_toSnapshot_3168_ = lean_ctor_get(v_oldProcessed_3163_, 0);
lean_inc_ref(v_toSnapshot_3168_);
lean_dec_ref(v_oldProcessed_3163_);
v_cmdState_3169_ = lean_ctor_get(v_val_3166_, 0);
lean_inc_ref(v_cmdState_3169_);
lean_dec(v_val_3166_);
v_stx_x3f_3170_ = lean_ctor_get(v_firstCmdSnap_3167_, 0);
lean_inc(v_stx_x3f_3170_);
lean_inc_ref(v_a_3160_);
v___f_3171_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3171_, 0, v_newParserState_3159_);
lean_closure_set(v___f_3171_, 1, v_cmdState_3169_);
lean_closure_set(v___f_3171_, 2, v_a_3160_);
lean_closure_set(v___f_3171_, 3, v_toSnapshot_3168_);
lean_closure_set(v___f_3171_, 4, v_newStx_3161_);
v___x_3172_ = lean_box(0);
v___x_3173_ = 1;
v___x_3174_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3167_, v___f_3171_, v_stx_x3f_3170_, v___x_3162_, v___x_3172_, v___x_3173_);
return v___x_3174_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec(v___x_3162_);
lean_dec_ref(v_newParserState_3159_);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_newStx_3161_);
v___x_3176_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3175_, v_oldProcessed_3163_);
return v___x_3176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3177_, lean_object* v_a_3178_, lean_object* v_newStx_3179_, lean_object* v___x_3180_, lean_object* v_oldProcessed_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3177_, v_a_3178_, v_newStx_3179_, v___x_3180_, v_oldProcessed_3181_);
lean_dec_ref(v_a_3178_);
return v_res_3183_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3184_ = 0;
v___x_3185_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3186_ = lean_box(0);
v___x_3187_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3188_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3189_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v___x_3187_);
lean_ctor_set(v___x_3189_, 2, v___x_3186_);
lean_ctor_set(v___x_3189_, 3, v___x_3185_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*4, v___x_3184_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3190_, lean_object* v_a_3191_, lean_object* v_old_3192_, lean_object* v_newStx_3193_, lean_object* v_newParserState_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_result_x3f_3197_; 
v_result_x3f_3197_ = lean_ctor_get(v_old_3192_, 4);
lean_inc(v_result_x3f_3197_);
if (lean_obj_tag(v_result_x3f_3197_) == 1)
{
lean_object* v_val_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3252_; 
v_val_3198_ = lean_ctor_get(v_result_x3f_3197_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_result_x3f_3197_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3200_ = v_result_x3f_3197_;
v_isShared_3201_ = v_isSharedCheck_3252_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_val_3198_);
lean_dec(v_result_x3f_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3252_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_processedSnap_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3250_; 
v_processedSnap_3202_ = lean_ctor_get(v_val_3198_, 1);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_val_3198_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_val_3198_, 0);
lean_dec(v_unused_3251_);
v___x_3204_ = v_val_3198_;
v_isShared_3205_ = v_isSharedCheck_3250_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_processedSnap_3202_);
lean_dec(v_val_3198_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3250_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_toSnapshot_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3245_; 
v_toSnapshot_3206_ = lean_ctor_get(v_old_3192_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_old_3192_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; lean_object* v_unused_3247_; lean_object* v_unused_3248_; lean_object* v_unused_3249_; 
v_unused_3246_ = lean_ctor_get(v_old_3192_, 4);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_old_3192_, 3);
lean_dec(v_unused_3247_);
v_unused_3248_ = lean_ctor_get(v_old_3192_, 2);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_old_3192_, 1);
lean_dec(v_unused_3249_);
v___x_3208_ = v_old_3192_;
v_isShared_3209_ = v_isSharedCheck_3245_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_toSnapshot_3206_);
lean_dec(v_old_3192_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3245_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_pos_3210_; lean_object* v_endPos_3211_; lean_object* v_stx_x3f_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v_diagnostics_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3241_; 
v_pos_3210_ = lean_ctor_get(v_newParserState_3194_, 0);
v_endPos_3211_ = lean_ctor_get(v_toProcessingContext_3190_, 3);
v_stx_x3f_3212_ = lean_ctor_get(v_processedSnap_3202_, 0);
lean_inc(v_stx_x3f_3212_);
lean_inc(v_endPos_3211_);
lean_inc(v_pos_3210_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_pos_3210_);
lean_ctor_set(v___x_3213_, 1, v_endPos_3211_);
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_inc_ref(v___x_3214_);
lean_inc(v_newStx_3193_);
lean_inc_ref(v_a_3191_);
lean_inc_ref(v_newParserState_3194_);
v___f_3215_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3215_, 0, v_newParserState_3194_);
lean_closure_set(v___f_3215_, 1, v_a_3191_);
lean_closure_set(v___f_3215_, 2, v_newStx_3193_);
lean_closure_set(v___f_3215_, 3, v___x_3214_);
v___x_3216_ = lean_box(0);
v___x_3217_ = 1;
v___x_3218_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3202_, v___f_3215_, v_stx_x3f_3212_, v___x_3214_, v___x_3216_, v___x_3217_);
v_diagnostics_3219_ = lean_ctor_get(v_toSnapshot_3206_, 1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_toSnapshot_3206_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; lean_object* v_unused_3243_; lean_object* v_unused_3244_; 
v_unused_3242_ = lean_ctor_get(v_toSnapshot_3206_, 3);
lean_dec(v_unused_3242_);
v_unused_3243_ = lean_ctor_get(v_toSnapshot_3206_, 2);
lean_dec(v_unused_3243_);
v_unused_3244_ = lean_ctor_get(v_toSnapshot_3206_, 0);
lean_dec(v_unused_3244_);
v___x_3221_ = v_toSnapshot_3206_;
v_isShared_3222_ = v_isSharedCheck_3241_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_diagnostics_3219_);
lean_dec(v_toSnapshot_3206_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3241_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3223_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3224_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3218_);
lean_ctor_set(v___x_3204_, 0, v_newParserState_3194_);
v___x_3226_ = v___x_3204_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_newParserState_3194_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3218_);
v___x_3226_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3226_);
v___x_3228_ = v___x_3200_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
uint8_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3229_ = 0;
v___x_3230_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3193_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_newStx_3193_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 3, v___x_3224_);
lean_ctor_set(v___x_3221_, 2, v___x_3216_);
lean_ctor_set(v___x_3221_, 0, v___x_3223_);
v___x_3233_ = v___x_3221_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_diagnostics_3219_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v___x_3216_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v___x_3224_);
v___x_3233_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*4, v___x_3229_);
v___x_3234_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3231_, v___x_3233_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 4, v___x_3228_);
lean_ctor_set(v___x_3208_, 3, v_newStx_3193_);
lean_ctor_set(v___x_3208_, 2, v_toProcessingContext_3190_);
lean_ctor_set(v___x_3208_, 1, v___x_3234_);
lean_ctor_set(v___x_3208_, 0, v___x_3230_);
v___x_3236_ = v___x_3208_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_toProcessingContext_3190_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_newStx_3193_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v___x_3228_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
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
lean_dec(v_result_x3f_3197_);
lean_dec_ref(v_newParserState_3194_);
lean_dec(v_newStx_3193_);
lean_dec_ref(v_toProcessingContext_3190_);
return v_old_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3253_, lean_object* v_a_3254_, lean_object* v_old_3255_, lean_object* v_newStx_3256_, lean_object* v_newParserState_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3253_, v_a_3254_, v_old_3255_, v_newStx_3256_, v_newParserState_3257_, v___y_3258_);
lean_dec_ref(v___y_3258_);
lean_dec_ref(v_a_3254_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3261_, lean_object* v_setupImports_3262_, lean_object* v_old_x3f_3263_, lean_object* v___f_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v___x_3267_; 
lean_inc_ref(v_toProcessingContext_3261_);
v___x_3267_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3261_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3337_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3270_ = v___x_3267_;
v_isShared_3271_ = v_isSharedCheck_3337_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3267_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3337_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v_snd_3272_; lean_object* v_fst_3273_; lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3336_; 
v_snd_3272_ = lean_ctor_get(v_a_3268_, 1);
lean_inc(v_snd_3272_);
v_fst_3273_ = lean_ctor_get(v_a_3268_, 0);
lean_inc(v_fst_3273_);
lean_dec(v_a_3268_);
v_fst_3274_ = lean_ctor_get(v_snd_3272_, 0);
v_snd_3275_ = lean_ctor_get(v_snd_3272_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_snd_3272_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3277_ = v_snd_3272_;
v_isShared_3278_ = v_isSharedCheck_3336_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_snd_3275_);
lean_inc(v_fst_3274_);
lean_dec(v_snd_3272_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3336_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
uint8_t v___x_3279_; 
v___x_3279_ = l_Lean_MessageLog_hasErrors(v_snd_3275_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___y_3282_; 
lean_inc(v_fst_3273_);
v___x_3280_ = l_Lean_Syntax_unsetTrailing(v_fst_3273_);
if (lean_obj_tag(v_old_x3f_3263_) == 1)
{
lean_object* v_val_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3319_; 
v_val_3303_ = lean_ctor_get(v_old_x3f_3263_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_old_x3f_3263_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3305_ = v_old_x3f_3263_;
v_isShared_3306_ = v_isSharedCheck_3319_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_val_3303_);
lean_dec(v_old_x3f_3263_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3319_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_stx_3307_; lean_object* v_result_x3f_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v_stx_3307_ = lean_ctor_get(v_val_3303_, 3);
v_result_x3f_3308_ = lean_ctor_get(v_val_3303_, 4);
lean_inc(v_stx_3307_);
v___x_3309_ = l_Lean_Syntax_unsetTrailing(v_stx_3307_);
lean_inc(v___x_3280_);
v___x_3310_ = l_Lean_Syntax_eqWithInfo(v___x_3280_, v___x_3309_);
if (v___x_3310_ == 0)
{
lean_inc(v_result_x3f_3308_);
lean_del_object(v___x_3305_);
lean_dec(v_val_3303_);
lean_dec_ref(v___f_3264_);
if (lean_obj_tag(v_result_x3f_3308_) == 0)
{
v___y_3282_ = v___y_3265_;
goto v___jp_3281_;
}
else
{
lean_object* v_val_3311_; lean_object* v_processedSnap_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_val_3311_ = lean_ctor_get(v_result_x3f_3308_, 0);
lean_inc(v_val_3311_);
lean_dec_ref_known(v_result_x3f_3308_, 1);
v_processedSnap_3312_ = lean_ctor_get(v_val_3311_, 1);
lean_inc_ref(v_processedSnap_3312_);
lean_dec(v_val_3311_);
v___x_3313_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3314_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3313_, v_processedSnap_3312_);
v___y_3282_ = v___y_3265_;
goto v___jp_3281_;
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_dec(v___x_3280_);
lean_del_object(v___x_3277_);
lean_dec(v_snd_3275_);
lean_del_object(v___x_3270_);
lean_dec_ref(v_setupImports_3262_);
lean_dec_ref(v_toProcessingContext_3261_);
lean_inc_ref(v___y_3265_);
v___x_3315_ = lean_apply_5(v___f_3264_, v_val_3303_, v_fst_3273_, v_fst_3274_, v___y_3265_, lean_box(0));
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3315_);
v___x_3317_ = v___x_3305_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_dec_ref(v___f_3264_);
lean_dec(v_old_x3f_3263_);
v___y_3282_ = v___y_3265_;
goto v___jp_3281_;
}
v___jp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3283_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3275_);
lean_inc(v_fst_3274_);
lean_inc(v_fst_3273_);
v___x_3284_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3262_, v___x_3280_, v_fst_3273_, v_fst_3274_, v___y_3282_);
v___x_3285_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3286_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_unsigned_to_nat(32u);
v___x_3289_ = lean_mk_empty_array_with_capacity(v___x_3288_);
lean_dec_ref(v___x_3289_);
v___x_3290_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___x_3284_);
v___x_3292_ = v___x_3277_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_fst_3274_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v___x_3284_);
v___x_3292_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3294_, 0, v___x_3285_);
lean_ctor_set(v___x_3294_, 1, v___x_3286_);
lean_ctor_set(v___x_3294_, 2, v___x_3287_);
lean_ctor_set(v___x_3294_, 3, v___x_3290_);
lean_ctor_set_uint8(v___x_3294_, sizeof(void*)*4, v___x_3279_);
lean_inc(v_fst_3273_);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_fst_3273_);
v___x_3296_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3296_, 0, v___x_3285_);
lean_ctor_set(v___x_3296_, 1, v___x_3283_);
lean_ctor_set(v___x_3296_, 2, v___x_3287_);
lean_ctor_set(v___x_3296_, 3, v___x_3290_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*4, v___x_3279_);
v___x_3297_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3295_, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3294_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
lean_ctor_set(v___x_3298_, 2, v_toProcessingContext_3261_);
lean_ctor_set(v___x_3298_, 3, v_fst_3273_);
lean_ctor_set(v___x_3298_, 4, v___x_3293_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3298_);
v___x_3300_ = v___x_3270_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_del_object(v___x_3277_);
lean_dec(v_fst_3274_);
lean_dec_ref(v___f_3264_);
lean_dec(v_old_x3f_3263_);
lean_dec_ref(v_setupImports_3262_);
v___x_3320_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3275_);
v___x_3321_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3322_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_unsigned_to_nat(32u);
v___x_3325_ = lean_mk_empty_array_with_capacity(v___x_3324_);
lean_dec_ref(v___x_3325_);
v___x_3326_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3327_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3327_, 0, v___x_3321_);
lean_ctor_set(v___x_3327_, 1, v___x_3322_);
lean_ctor_set(v___x_3327_, 2, v___x_3323_);
lean_ctor_set(v___x_3327_, 3, v___x_3326_);
lean_ctor_set_uint8(v___x_3327_, sizeof(void*)*4, v___x_3279_);
lean_inc(v_fst_3273_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_fst_3273_);
v___x_3329_ = 0;
v___x_3330_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3330_, 0, v___x_3321_);
lean_ctor_set(v___x_3330_, 1, v___x_3320_);
lean_ctor_set(v___x_3330_, 2, v___x_3323_);
lean_ctor_set(v___x_3330_, 3, v___x_3326_);
lean_ctor_set_uint8(v___x_3330_, sizeof(void*)*4, v___x_3329_);
v___x_3331_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3328_, v___x_3330_);
v___x_3332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3327_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
lean_ctor_set(v___x_3332_, 2, v_toProcessingContext_3261_);
lean_ctor_set(v___x_3332_, 3, v_fst_3273_);
lean_ctor_set(v___x_3332_, 4, v___x_3323_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3332_);
v___x_3334_ = v___x_3270_;
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
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v___f_3264_);
lean_dec(v_old_x3f_3263_);
lean_dec_ref(v_setupImports_3262_);
lean_dec_ref(v_toProcessingContext_3261_);
v_a_3338_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3267_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3267_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3346_, lean_object* v_setupImports_3347_, lean_object* v_old_x3f_3348_, lean_object* v___f_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3346_, v_setupImports_3347_, v_old_x3f_3348_, v___f_3349_, v___y_3350_);
lean_dec_ref(v___y_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3353_, lean_object* v_toProcessingContext_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3356_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3353_);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3359_, 0, v_x_3355_);
lean_ctor_set(v___x_3359_, 1, v___x_3356_);
lean_ctor_set(v___x_3359_, 2, v_toProcessingContext_3354_);
lean_ctor_set(v___x_3359_, 3, v___x_3357_);
lean_ctor_set(v___x_3359_, 4, v___x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3360_, lean_object* v_old_x3f_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_toProcessingContext_3364_; lean_object* v___x_3365_; lean_object* v___f_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; 
v_toProcessingContext_3364_ = lean_ctor_get(v_a_3362_, 0);
v___x_3365_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3362_);
lean_inc_ref_n(v_toProcessingContext_3364_, 3);
v___f_3366_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3366_, 0, v_toProcessingContext_3364_);
lean_closure_set(v___f_3366_, 1, v_a_3362_);
lean_inc(v_old_x3f_3361_);
v___f_3367_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3367_, 0, v_toProcessingContext_3364_);
lean_closure_set(v___f_3367_, 1, v_setupImports_3360_);
lean_closure_set(v___f_3367_, 2, v_old_x3f_3361_);
lean_closure_set(v___f_3367_, 3, v___f_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3368_, 0, v___x_3365_);
lean_closure_set(v___f_3368_, 1, v_toProcessingContext_3364_);
if (lean_obj_tag(v_old_x3f_3361_) == 1)
{
lean_object* v_val_3369_; lean_object* v_result_x3f_3370_; 
v_val_3369_ = lean_ctor_get(v_old_x3f_3361_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v_old_x3f_3361_, 1);
v_result_x3f_3370_ = lean_ctor_get(v_val_3369_, 4);
if (lean_obj_tag(v_result_x3f_3370_) == 1)
{
lean_object* v_stx_3371_; lean_object* v_val_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_stx_3371_ = lean_ctor_get(v_val_3369_, 3);
lean_inc(v_stx_3371_);
v_val_3372_ = lean_ctor_get(v_result_x3f_3370_, 0);
lean_inc(v_val_3369_);
v___x_3373_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3369_);
v___x_3374_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
if (lean_obj_tag(v_val_3375_) == 1)
{
lean_object* v_val_3376_; lean_object* v_firstCmdSnap_3377_; lean_object* v___x_3378_; 
v_val_3376_ = lean_ctor_get(v_val_3375_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_val_3375_, 1);
v_firstCmdSnap_3377_ = lean_ctor_get(v_val_3376_, 1);
lean_inc_ref(v_firstCmdSnap_3377_);
lean_dec(v_val_3376_);
v___x_3378_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3377_);
if (lean_obj_tag(v___x_3378_) == 1)
{
lean_object* v_val_3379_; lean_object* v_nextCmdSnap_x3f_3380_; 
v_val_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_val_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v_nextCmdSnap_x3f_3380_ = lean_ctor_get(v_val_3379_, 4);
lean_inc(v_nextCmdSnap_x3f_3380_);
lean_dec(v_val_3379_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3380_) == 0)
{
lean_object* v___x_3381_; 
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3381_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3381_;
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3383_; 
v_val_3382_ = lean_ctor_get(v_nextCmdSnap_x3f_3380_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3380_, 1);
v___x_3383_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3382_);
if (lean_obj_tag(v___x_3383_) == 1)
{
lean_object* v_val_3384_; lean_object* v_parserState_3385_; lean_object* v_pos_3386_; uint8_t v___x_3387_; 
v_val_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_val_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v_parserState_3385_ = lean_ctor_get(v_val_3384_, 2);
lean_inc_ref(v_parserState_3385_);
lean_dec(v_val_3384_);
v_pos_3386_ = lean_ctor_get(v_parserState_3385_, 0);
lean_inc(v_pos_3386_);
lean_dec_ref(v_parserState_3385_);
v___x_3387_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3386_, v_a_3362_);
lean_dec(v_pos_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3388_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3388_;
}
else
{
lean_object* v_parserState_3389_; lean_object* v___x_3390_; 
lean_dec_ref(v___f_3368_);
lean_dec_ref(v___f_3367_);
v_parserState_3389_ = lean_ctor_get(v_val_3372_, 0);
lean_inc_ref(v_parserState_3389_);
lean_inc_ref(v_toProcessingContext_3364_);
v___x_3390_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3364_, v_a_3362_, v_val_3369_, v_stx_3371_, v_parserState_3389_, v_a_3362_);
return v___x_3390_;
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v___x_3383_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3391_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3391_;
}
}
}
else
{
lean_object* v___x_3392_; 
lean_dec(v___x_3378_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3392_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3392_;
}
}
else
{
lean_object* v___x_3393_; 
lean_dec(v_val_3375_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3393_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3393_;
}
}
else
{
lean_object* v___x_3394_; 
lean_dec(v___x_3374_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3394_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3394_;
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v_val_3369_);
v___x_3395_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3396_; 
lean_dec(v_old_x3f_3361_);
v___x_3396_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3362_);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3397_, lean_object* v_old_x3f_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3397_, v_old_x3f_3398_, v_a_3399_);
lean_dec_ref(v_a_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3402_, lean_object* v_old_x3f_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; 
lean_inc(v_old_x3f_3403_);
v___x_3406_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3406_, 0, v_setupImports_3402_);
lean_closure_set(v___x_3406_, 1, v_old_x3f_3403_);
if (lean_obj_tag(v_old_x3f_3403_) == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = lean_box(0);
v___x_3408_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3406_, v___x_3407_, v_a_3404_);
return v___x_3408_;
}
else
{
lean_object* v_val_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3418_; 
v_val_3409_ = lean_ctor_get(v_old_x3f_3403_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_old_x3f_3403_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3411_ = v_old_x3f_3403_;
v_isShared_3412_ = v_isSharedCheck_3418_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_val_3409_);
lean_dec(v_old_x3f_3403_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3418_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v_ictx_3413_; lean_object* v___x_3415_; 
v_ictx_3413_ = lean_ctor_get(v_val_3409_, 2);
lean_inc_ref(v_ictx_3413_);
lean_dec(v_val_3409_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v_ictx_3413_);
v___x_3415_ = v___x_3411_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_ictx_3413_);
v___x_3415_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3406_, v___x_3415_, v_a_3404_);
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3419_, lean_object* v_old_x3f_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Language_Lean_process(v_setupImports_3419_, v_old_x3f_3420_, v_a_3421_);
lean_dec_ref(v_a_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3424_, lean_object* v_parserState_3425_, lean_object* v_commandState_3426_, lean_object* v_old_x3f_3427_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3437_; 
v___x_3429_ = lean_io_promise_new();
v___x_3430_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3427_) == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_box(0);
v___y_3437_ = v___x_3452_;
goto v___jp_3436_;
}
else
{
lean_object* v_val_3453_; lean_object* v_snd_3454_; lean_object* v___x_3455_; 
v_val_3453_ = lean_ctor_get(v_old_x3f_3427_, 0);
v_snd_3454_ = lean_ctor_get(v_val_3453_, 1);
lean_inc(v_snd_3454_);
v___x_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_snd_3454_);
v___y_3437_ = v___x_3455_;
goto v___jp_3436_;
}
v___jp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3432_, v___y_3433_, v_inputCtx_3424_);
lean_dec(v___x_3434_);
v___x_3435_ = l_IO_Promise_result_x21___redArg(v___x_3429_);
lean_dec(v___x_3429_);
return v___x_3435_;
}
v___jp_3436_:
{
uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3438_ = 1;
v___x_3439_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
v___x_3440_ = lean_box(v___x_3438_);
lean_inc(v___x_3429_);
v___x_3441_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3441_, 0, v___y_3437_);
lean_closure_set(v___x_3441_, 1, v_parserState_3425_);
lean_closure_set(v___x_3441_, 2, v_commandState_3426_);
lean_closure_set(v___x_3441_, 3, v___x_3429_);
lean_closure_set(v___x_3441_, 4, v___x_3440_);
lean_closure_set(v___x_3441_, 5, v___x_3430_);
lean_closure_set(v___x_3441_, 6, v___x_3439_);
if (lean_obj_tag(v_old_x3f_3427_) == 0)
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
v___y_3432_ = v___x_3441_;
v___y_3433_ = v___x_3442_;
goto v___jp_3431_;
}
else
{
lean_object* v_val_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3451_; 
v_val_3443_ = lean_ctor_get(v_old_x3f_3427_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_old_x3f_3427_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3445_ = v_old_x3f_3427_;
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_val_3443_);
lean_dec(v_old_x3f_3427_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_fst_3447_; lean_object* v___x_3449_; 
v_fst_3447_ = lean_ctor_get(v_val_3443_, 0);
lean_inc(v_fst_3447_);
lean_dec(v_val_3443_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v_fst_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_fst_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v___y_3432_ = v___x_3441_;
v___y_3433_ = v___x_3449_;
goto v___jp_3431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3456_, lean_object* v_parserState_3457_, lean_object* v_commandState_3458_, lean_object* v_old_x3f_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3456_, v_parserState_3457_, v_commandState_3458_, v_old_x3f_3459_);
lean_dec_ref(v_inputCtx_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3462_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3463_; 
v_nextCmdSnap_x3f_3463_ = lean_ctor_get(v_snap_3462_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3463_) == 1)
{
lean_object* v_val_3464_; lean_object* v___x_3465_; 
lean_inc_ref(v_nextCmdSnap_x3f_3463_);
lean_dec_ref(v_snap_3462_);
v_val_3464_ = lean_ctor_get(v_nextCmdSnap_x3f_3463_, 0);
lean_inc(v_val_3464_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3463_, 1);
v___x_3465_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3464_);
v_snap_3462_ = v___x_3465_;
goto _start;
}
else
{
lean_object* v_elabSnap_3467_; lean_object* v_resultSnap_3468_; lean_object* v___x_3469_; lean_object* v_cmdState_3470_; lean_object* v___x_3471_; 
v_elabSnap_3467_ = lean_ctor_get(v_snap_3462_, 3);
lean_inc_ref(v_elabSnap_3467_);
lean_dec_ref(v_snap_3462_);
v_resultSnap_3468_ = lean_ctor_get(v_elabSnap_3467_, 2);
lean_inc_ref(v_resultSnap_3468_);
lean_dec_ref(v_elabSnap_3467_);
v___x_3469_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3468_);
v_cmdState_3470_ = lean_ctor_get(v___x_3469_, 1);
lean_inc_ref(v_cmdState_3470_);
lean_dec(v___x_3469_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v_cmdState_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3472_){
_start:
{
lean_object* v_result_x3f_3473_; 
v_result_x3f_3473_ = lean_ctor_get(v_snap_3472_, 4);
lean_inc(v_result_x3f_3473_);
lean_dec_ref(v_snap_3472_);
if (lean_obj_tag(v_result_x3f_3473_) == 0)
{
lean_object* v___x_3474_; 
v___x_3474_ = lean_box(0);
return v___x_3474_;
}
else
{
lean_object* v_val_3475_; lean_object* v_processedSnap_3476_; lean_object* v___x_3477_; lean_object* v_result_x3f_3478_; 
v_val_3475_ = lean_ctor_get(v_result_x3f_3473_, 0);
lean_inc(v_val_3475_);
lean_dec_ref_known(v_result_x3f_3473_, 1);
v_processedSnap_3476_ = lean_ctor_get(v_val_3475_, 1);
lean_inc_ref(v_processedSnap_3476_);
lean_dec(v_val_3475_);
v___x_3477_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3476_);
v_result_x3f_3478_ = lean_ctor_get(v___x_3477_, 2);
lean_inc(v_result_x3f_3478_);
lean_dec(v___x_3477_);
if (lean_obj_tag(v_result_x3f_3478_) == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_box(0);
return v___x_3479_;
}
else
{
lean_object* v_val_3480_; lean_object* v_firstCmdSnap_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_val_3480_ = lean_ctor_get(v_result_x3f_3478_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_result_x3f_3478_, 1);
v_firstCmdSnap_3481_ = lean_ctor_get(v_val_3480_, 1);
lean_inc_ref(v_firstCmdSnap_3481_);
lean_dec(v_val_3480_);
v___x_3482_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3481_);
v___x_3483_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3482_);
return v___x_3483_;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = 1;
v___x_3490_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3491_ = l_Lean_Name_toString(v___x_3490_, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3492_ = 0;
v___x_3493_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3494_ = lean_box(0);
v___x_3495_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3496_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3497_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v___x_3495_);
lean_ctor_set(v___x_3497_, 2, v___x_3494_);
lean_ctor_set(v___x_3497_, 3, v___x_3493_);
lean_ctor_set_uint8(v___x_3497_, sizeof(void*)*4, v___x_3492_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3499_ = lean_box(0);
v___x_3500_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3499_, v___x_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3501_){
_start:
{
lean_object* v_result_x3f_3502_; 
v_result_x3f_3502_ = lean_ctor_get(v_snap_3501_, 4);
lean_inc(v_result_x3f_3502_);
if (lean_obj_tag(v_result_x3f_3502_) == 1)
{
lean_object* v_val_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3577_; 
v_val_3503_ = lean_ctor_get(v_result_x3f_3502_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_result_x3f_3502_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3505_ = v_result_x3f_3502_;
v_isShared_3506_ = v_isSharedCheck_3577_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_val_3503_);
lean_dec(v_result_x3f_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3577_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_toSnapshot_3507_; lean_object* v_metaSnap_3508_; lean_object* v_ictx_3509_; lean_object* v_stx_3510_; lean_object* v_parserState_3511_; lean_object* v_processedSnap_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3576_; 
v_toSnapshot_3507_ = lean_ctor_get(v_snap_3501_, 0);
v_metaSnap_3508_ = lean_ctor_get(v_snap_3501_, 1);
v_ictx_3509_ = lean_ctor_get(v_snap_3501_, 2);
v_stx_3510_ = lean_ctor_get(v_snap_3501_, 3);
v_parserState_3511_ = lean_ctor_get(v_val_3503_, 0);
v_processedSnap_3512_ = lean_ctor_get(v_val_3503_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_val_3503_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3514_ = v_val_3503_;
v_isShared_3515_ = v_isSharedCheck_3576_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_processedSnap_3512_);
lean_inc(v_parserState_3511_);
lean_dec(v_val_3503_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3576_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_processed_3516_; lean_object* v_result_x3f_3517_; 
v_processed_3516_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3512_);
v_result_x3f_3517_ = lean_ctor_get(v_processed_3516_, 2);
lean_inc(v_result_x3f_3517_);
if (lean_obj_tag(v_result_x3f_3517_) == 1)
{
lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3570_; 
lean_inc(v_stx_3510_);
lean_inc_ref(v_ictx_3509_);
lean_inc_ref(v_metaSnap_3508_);
lean_inc_ref(v_toSnapshot_3507_);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_snap_3501_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; lean_object* v_unused_3574_; lean_object* v_unused_3575_; 
v_unused_3571_ = lean_ctor_get(v_snap_3501_, 4);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_snap_3501_, 3);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_snap_3501_, 2);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_snap_3501_, 1);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v_snap_3501_, 0);
lean_dec(v_unused_3575_);
v___x_3519_ = v_snap_3501_;
v_isShared_3520_ = v_isSharedCheck_3570_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v_snap_3501_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3570_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_val_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3569_; 
v_val_3521_ = lean_ctor_get(v_result_x3f_3517_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_result_x3f_3517_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3523_ = v_result_x3f_3517_;
v_isShared_3524_ = v_isSharedCheck_3569_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_val_3521_);
lean_dec(v_result_x3f_3517_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3569_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v_toSnapshot_3525_; lean_object* v_metaSnap_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3567_; 
v_toSnapshot_3525_ = lean_ctor_get(v_processed_3516_, 0);
v_metaSnap_3526_ = lean_ctor_get(v_processed_3516_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_processed_3516_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v_processed_3516_, 2);
lean_dec(v_unused_3568_);
v___x_3528_ = v_processed_3516_;
v_isShared_3529_ = v_isSharedCheck_3567_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_metaSnap_3526_);
lean_inc(v_toSnapshot_3525_);
lean_dec(v_processed_3516_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3567_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_cmdState_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3565_; 
v_cmdState_3530_ = lean_ctor_get(v_val_3521_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_val_3521_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v_val_3521_, 1);
lean_dec(v_unused_3566_);
v___x_3532_ = v_val_3521_;
v_isShared_3533_ = v_isSharedCheck_3565_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_cmdState_3530_);
lean_dec(v_val_3521_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3565_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v_resultSnap_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v_elabSnap_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_termCmd_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
lean_inc_ref(v_cmdState_3530_);
v_resultSnap_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_resultSnap_3536_, 0, v___x_3535_);
lean_ctor_set(v_resultSnap_3536_, 1, v_cmdState_3530_);
v___x_3537_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
v___x_3538_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3534_, v_resultSnap_3536_);
v___x_3539_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3540_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v_elabSnap_3541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3541_, 0, v___x_3535_);
lean_ctor_set(v_elabSnap_3541_, 1, v___x_3537_);
lean_ctor_set(v_elabSnap_3541_, 2, v___x_3538_);
lean_ctor_set(v_elabSnap_3541_, 3, v___x_3539_);
lean_ctor_set(v_elabSnap_3541_, 4, v___x_3540_);
v___x_3542_ = lean_box(0);
v___x_3543_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3544_, 0, v___x_3535_);
lean_ctor_set(v_termCmd_3544_, 1, v___x_3542_);
lean_ctor_set(v_termCmd_3544_, 2, v___x_3543_);
lean_ctor_set(v_termCmd_3544_, 3, v_elabSnap_3541_);
lean_ctor_set(v_termCmd_3544_, 4, v___x_3534_);
v___x_3545_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3534_, v_termCmd_3544_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 1, v___x_3545_);
v___x_3547_ = v___x_3532_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_cmdState_3530_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3549_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3547_);
v___x_3549_ = v___x_3523_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v_newProcessed_3551_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 2, v___x_3549_);
v_newProcessed_3551_ = v___x_3528_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_toSnapshot_3525_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_metaSnap_3526_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v___x_3549_);
v_newProcessed_3551_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3552_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3534_, v_newProcessed_3551_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v___x_3552_);
v___x_3554_ = v___x_3514_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_parserState_3511_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3556_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3554_);
v___x_3556_ = v___x_3505_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3558_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 4, v___x_3556_);
v___x_3558_ = v___x_3519_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_toSnapshot_3507_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_metaSnap_3508_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_ictx_3509_);
lean_ctor_set(v_reuseFailAlloc_3559_, 3, v_stx_3510_);
lean_ctor_set(v_reuseFailAlloc_3559_, 4, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
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
lean_dec(v_result_x3f_3517_);
lean_dec(v_processed_3516_);
lean_del_object(v___x_3514_);
lean_dec_ref(v_parserState_3511_);
lean_del_object(v___x_3505_);
return v_snap_3501_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3502_);
return v_snap_3501_;
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

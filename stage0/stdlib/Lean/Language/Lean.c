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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
extern lean_object* l_Lean_internal_cmdlineSnapshots;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
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
static lean_once_cell_t l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4;
static const lean_string_object l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parseCmd"};
static const lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5 = (const lean_object*)&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5_value;
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
lean_object* v_val_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_val_64_ = lean_ctor_get(v_firstDiffPos_x3f_62_, 0);
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v_pos_59_, v___x_65_);
v___x_67_ = lean_nat_dec_le(v___x_66_, v_val_64_);
lean_dec(v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object* v_pos_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_68_, v_a_69_);
lean_dec_ref(v_a_69_);
lean_dec(v_pos_68_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13(void){
_start:
{
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = 1;
v___x_105_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__12));
v___x_106_ = l_Lean_Name_toString(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(32u);
v___x_108_ = lean_mk_empty_array_with_capacity(v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15(void){
_start:
{
size_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_110_ = ((size_t)5ULL);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_unsigned_to_nat(32u);
v___x_113_ = lean_mk_empty_array_with_capacity(v___x_112_);
v___x_114_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_115_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_111_);
lean_ctor_set(v___x_115_, 3, v___x_111_);
lean_ctor_set_usize(v___x_115_, 4, v___x_110_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16(void){
_start:
{
lean_object* v___x_116_; uint64_t v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__15);
v___x_117_ = 0ULL;
v___x_118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint64(v___x_118_, sizeof(void*)*1, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(lean_object* v_ex_119_, lean_object* v_act_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
lean_inc_ref(v_a_121_);
v___x_123_ = lean_apply_2(v_act_120_, v_a_121_, lean_box(0));
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; 
lean_dec(v_ex_119_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_123_, 1);
return v_a_124_;
}
else
{
lean_object* v_a_125_; lean_object* v_toProcessingContext_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_a_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_123_, 1);
v_toProcessingContext_126_ = lean_ctor_get(v_a_121_, 0);
v___x_127_ = lean_io_error_to_string(v_a_125_);
v___x_128_ = l_Lean_Language_diagnosticsOfHeaderError(v___x_127_, v_toProcessingContext_126_);
v___x_129_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__13);
v___x_130_ = lean_box(0);
v___x_131_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_132_ = 0;
v___x_133_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_133_, 0, v___x_129_);
lean_ctor_set(v___x_133_, 1, v___x_128_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
lean_ctor_set(v___x_133_, 3, v___x_131_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*4, v___x_132_);
v___x_134_ = lean_apply_1(v_ex_119_, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___boxed(lean_object* v_ex_135_, lean_object* v_act_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_135_, v_act_136_, v_a_137_);
lean_dec_ref(v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object* v_00_u03b1_140_, lean_object* v_ex_141_, lean_object* v_act_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v_ex_141_, v_act_142_, v_a_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed(lean_object* v_00_u03b1_146_, lean_object* v_ex_147_, lean_object* v_act_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(v_00_u03b1_146_, v_ex_147_, v_act_148_, v_a_149_);
lean_dec_ref(v_a_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(lean_object* v_o_155_, lean_object* v_k_156_, uint8_t v_v_157_){
_start:
{
lean_object* v_map_158_; uint8_t v_hasTrace_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_173_; 
v_map_158_ = lean_ctor_get(v_o_155_, 0);
v_hasTrace_159_ = lean_ctor_get_uint8(v_o_155_, sizeof(void*)*1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_o_155_);
if (v_isSharedCheck_173_ == 0)
{
v___x_161_ = v_o_155_;
v_isShared_162_ = v_isSharedCheck_173_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_map_158_);
lean_dec(v_o_155_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_173_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_163_, 0, v_v_157_);
lean_inc(v_k_156_);
v___x_164_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_156_, v___x_163_, v_map_158_);
if (v_hasTrace_159_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_166_ = l_Lean_Name_isPrefixOf(v___x_165_, v_k_156_);
lean_dec(v_k_156_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_164_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_166_);
return v___x_168_;
}
}
else
{
lean_object* v___x_171_; 
lean_dec(v_k_156_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_171_ = v___x_161_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*1, v_hasTrace_159_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___boxed(lean_object* v_o_174_, lean_object* v_k_175_, lean_object* v_v_176_){
_start:
{
uint8_t v_v_boxed_177_; lean_object* v_res_178_; 
v_v_boxed_177_ = lean_unbox(v_v_176_);
v_res_178_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_o_174_, v_k_175_, v_v_boxed_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(lean_object* v_o_179_, lean_object* v_k_180_, lean_object* v_v_181_){
_start:
{
lean_object* v_map_182_; uint8_t v_hasTrace_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_197_; 
v_map_182_ = lean_ctor_get(v_o_179_, 0);
v_hasTrace_183_ = lean_ctor_get_uint8(v_o_179_, sizeof(void*)*1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_o_179_);
if (v_isSharedCheck_197_ == 0)
{
v___x_185_ = v_o_179_;
v_isShared_186_ = v_isSharedCheck_197_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_map_182_);
lean_dec(v_o_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_197_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v_v_181_);
lean_inc(v_k_180_);
v___x_188_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_180_, v___x_187_, v_map_182_);
if (v_hasTrace_183_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_192_; 
v___x_189_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_190_ = l_Lean_Name_isPrefixOf(v___x_189_, v_k_180_);
lean_dec(v_k_180_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_188_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_190_);
return v___x_192_;
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_k_180_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_195_ = v___x_185_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_196_, sizeof(void*)*1, v_hasTrace_183_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(lean_object* v_o_198_, lean_object* v_k_199_, lean_object* v_v_200_){
_start:
{
lean_object* v_map_201_; uint8_t v_hasTrace_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_216_; 
v_map_201_ = lean_ctor_get(v_o_198_, 0);
v_hasTrace_202_ = lean_ctor_get_uint8(v_o_198_, sizeof(void*)*1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_o_198_);
if (v_isSharedCheck_216_ == 0)
{
v___x_204_ = v_o_198_;
v_isShared_205_ = v_isSharedCheck_216_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_map_201_);
lean_dec(v_o_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_216_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v_v_200_);
lean_inc(v_k_199_);
v___x_207_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_199_, v___x_206_, v_map_201_);
if (v_hasTrace_202_ == 0)
{
lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_211_; 
v___x_208_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_209_ = l_Lean_Name_isPrefixOf(v___x_208_, v_k_199_);
lean_dec(v_k_199_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_211_ = v___x_204_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_207_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_209_);
return v___x_211_;
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_k_199_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_214_ = v___x_204_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*1, v_hasTrace_202_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption(lean_object* v_opts_224_, lean_object* v_decl_225_, lean_object* v_name_226_, lean_object* v_val_227_){
_start:
{
lean_object* v_defValue_229_; 
v_defValue_229_ = lean_ctor_get(v_decl_225_, 2);
lean_inc_ref(v_defValue_229_);
lean_dec_ref(v_decl_225_);
switch(lean_obj_tag(v_defValue_229_))
{
case 1:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
lean_dec_ref_known(v_defValue_229_, 0);
v___x_230_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__0));
v___x_231_ = lean_string_dec_eq(v_val_227_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__1));
v___x_233_ = lean_string_dec_eq(v_val_227_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_name_226_);
lean_dec_ref(v_opts_224_);
v___x_234_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_235_ = lean_string_append(v___x_234_, v_val_227_);
lean_dec_ref(v_val_227_);
v___x_236_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__3));
v___x_237_ = lean_string_append(v___x_235_, v___x_236_);
v___x_238_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_val_227_);
v___x_240_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_224_, v_name_226_, v___x_231_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v_val_227_);
v___x_242_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0(v_opts_224_, v_name_226_, v___x_231_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
case 3:
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_268_; 
v_isSharedCheck_268_ = !lean_is_exclusive(v_defValue_229_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; 
v_unused_269_ = lean_ctor_get(v_defValue_229_, 0);
lean_dec(v_unused_269_);
v___x_245_ = v_defValue_229_;
v_isShared_246_ = v_isSharedCheck_268_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_defValue_229_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_268_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_string_utf8_byte_size(v_val_227_);
lean_inc_ref(v_val_227_);
v___x_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_249_, 0, v_val_227_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_248_);
v___x_250_ = l_String_Slice_toNat_x3f(v___x_249_);
lean_dec_ref_known(v___x_249_, 3);
if (lean_obj_tag(v___x_250_) == 1)
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
lean_del_object(v___x_245_);
lean_dec_ref(v_val_227_);
v_val_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_259_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__1(v_opts_224_, v_name_226_, v_val_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 0);
lean_ctor_set(v___x_253_, 0, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
lean_dec(v___x_250_);
lean_dec(v_name_226_);
lean_dec_ref(v_opts_224_);
v___x_260_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__2));
v___x_261_ = lean_string_append(v___x_260_, v_val_227_);
lean_dec_ref(v_val_227_);
v___x_262_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__4));
v___x_263_ = lean_string_append(v___x_261_, v___x_262_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 18);
lean_ctor_set(v___x_245_, 0, v___x_263_);
v___x_265_ = v___x_245_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_267_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
}
}
case 0:
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_isSharedCheck_277_ = !lean_is_exclusive(v_defValue_229_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_defValue_229_, 0);
lean_dec(v_unused_278_);
v___x_271_ = v_defValue_229_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_defValue_229_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__2(v_opts_224_, v_name_226_, v_val_227_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
default: 
{
lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v_defValue_229_);
lean_dec_ref(v_val_227_);
lean_dec_ref(v_opts_224_);
v___x_279_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__5));
v___x_280_ = 1;
v___x_281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_226_, v___x_280_);
v___x_282_ = lean_string_append(v___x_279_, v___x_281_);
lean_dec_ref(v___x_281_);
v___x_283_ = ((lean_object*)(l_Lean_Language_Lean_setOption___closed__6));
v___x_284_ = lean_string_append(v___x_282_, v___x_283_);
v___x_285_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_setOption___boxed(lean_object* v_opts_287_, lean_object* v_decl_288_, lean_object* v_name_289_, lean_object* v_val_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Language_Lean_setOption(v_opts_287_, v_decl_288_, v_name_289_, v_val_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(lean_object* v_o_293_, lean_object* v_k_294_, lean_object* v_v_295_){
_start:
{
lean_object* v_map_296_; uint8_t v_hasTrace_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_310_; 
v_map_296_ = lean_ctor_get(v_o_293_, 0);
v_hasTrace_297_ = lean_ctor_get_uint8(v_o_293_, sizeof(void*)*1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_o_293_);
if (v_isSharedCheck_310_ == 0)
{
v___x_299_ = v_o_293_;
v_isShared_300_ = v_isSharedCheck_310_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_map_296_);
lean_dec(v_o_293_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_310_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; 
lean_inc(v_k_294_);
v___x_301_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_294_, v_v_295_, v_map_296_);
if (v_hasTrace_297_ == 0)
{
lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_305_; 
v___x_302_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_303_ = l_Lean_Name_isPrefixOf(v___x_302_, v_k_294_);
lean_dec(v_k_294_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_305_ = v___x_299_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_301_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_303_);
return v___x_305_;
}
}
else
{
lean_object* v___x_308_; 
lean_dec(v_k_294_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_308_ = v___x_299_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_309_, sizeof(void*)*1, v_hasTrace_297_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(lean_object* v_a_317_, lean_object* v_init_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_d_322_; 
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v_l_327_; lean_object* v_r_328_; lean_object* v___x_329_; 
v_k_325_ = lean_ctor_get(v_x_319_, 1);
lean_inc(v_k_325_);
v_v_326_ = lean_ctor_get(v_x_319_, 2);
lean_inc(v_v_326_);
v_l_327_ = lean_ctor_get(v_x_319_, 3);
lean_inc(v_l_327_);
v_r_328_ = lean_ctor_get(v_x_319_, 4);
lean_inc(v_r_328_);
lean_dec_ref_known(v_x_319_, 5);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_317_, v_init_318_, v_l_327_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
if (lean_obj_tag(v_a_330_) == 0)
{
lean_object* v_a_331_; 
lean_dec_ref_known(v___x_329_, 1);
lean_dec(v_r_328_);
lean_dec(v_v_326_);
lean_dec(v_k_325_);
v_a_331_ = lean_ctor_get(v_a_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v_a_330_, 1);
v_d_322_ = v_a_331_;
goto v___jp_321_;
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_383_; 
v_a_332_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_383_ == 0)
{
v___x_334_ = v_a_330_;
v_isShared_335_ = v_isSharedCheck_383_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v_a_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_383_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_336_ = l_Lean_Name_getRoot(v_k_325_);
v___x_337_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__1));
v___x_338_ = lean_box(0);
v___x_339_ = l_Lean_Name_replacePrefix(v_k_325_, v___x_337_, v___x_338_);
v___x_340_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_317_, v___x_339_);
if (lean_obj_tag(v___x_340_) == 1)
{
lean_dec(v___x_336_);
lean_del_object(v___x_334_);
lean_dec_ref_known(v___x_329_, 1);
if (lean_obj_tag(v_v_326_) == 0)
{
lean_object* v_val_341_; lean_object* v_v_342_; lean_object* v___x_343_; 
v_val_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_340_, 1);
v_v_342_ = lean_ctor_get(v_v_326_, 0);
lean_inc_ref(v_v_342_);
lean_dec_ref_known(v_v_326_, 1);
v___x_343_ = l_Lean_Language_Lean_setOption(v_a_332_, v_val_341_, v___x_339_, v_v_342_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v_init_318_ = v_a_344_;
v_x_319_ = v_r_328_;
goto _start;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_r_328_);
v_a_346_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_343_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_343_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v___x_354_; 
lean_dec_ref_known(v___x_340_, 1);
v___x_354_ = l_Lean_Options_set___at___00Lean_Language_Lean_reparseOptions_spec__0(v_a_332_, v___x_339_, v_v_326_);
v_init_318_ = v___x_354_;
v_x_319_ = v_r_328_;
goto _start;
}
}
else
{
uint8_t v___x_356_; 
lean_dec(v___x_340_);
lean_dec(v_a_332_);
lean_dec(v_v_326_);
v___x_356_ = lean_name_eq(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_r_328_);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_329_, 0);
lean_dec(v_unused_378_);
v___x_358_ = v___x_329_;
v_isShared_359_ = v_isSharedCheck_377_;
goto v_resetjp_357_;
}
else
{
lean_dec(v___x_329_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_377_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_360_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__2));
v___x_361_ = 1;
lean_inc(v___x_339_);
v___x_362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_339_, v___x_361_);
v___x_363_ = lean_string_append(v___x_360_, v___x_362_);
lean_dec_ref(v___x_362_);
v___x_364_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__3));
v___x_365_ = lean_string_append(v___x_363_, v___x_364_);
v___x_366_ = l_Lean_Name_append(v___x_337_, v___x_339_);
v___x_367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_366_, v___x_361_);
v___x_368_ = lean_string_append(v___x_365_, v___x_367_);
lean_dec_ref(v___x_367_);
v___x_369_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___closed__4));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 18);
lean_ctor_set(v___x_334_, 0, v___x_370_);
v___x_372_ = v___x_334_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 1);
lean_ctor_set(v___x_358_, 0, v___x_372_);
v___x_374_ = v___x_358_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_dec(v___x_339_);
lean_del_object(v___x_334_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_329_, 1);
if (lean_obj_tag(v_a_379_) == 0)
{
lean_object* v_a_380_; 
lean_dec(v_r_328_);
v_a_380_ = lean_ctor_get(v_a_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v_a_379_, 1);
v_d_322_ = v_a_380_;
goto v___jp_321_;
}
else
{
lean_object* v_a_381_; 
v_a_381_ = lean_ctor_get(v_a_379_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v_a_379_, 1);
v_init_318_ = v_a_381_;
v_x_319_ = v_r_328_;
goto _start;
}
}
else
{
lean_dec(v_r_328_);
return v___x_329_;
}
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
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v_init_318_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
v___jp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v_d_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1___boxed(lean_object* v_a_386_, lean_object* v_init_387_, lean_object* v_x_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_386_, v_init_387_, v_x_388_);
lean_dec(v_a_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions(lean_object* v_opts_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v_map_395_; lean_object* v_opts_x27_396_; lean_object* v___x_397_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
v_map_395_ = lean_ctor_get(v_opts_391_, 0);
lean_inc(v_map_395_);
lean_dec_ref(v_opts_391_);
v_opts_x27_396_ = l_Lean_Options_empty;
v___x_397_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Language_Lean_reparseOptions_spec__1(v_a_394_, v_opts_x27_396_, v_map_395_);
lean_dec(v_a_394_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_a_402_; lean_object* v___x_404_; 
v_a_402_ = lean_ctor_get(v_a_398_, 0);
lean_inc(v_a_402_);
lean_dec(v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_a_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_397_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_397_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v_opts_391_);
v_a_415_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_393_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_393_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_reparseOptions___boxed(lean_object* v_opts_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Language_Lean_reparseOptions(v_opts_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(lean_object* v_stx_434_){
_start:
{
lean_object* v_stx_436_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = l_Lean_Syntax_getArg(v_stx_434_, v___x_439_);
v___x_441_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f___closed__3));
v___x_442_ = l_Lean_Syntax_isOfKind(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
v_stx_436_ = v_stx_434_;
goto v___jp_435_;
}
else
{
lean_object* v___x_443_; lean_object* v_stx_444_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v_stx_444_ = l_Lean_Syntax_getArg(v_stx_434_, v___x_443_);
lean_dec(v_stx_434_);
v_stx_436_ = v_stx_444_;
goto v___jp_435_;
}
v___jp_435_:
{
uint8_t v___x_437_; lean_object* v___x_438_; 
v___x_437_ = 0;
v___x_438_ = l_Lean_Syntax_getPos_x3f(v_stx_436_, v___x_437_);
lean_dec(v_stx_436_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(lean_object* v_name_445_, lean_object* v_decl_446_, lean_object* v_ref_447_){
_start:
{
lean_object* v_defValue_449_; lean_object* v_descr_450_; lean_object* v_deprecation_x3f_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_defValue_449_ = lean_ctor_get(v_decl_446_, 0);
v_descr_450_ = lean_ctor_get(v_decl_446_, 1);
v_deprecation_x3f_451_ = lean_ctor_get(v_decl_446_, 2);
v___x_452_ = lean_alloc_ctor(1, 0, 1);
v___x_453_ = lean_unbox(v_defValue_449_);
lean_ctor_set_uint8(v___x_452_, 0, v___x_453_);
lean_inc(v_deprecation_x3f_451_);
lean_inc_ref(v_descr_450_);
lean_inc_n(v_name_445_, 2);
v___x_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_454_, 0, v_name_445_);
lean_ctor_set(v___x_454_, 1, v_ref_447_);
lean_ctor_set(v___x_454_, 2, v___x_452_);
lean_ctor_set(v___x_454_, 3, v_descr_450_);
lean_ctor_set(v___x_454_, 4, v_deprecation_x3f_451_);
v___x_455_ = lean_register_option(v_name_445_, v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v___x_455_, 0);
lean_dec(v_unused_464_);
v___x_457_ = v___x_455_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_dec(v___x_455_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_inc(v_defValue_449_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_name_445_);
lean_ctor_set(v___x_459_, 1, v_defValue_449_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_name_445_);
v_a_465_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_455_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_455_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_473_, lean_object* v_decl_474_, lean_object* v_ref_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v_name_473_, v_decl_474_, v_ref_475_);
lean_dec_ref(v_decl_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__2_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_496_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__4_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_497_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn___closed__5_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_));
v___x_498_ = l_Lean_Option_register___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4__spec__0(v___x_495_, v___x_496_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4____boxed(lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_initFn_00___x40_Lean_Language_Lean_3734918084____hygCtx___hyg_4_();
return v_res_500_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(32u);
v___x_502_ = lean_mk_empty_array_with_capacity(v___x_501_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = ((size_t)5ULL);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_unsigned_to_nat(32u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_506_);
v___x_508_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__0);
v___x_509_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
lean_ctor_set(v___x_509_, 2, v___x_505_);
lean_ctor_set(v___x_509_, 3, v___x_505_);
lean_ctor_set_usize(v___x_509_, 4, v___x_504_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_infoState_513_; lean_object* v_trees_514_; lean_object* v___x_515_; lean_object* v_infoState_516_; lean_object* v_env_517_; lean_object* v_messages_518_; lean_object* v_scopes_519_; lean_object* v_usedQuotCtxts_520_; lean_object* v_nextMacroScope_521_; lean_object* v_maxRecDepth_522_; lean_object* v_ngen_523_; lean_object* v_auxDeclNGen_524_; lean_object* v_traceState_525_; lean_object* v_snapshotTasks_526_; lean_object* v_prevLinterStates_527_; lean_object* v_codeQualityEntryTasks_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_549_; 
v___x_512_ = lean_st_ref_get(v___y_510_);
v_infoState_513_ = lean_ctor_get(v___x_512_, 8);
lean_inc_ref(v_infoState_513_);
lean_dec(v___x_512_);
v_trees_514_ = lean_ctor_get(v_infoState_513_, 2);
lean_inc_ref(v_trees_514_);
lean_dec_ref(v_infoState_513_);
v___x_515_ = lean_st_ref_take(v___y_510_);
v_infoState_516_ = lean_ctor_get(v___x_515_, 8);
v_env_517_ = lean_ctor_get(v___x_515_, 0);
v_messages_518_ = lean_ctor_get(v___x_515_, 1);
v_scopes_519_ = lean_ctor_get(v___x_515_, 2);
v_usedQuotCtxts_520_ = lean_ctor_get(v___x_515_, 3);
v_nextMacroScope_521_ = lean_ctor_get(v___x_515_, 4);
v_maxRecDepth_522_ = lean_ctor_get(v___x_515_, 5);
v_ngen_523_ = lean_ctor_get(v___x_515_, 6);
v_auxDeclNGen_524_ = lean_ctor_get(v___x_515_, 7);
v_traceState_525_ = lean_ctor_get(v___x_515_, 9);
v_snapshotTasks_526_ = lean_ctor_get(v___x_515_, 10);
v_prevLinterStates_527_ = lean_ctor_get(v___x_515_, 11);
v_codeQualityEntryTasks_528_ = lean_ctor_get(v___x_515_, 12);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_549_ == 0)
{
v___x_530_ = v___x_515_;
v_isShared_531_ = v_isSharedCheck_549_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_codeQualityEntryTasks_528_);
lean_inc(v_prevLinterStates_527_);
lean_inc(v_snapshotTasks_526_);
lean_inc(v_traceState_525_);
lean_inc(v_infoState_516_);
lean_inc(v_auxDeclNGen_524_);
lean_inc(v_ngen_523_);
lean_inc(v_maxRecDepth_522_);
lean_inc(v_nextMacroScope_521_);
lean_inc(v_usedQuotCtxts_520_);
lean_inc(v_scopes_519_);
lean_inc(v_messages_518_);
lean_inc(v_env_517_);
lean_dec(v___x_515_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_549_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint8_t v_enabled_532_; lean_object* v_assignment_533_; lean_object* v_lazyAssignment_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_547_; 
v_enabled_532_ = lean_ctor_get_uint8(v_infoState_516_, sizeof(void*)*3);
v_assignment_533_ = lean_ctor_get(v_infoState_516_, 0);
v_lazyAssignment_534_ = lean_ctor_get(v_infoState_516_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_infoState_516_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_infoState_516_, 2);
lean_dec(v_unused_548_);
v___x_536_ = v_infoState_516_;
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_lazyAssignment_534_);
lean_inc(v_assignment_533_);
lean_dec(v_infoState_516_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 2, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_assignment_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_lazyAssignment_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v___x_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*3, v_enabled_532_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 8, v___x_540_);
v___x_542_ = v___x_530_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_env_517_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_messages_518_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_scopes_519_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_usedQuotCtxts_520_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_nextMacroScope_521_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v_maxRecDepth_522_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_ngen_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_auxDeclNGen_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_545_, 9, v_traceState_525_);
lean_ctor_set(v_reuseFailAlloc_545_, 10, v_snapshotTasks_526_);
lean_ctor_set(v_reuseFailAlloc_545_, 11, v_prevLinterStates_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 12, v_codeQualityEntryTasks_528_);
v___x_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_st_ref_put(v___y_510_, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_trees_514_);
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_550_);
lean_dec(v___y_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_561_, lean_object* v_opt_562_){
_start:
{
lean_object* v_name_563_; lean_object* v_defValue_564_; lean_object* v_map_565_; lean_object* v___x_566_; 
v_name_563_ = lean_ctor_get(v_opt_562_, 0);
v_defValue_564_ = lean_ctor_get(v_opt_562_, 1);
v_map_565_ = lean_ctor_get(v_opts_561_, 0);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_565_, v_name_563_);
if (lean_obj_tag(v___x_566_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = lean_unbox(v_defValue_564_);
return v___x_567_;
}
else
{
lean_object* v_val_568_; 
v_val_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v___x_566_, 1);
if (lean_obj_tag(v_val_568_) == 1)
{
uint8_t v_v_569_; 
v_v_569_ = lean_ctor_get_uint8(v_val_568_, 0);
lean_dec_ref_known(v_val_568_, 0);
return v_v_569_;
}
else
{
uint8_t v___x_570_; 
lean_dec(v_val_568_);
v___x_570_ = lean_unbox(v_defValue_564_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_571_, lean_object* v_opt_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_571_, v_opt_572_);
lean_dec_ref(v_opt_572_);
lean_dec_ref(v_opts_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = l_Lean_Language_Snapshot_transform(v_val_577_, v___y_578_);
v___x_580_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_582_, v___y_583_);
lean_dec_ref(v___y_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_585_, lean_object* v_val_586_){
_start:
{
lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_inc_ref(v_val_586_);
v___f_587_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_587_, 0, v_val_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_inst_585_);
lean_ctor_set(v___x_588_, 1, v_val_586_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___f_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_590_, lean_object* v_cmds_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_593_);
lean_dec_ref(v___x_595_);
v___x_596_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_590_, v_cmds_591_, v___y_592_, v___y_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_597_, lean_object* v_cmds_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_597_, v_cmds_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_603_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_ctor_set(v___x_608_, 2, v___x_607_);
lean_ctor_set(v___x_608_, 3, v___x_607_);
lean_ctor_set(v___x_608_, 4, v___x_606_);
lean_ctor_set(v___x_608_, 5, v___x_606_);
lean_ctor_set(v___x_608_, 6, v___x_606_);
lean_ctor_set(v___x_608_, 7, v___x_606_);
lean_ctor_set(v___x_608_, 8, v___x_606_);
lean_ctor_set(v___x_608_, 9, v___x_606_);
lean_ctor_set(v___x_608_, 10, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(32u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_612_ = ((size_t)5ULL);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_unsigned_to_nat(32u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_617_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_613_);
lean_ctor_set(v___x_617_, 3, v___x_613_);
lean_ctor_set_usize(v___x_617_, 4, v___x_612_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_618_ = lean_box(1);
v___x_619_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_620_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_618_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v_env_626_; lean_object* v___x_627_; lean_object* v_scopes_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_opts_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_625_ = lean_st_ref_get(v___y_623_);
v_env_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc_ref(v_env_626_);
lean_dec(v___x_625_);
v___x_627_ = lean_st_ref_get(v___y_623_);
v_scopes_628_ = lean_ctor_get(v___x_627_, 2);
lean_inc(v_scopes_628_);
lean_dec(v___x_627_);
v___x_629_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_630_ = l_List_head_x21___redArg(v___x_629_, v_scopes_628_);
lean_dec(v_scopes_628_);
v_opts_631_ = lean_ctor_get(v___x_630_, 1);
lean_inc_ref(v_opts_631_);
lean_dec(v___x_630_);
v___x_632_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_633_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_634_, 0, v_env_626_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_ctor_set(v___x_634_, 3, v_opts_631_);
v___x_635_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_msgData_622_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_637_, v___y_638_);
lean_dec(v___y_638_);
return v_res_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_641_, uint8_t v___y_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 1)
{
lean_object* v_pre_644_; 
v_pre_644_ = lean_ctor_get(v_x_643_, 0);
if (lean_obj_tag(v_pre_644_) == 0)
{
lean_object* v_str_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_str_645_ = lean_ctor_get(v_x_643_, 1);
v___x_646_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_647_ = lean_string_dec_eq(v_str_645_, v___x_646_);
if (v___x_647_ == 0)
{
return v___x_647_;
}
else
{
return v_suppressElabErrors_641_;
}
}
else
{
return v___y_642_;
}
}
else
{
return v___y_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_648_, lean_object* v___y_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_suppressElabErrors_boxed_651_; uint8_t v___y_9108__boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_suppressElabErrors_boxed_651_ = lean_unbox(v_suppressElabErrors_648_);
v___y_9108__boxed_652_ = lean_unbox(v___y_649_);
v_res_653_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_651_, v___y_9108__boxed_652_, v_x_650_);
lean_dec(v_x_650_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_656_, lean_object* v_msgData_657_, uint8_t v_severity_658_, uint8_t v_isSilent_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; lean_object* v___y_671_; uint8_t v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; uint8_t v___y_765_; uint8_t v___y_766_; uint8_t v___y_767_; uint8_t v___x_782_; uint8_t v___y_784_; uint8_t v___y_785_; uint8_t v___y_786_; uint8_t v___y_788_; uint8_t v___x_800_; 
v___x_782_ = 2;
v___x_800_ = l_Lean_instBEqMessageSeverity_beq(v_severity_658_, v___x_782_);
if (v___x_800_ == 0)
{
v___y_788_ = v___x_800_;
goto v___jp_787_;
}
else
{
uint8_t v___x_801_; 
lean_inc_ref(v_msgData_657_);
v___x_801_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_657_);
v___y_788_ = v___x_801_;
goto v___jp_787_;
}
v___jp_663_:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Elab_Command_getScope___redArg(v___y_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_Elab_Command_getScope___redArg(v___y_671_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_711_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_711_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_711_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_711_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_currNamespace_680_; lean_object* v_openDecls_681_; lean_object* v_env_682_; lean_object* v_messages_683_; lean_object* v_scopes_684_; lean_object* v_usedQuotCtxts_685_; lean_object* v_nextMacroScope_686_; lean_object* v_maxRecDepth_687_; lean_object* v_ngen_688_; lean_object* v_auxDeclNGen_689_; lean_object* v_infoState_690_; lean_object* v_traceState_691_; lean_object* v_snapshotTasks_692_; lean_object* v_prevLinterStates_693_; lean_object* v_codeQualityEntryTasks_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_710_; 
v___x_679_ = lean_st_ref_take(v___y_671_);
v_currNamespace_680_ = lean_ctor_get(v_a_673_, 2);
lean_inc(v_currNamespace_680_);
lean_dec(v_a_673_);
v_openDecls_681_ = lean_ctor_get(v_a_675_, 3);
lean_inc(v_openDecls_681_);
lean_dec(v_a_675_);
v_env_682_ = lean_ctor_get(v___x_679_, 0);
v_messages_683_ = lean_ctor_get(v___x_679_, 1);
v_scopes_684_ = lean_ctor_get(v___x_679_, 2);
v_usedQuotCtxts_685_ = lean_ctor_get(v___x_679_, 3);
v_nextMacroScope_686_ = lean_ctor_get(v___x_679_, 4);
v_maxRecDepth_687_ = lean_ctor_get(v___x_679_, 5);
v_ngen_688_ = lean_ctor_get(v___x_679_, 6);
v_auxDeclNGen_689_ = lean_ctor_get(v___x_679_, 7);
v_infoState_690_ = lean_ctor_get(v___x_679_, 8);
v_traceState_691_ = lean_ctor_get(v___x_679_, 9);
v_snapshotTasks_692_ = lean_ctor_get(v___x_679_, 10);
v_prevLinterStates_693_ = lean_ctor_get(v___x_679_, 11);
v_codeQualityEntryTasks_694_ = lean_ctor_get(v___x_679_, 12);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_710_ == 0)
{
v___x_696_ = v___x_679_;
v_isShared_697_ = v_isSharedCheck_710_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_codeQualityEntryTasks_694_);
lean_inc(v_prevLinterStates_693_);
lean_inc(v_snapshotTasks_692_);
lean_inc(v_traceState_691_);
lean_inc(v_infoState_690_);
lean_inc(v_auxDeclNGen_689_);
lean_inc(v_ngen_688_);
lean_inc(v_maxRecDepth_687_);
lean_inc(v_nextMacroScope_686_);
lean_inc(v_usedQuotCtxts_685_);
lean_inc(v_scopes_684_);
lean_inc(v_messages_683_);
lean_inc(v_env_682_);
lean_dec(v___x_679_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_710_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_currNamespace_680_);
lean_ctor_set(v___x_698_, 1, v_openDecls_681_);
v___x_699_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___y_664_);
lean_inc_ref(v___y_669_);
lean_inc_ref(v___y_665_);
v___x_700_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_700_, 0, v___y_665_);
lean_ctor_set(v___x_700_, 1, v___y_668_);
lean_ctor_set(v___x_700_, 2, v___y_667_);
lean_ctor_set(v___x_700_, 3, v___y_669_);
lean_ctor_set(v___x_700_, 4, v___x_699_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5, v___y_670_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 1, v___y_666_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*5 + 2, v_isSilent_659_);
v___x_701_ = l_Lean_MessageLog_add(v___x_700_, v_messages_683_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_701_);
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_env_682_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_scopes_684_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_usedQuotCtxts_685_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_nextMacroScope_686_);
lean_ctor_set(v_reuseFailAlloc_709_, 5, v_maxRecDepth_687_);
lean_ctor_set(v_reuseFailAlloc_709_, 6, v_ngen_688_);
lean_ctor_set(v_reuseFailAlloc_709_, 7, v_auxDeclNGen_689_);
lean_ctor_set(v_reuseFailAlloc_709_, 8, v_infoState_690_);
lean_ctor_set(v_reuseFailAlloc_709_, 9, v_traceState_691_);
lean_ctor_set(v_reuseFailAlloc_709_, 10, v_snapshotTasks_692_);
lean_ctor_set(v_reuseFailAlloc_709_, 11, v_prevLinterStates_693_);
lean_ctor_set(v_reuseFailAlloc_709_, 12, v_codeQualityEntryTasks_694_);
v___x_703_ = v_reuseFailAlloc_709_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_704_ = lean_st_ref_put(v___y_671_, v___x_703_);
v___x_705_ = lean_box(0);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_705_);
v___x_707_ = v___x_677_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_a_673_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_664_);
v_a_712_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_674_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_674_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
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
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_664_);
v_a_720_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_672_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_672_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
v___jp_728_:
{
lean_object* v_fileName_734_; lean_object* v_fileMap_735_; uint8_t v_suppressElabErrors_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_755_; 
v_fileName_734_ = lean_ctor_get(v___y_660_, 0);
v_fileMap_735_ = lean_ctor_get(v___y_660_, 1);
v_suppressElabErrors_736_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*10);
v___x_737_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_657_);
v___x_738_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_737_, v___y_661_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_755_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_755_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_755_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_inc_ref_n(v_fileMap_735_, 2);
v___x_743_ = l_Lean_FileMap_toPosition(v_fileMap_735_, v___y_730_);
lean_dec(v___y_730_);
v___x_744_ = l_Lean_FileMap_toPosition(v_fileMap_735_, v___y_733_);
lean_dec(v___y_733_);
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_736_ == 0)
{
lean_del_object(v___x_741_);
v___y_664_ = v_a_739_;
v___y_665_ = v_fileName_734_;
v___y_666_ = v___y_731_;
v___y_667_ = v___x_745_;
v___y_668_ = v___x_743_;
v___y_669_ = v___x_746_;
v___y_670_ = v___y_732_;
v___y_671_ = v___y_661_;
goto v___jp_663_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; uint8_t v___x_750_; 
v___x_747_ = lean_box(v_suppressElabErrors_736_);
v___x_748_ = lean_box(v___y_729_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_749_, 0, v___x_747_);
lean_closure_set(v___f_749_, 1, v___x_748_);
lean_inc(v_a_739_);
v___x_750_ = l_Lean_MessageData_hasTag(v___f_749_, v_a_739_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec_ref_known(v___x_745_, 1);
lean_dec_ref(v___x_743_);
lean_dec(v_a_739_);
v___x_751_ = lean_box(0);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_751_);
v___x_753_ = v___x_741_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_del_object(v___x_741_);
v___y_664_ = v_a_739_;
v___y_665_ = v_fileName_734_;
v___y_666_ = v___y_731_;
v___y_667_ = v___x_745_;
v___y_668_ = v___x_743_;
v___y_669_ = v___x_746_;
v___y_670_ = v___y_732_;
v___y_671_ = v___y_661_;
goto v___jp_663_;
}
}
}
}
v___jp_756_:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Syntax_getTailPos_x3f(v___y_759_, v___y_760_);
lean_dec(v___y_759_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_inc(v___y_761_);
v___y_729_ = v___y_757_;
v___y_730_ = v___y_761_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_761_;
goto v___jp_728_;
}
else
{
lean_object* v_val_763_; 
v_val_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_763_);
lean_dec_ref_known(v___x_762_, 1);
v___y_729_ = v___y_757_;
v___y_730_ = v___y_761_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_760_;
v___y_733_ = v_val_763_;
goto v___jp_728_;
}
}
v___jp_764_:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Elab_Command_getRef___redArg(v___y_660_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_ref_770_; lean_object* v___x_771_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v_ref_770_ = l_Lean_replaceRef(v_ref_656_, v_a_769_);
lean_dec(v_a_769_);
v___x_771_ = l_Lean_Syntax_getPos_x3f(v_ref_770_, v___y_766_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v___y_757_ = v___y_765_;
v___y_758_ = v___y_767_;
v___y_759_ = v_ref_770_;
v___y_760_ = v___y_766_;
v___y_761_ = v___x_772_;
goto v___jp_756_;
}
else
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_771_, 1);
v___y_757_ = v___y_765_;
v___y_758_ = v___y_767_;
v___y_759_ = v_ref_770_;
v___y_760_ = v___y_766_;
v___y_761_ = v_val_773_;
goto v___jp_756_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_msgData_657_);
v_a_774_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_768_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_768_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
v___jp_783_:
{
if (v___y_786_ == 0)
{
v___y_765_ = v___y_784_;
v___y_766_ = v___y_785_;
v___y_767_ = v_severity_658_;
goto v___jp_764_;
}
else
{
v___y_765_ = v___y_784_;
v___y_766_ = v___y_785_;
v___y_767_ = v___x_782_;
goto v___jp_764_;
}
}
v___jp_787_:
{
if (v___y_788_ == 0)
{
lean_object* v___x_789_; lean_object* v_scopes_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_opts_793_; uint8_t v___x_794_; uint8_t v___x_795_; 
v___x_789_ = lean_st_ref_get(v___y_661_);
v_scopes_790_ = lean_ctor_get(v___x_789_, 2);
lean_inc(v_scopes_790_);
lean_dec(v___x_789_);
v___x_791_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_792_ = l_List_head_x21___redArg(v___x_791_, v_scopes_790_);
lean_dec(v_scopes_790_);
v_opts_793_ = lean_ctor_get(v___x_792_, 1);
lean_inc_ref(v_opts_793_);
lean_dec(v___x_792_);
v___x_794_ = 1;
v___x_795_ = l_Lean_instBEqMessageSeverity_beq(v_severity_658_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec_ref(v_opts_793_);
v___y_784_ = v___y_788_;
v___y_785_ = v___y_788_;
v___y_786_ = v___x_795_;
goto v___jp_783_;
}
else
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = l_Lean_warningAsError;
v___x_797_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_793_, v___x_796_);
lean_dec_ref(v_opts_793_);
v___y_784_ = v___y_788_;
v___y_785_ = v___y_788_;
v___y_786_ = v___x_797_;
goto v___jp_783_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_msgData_657_);
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_802_, lean_object* v_msgData_803_, lean_object* v_severity_804_, lean_object* v_isSilent_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
uint8_t v_severity_boxed_809_; uint8_t v_isSilent_boxed_810_; lean_object* v_res_811_; 
v_severity_boxed_809_ = lean_unbox(v_severity_804_);
v_isSilent_boxed_810_ = lean_unbox(v_isSilent_805_);
v_res_811_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_802_, v_msgData_803_, v_severity_boxed_809_, v_isSilent_boxed_810_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v_ref_802_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_812_, uint8_t v_severity_813_, uint8_t v_isSilent_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Elab_Command_getRef___redArg(v___y_815_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_819_, v_msgData_812_, v_severity_813_, v_isSilent_814_, v___y_815_, v___y_816_);
lean_dec(v_a_819_);
return v___x_820_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v_msgData_812_);
v_a_821_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_818_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_818_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_829_, lean_object* v_severity_830_, lean_object* v_isSilent_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v_severity_boxed_835_; uint8_t v_isSilent_boxed_836_; lean_object* v_res_837_; 
v_severity_boxed_835_ = lean_unbox(v_severity_830_);
v_isSilent_boxed_836_ = lean_unbox(v_isSilent_831_);
v_res_837_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_829_, v_severity_boxed_835_, v_isSilent_boxed_836_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
uint8_t v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = 2;
v___x_843_ = 0;
v___x_844_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_838_, v___x_842_, v___x_843_, v___y_839_, v___y_840_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_850_, lean_object* v_msgData_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = 2;
v___x_856_ = 0;
v___x_857_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_850_, v_msgData_851_, v___x_855_, v___x_856_, v___y_852_, v___y_853_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_858_, lean_object* v_msgData_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_858_, v_msgData_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v_ref_858_);
return v_res_863_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
if (lean_obj_tag(v_ex_867_) == 0)
{
lean_object* v_ref_871_; lean_object* v_msg_872_; lean_object* v___x_873_; 
v_ref_871_ = lean_ctor_get(v_ex_867_, 0);
lean_inc(v_ref_871_);
v_msg_872_ = lean_ctor_get(v_ex_867_, 1);
lean_inc_ref(v_msg_872_);
lean_dec_ref_known(v_ex_867_, 2);
v___x_873_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_871_, v_msg_872_, v___y_868_, v___y_869_);
lean_dec(v_ref_871_);
return v___x_873_;
}
else
{
lean_object* v_id_874_; uint8_t v___y_876_; uint8_t v___x_898_; 
v_id_874_ = lean_ctor_get(v_ex_867_, 0);
lean_inc(v_id_874_);
v___x_898_ = l_Lean_Elab_isAbortExceptionId(v_id_874_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; 
v___x_899_ = l_Lean_Exception_isInterrupt(v_ex_867_);
lean_dec_ref_known(v_ex_867_, 2);
v___y_876_ = v___x_899_;
goto v___jp_875_;
}
else
{
lean_dec_ref_known(v_ex_867_, 2);
v___y_876_ = v___x_898_;
goto v___jp_875_;
}
v___jp_875_:
{
if (v___y_876_ == 0)
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_InternalExceptionId_getName(v_id_874_);
lean_dec(v_id_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_880_ = l_Lean_MessageData_ofName(v_a_878_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_881_, v___y_868_, v___y_869_);
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_895_; 
v_a_883_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_895_ == 0)
{
v___x_885_ = v___x_877_;
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_877_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_ref_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v_ref_887_ = lean_ctor_get(v___y_868_, 7);
v___x_888_ = lean_io_error_to_string(v_a_883_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = l_Lean_MessageData_ofFormat(v___x_889_);
lean_inc(v_ref_887_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_ref_887_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_891_);
v___x_893_ = v___x_885_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_id_874_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_909_ = lean_apply_3(v_x_905_, v___y_906_, v___y_907_, lean_box(0));
if (lean_obj_tag(v___x_909_) == 0)
{
return v___x_909_;
}
else
{
lean_object* v_a_910_; uint8_t v___x_911_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
v___x_911_ = l_Lean_Exception_isInterrupt(v_a_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_dec_ref_known(v___x_909_, 1);
v___x_912_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_910_, v___y_906_, v___y_907_);
return v___x_912_;
}
else
{
lean_dec(v_a_910_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_918_, lean_object* v___x_919_, lean_object* v_val_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_a_924_; lean_object* v___x_926_; 
v___x_926_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_918_, v___x_919_, v_val_920_);
if (lean_obj_tag(v___x_926_) == 0)
{
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v_a_924_ = v_a_927_;
goto v___jp_923_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_926_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v___x_936_; 
lean_dec_ref_known(v___x_926_, 1);
v___x_936_ = lean_box(0);
v_a_924_ = v___x_936_;
goto v___jp_923_;
}
v___jp_923_:
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_a_924_);
return v___x_925_;
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1059_, lean_object* v_cmds_1060_, lean_object* v_cmdState_1061_, lean_object* v_beginPos_1062_, lean_object* v_snap_1063_, lean_object* v_cancelTk_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_env_1067_; lean_object* v_scopes_1068_; lean_object* v_usedQuotCtxts_1069_; lean_object* v_nextMacroScope_1070_; lean_object* v_maxRecDepth_1071_; lean_object* v_ngen_1072_; lean_object* v_auxDeclNGen_1073_; lean_object* v_infoState_1074_; lean_object* v_prevLinterStates_1075_; lean_object* v_codeQualityEntryTasks_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1154_; 
v_env_1067_ = lean_ctor_get(v_cmdState_1061_, 0);
v_scopes_1068_ = lean_ctor_get(v_cmdState_1061_, 2);
v_usedQuotCtxts_1069_ = lean_ctor_get(v_cmdState_1061_, 3);
v_nextMacroScope_1070_ = lean_ctor_get(v_cmdState_1061_, 4);
v_maxRecDepth_1071_ = lean_ctor_get(v_cmdState_1061_, 5);
v_ngen_1072_ = lean_ctor_get(v_cmdState_1061_, 6);
v_auxDeclNGen_1073_ = lean_ctor_get(v_cmdState_1061_, 7);
v_infoState_1074_ = lean_ctor_get(v_cmdState_1061_, 8);
v_prevLinterStates_1075_ = lean_ctor_get(v_cmdState_1061_, 11);
v_codeQualityEntryTasks_1076_ = lean_ctor_get(v_cmdState_1061_, 12);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_cmdState_1061_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; 
v_unused_1155_ = lean_ctor_get(v_cmdState_1061_, 10);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_cmdState_1061_, 9);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_cmdState_1061_, 1);
lean_dec(v_unused_1157_);
v___x_1078_ = v_cmdState_1061_;
v_isShared_1079_ = v_isSharedCheck_1154_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1076_);
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
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1154_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1080_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1081_ = l_List_head_x21___redArg(v___x_1080_, v_scopes_1068_);
v___x_1082_ = l_Lean_MessageLog_empty;
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1085_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 10, v___x_1085_);
lean_ctor_set(v___x_1078_, 9, v___x_1084_);
lean_ctor_set(v___x_1078_, 1, v___x_1082_);
v___x_1087_ = v___x_1078_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_env_1067_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_scopes_1068_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_usedQuotCtxts_1069_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_nextMacroScope_1070_);
lean_ctor_set(v_reuseFailAlloc_1153_, 5, v_maxRecDepth_1071_);
lean_ctor_set(v_reuseFailAlloc_1153_, 6, v_ngen_1072_);
lean_ctor_set(v_reuseFailAlloc_1153_, 7, v_auxDeclNGen_1073_);
lean_ctor_set(v_reuseFailAlloc_1153_, 8, v_infoState_1074_);
lean_ctor_set(v_reuseFailAlloc_1153_, 9, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1153_, 10, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1153_, 11, v_prevLinterStates_1075_);
lean_ctor_set(v_reuseFailAlloc_1153_, 12, v_codeQualityEntryTasks_1076_);
v___x_1087_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v_toProcessingContext_1089_; lean_object* v_fileName_1090_; lean_object* v_fileMap_1091_; lean_object* v_opts_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v_messages_1104_; lean_object* v___y_1132_; 
v___x_1088_ = lean_st_mk_ref(v___x_1087_);
v_toProcessingContext_1089_ = lean_ctor_get(v_a_1065_, 0);
v_fileName_1090_ = lean_ctor_get(v_toProcessingContext_1089_, 1);
v_fileMap_1091_ = lean_ctor_get(v_toProcessingContext_1089_, 2);
v_opts_1092_ = lean_ctor_get(v___x_1081_, 1);
lean_inc_ref(v_opts_1092_);
lean_dec(v___x_1081_);
v___f_1093_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1093_, 0, v_stx_1059_);
lean_closure_set(v___f_1093_, 1, v_cmds_1060_);
v___x_1094_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Lean_firstFrontendMacroScope;
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_internal_cmdlineSnapshots;
v___x_1100_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1092_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1152_; 
lean_inc_ref(v_snap_1063_);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_snap_1063_);
v___y_1132_ = v___x_1152_;
goto v___jp_1131_;
}
else
{
v___y_1132_ = v___x_1096_;
goto v___jp_1131_;
}
v___jp_1101_:
{
lean_object* v_new_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_env_1111_; lean_object* v_scopes_1112_; lean_object* v_usedQuotCtxts_1113_; lean_object* v_nextMacroScope_1114_; lean_object* v_maxRecDepth_1115_; lean_object* v_ngen_1116_; lean_object* v_auxDeclNGen_1117_; lean_object* v_infoState_1118_; lean_object* v_traceState_1119_; lean_object* v_snapshotTasks_1120_; lean_object* v_prevLinterStates_1121_; lean_object* v_codeQualityEntryTasks_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_new_1105_ = lean_ctor_get(v_snap_1063_, 1);
lean_inc(v_new_1105_);
lean_dec_ref(v_snap_1063_);
v___x_1106_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1107_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1108_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_ctor_set(v___x_1108_, 2, v___x_1096_);
lean_ctor_set(v___x_1108_, 3, v___x_1084_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*4, v___y_1102_);
v___x_1109_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1094_, v___x_1108_);
v___x_1110_ = lean_io_promise_resolve(v___x_1109_, v_new_1105_);
lean_dec(v_new_1105_);
v_env_1111_ = lean_ctor_get(v___y_1103_, 0);
v_scopes_1112_ = lean_ctor_get(v___y_1103_, 2);
v_usedQuotCtxts_1113_ = lean_ctor_get(v___y_1103_, 3);
v_nextMacroScope_1114_ = lean_ctor_get(v___y_1103_, 4);
v_maxRecDepth_1115_ = lean_ctor_get(v___y_1103_, 5);
v_ngen_1116_ = lean_ctor_get(v___y_1103_, 6);
v_auxDeclNGen_1117_ = lean_ctor_get(v___y_1103_, 7);
v_infoState_1118_ = lean_ctor_get(v___y_1103_, 8);
v_traceState_1119_ = lean_ctor_get(v___y_1103_, 9);
v_snapshotTasks_1120_ = lean_ctor_get(v___y_1103_, 10);
v_prevLinterStates_1121_ = lean_ctor_get(v___y_1103_, 11);
v_codeQualityEntryTasks_1122_ = lean_ctor_get(v___y_1103_, 12);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___y_1103_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___y_1103_, 1);
lean_dec(v_unused_1130_);
v___x_1124_ = v___y_1103_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1122_);
lean_inc(v_prevLinterStates_1121_);
lean_inc(v_snapshotTasks_1120_);
lean_inc(v_traceState_1119_);
lean_inc(v_infoState_1118_);
lean_inc(v_auxDeclNGen_1117_);
lean_inc(v_ngen_1116_);
lean_inc(v_maxRecDepth_1115_);
lean_inc(v_nextMacroScope_1114_);
lean_inc(v_usedQuotCtxts_1113_);
lean_inc(v_scopes_1112_);
lean_inc(v_env_1111_);
lean_dec(v___y_1103_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v_messages_1104_);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_env_1111_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_messages_1104_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_scopes_1112_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_usedQuotCtxts_1113_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_nextMacroScope_1114_);
lean_ctor_set(v_reuseFailAlloc_1128_, 5, v_maxRecDepth_1115_);
lean_ctor_set(v_reuseFailAlloc_1128_, 6, v_ngen_1116_);
lean_ctor_set(v_reuseFailAlloc_1128_, 7, v_auxDeclNGen_1117_);
lean_ctor_set(v_reuseFailAlloc_1128_, 8, v_infoState_1118_);
lean_ctor_set(v_reuseFailAlloc_1128_, 9, v_traceState_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 10, v_snapshotTasks_1120_);
lean_ctor_set(v_reuseFailAlloc_1128_, 11, v_prevLinterStates_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 12, v_codeQualityEntryTasks_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
v___jp_1131_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v_fst_1140_; lean_object* v___x_1141_; lean_object* v_messages_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_cancelTk_1064_);
v___x_1134_ = 0;
lean_inc(v_beginPos_1062_);
lean_inc_ref(v_fileMap_1091_);
lean_inc_ref(v_fileName_1090_);
v___x_1135_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1135_, 0, v_fileName_1090_);
lean_ctor_set(v___x_1135_, 1, v_fileMap_1091_);
lean_ctor_set(v___x_1135_, 2, v___x_1083_);
lean_ctor_set(v___x_1135_, 3, v_beginPos_1062_);
lean_ctor_set(v___x_1135_, 4, v___x_1095_);
lean_ctor_set(v___x_1135_, 5, v___x_1096_);
lean_ctor_set(v___x_1135_, 6, v___x_1097_);
lean_ctor_set(v___x_1135_, 7, v___x_1098_);
lean_ctor_set(v___x_1135_, 8, v___y_1132_);
lean_ctor_set(v___x_1135_, 9, v___x_1133_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*10, v___x_1134_);
lean_inc(v___x_1088_);
v___f_1136_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1136_, 0, v___f_1093_);
lean_closure_set(v___f_1136_, 1, v___x_1135_);
lean_closure_set(v___f_1136_, 2, v___x_1088_);
v___x_1137_ = l_Lean_Core_stderrAsMessages;
v___x_1138_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1092_, v___x_1137_);
lean_dec_ref(v_opts_1092_);
v___x_1139_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1136_, v___x_1138_, v_a_1065_);
v_fst_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_fst_1140_);
lean_dec_ref(v___x_1139_);
v___x_1141_ = lean_st_ref_get(v___x_1088_);
lean_dec(v___x_1088_);
v_messages_1142_ = lean_ctor_get(v___x_1141_, 1);
lean_inc_ref(v_messages_1142_);
v___x_1143_ = lean_string_utf8_byte_size(v_fst_1140_);
v___x_1144_ = lean_nat_dec_eq(v___x_1143_, v___x_1083_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_inc_ref(v_fileMap_1091_);
v___x_1145_ = l_Lean_FileMap_toPosition(v_fileMap_1091_, v_beginPos_1062_);
lean_dec(v_beginPos_1062_);
v___x_1146_ = 0;
v___x_1147_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_fst_1140_);
v___x_1149_ = l_Lean_MessageData_ofFormat(v___x_1148_);
lean_inc_ref(v_fileName_1090_);
v___x_1150_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1150_, 0, v_fileName_1090_);
lean_ctor_set(v___x_1150_, 1, v___x_1145_);
lean_ctor_set(v___x_1150_, 2, v___x_1096_);
lean_ctor_set(v___x_1150_, 3, v___x_1147_);
lean_ctor_set(v___x_1150_, 4, v___x_1149_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*5, v___x_1134_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*5 + 1, v___x_1146_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*5 + 2, v___x_1134_);
v___x_1151_ = l_Lean_MessageLog_add(v___x_1150_, v_messages_1142_);
v___y_1102_ = v___x_1134_;
v___y_1103_ = v___x_1141_;
v_messages_1104_ = v___x_1151_;
goto v___jp_1101_;
}
else
{
lean_dec(v_fst_1140_);
lean_dec(v_beginPos_1062_);
v___y_1102_ = v___x_1134_;
v___y_1103_ = v___x_1141_;
v_messages_1104_ = v_messages_1142_;
goto v___jp_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1158_, lean_object* v_cmds_1159_, lean_object* v_cmdState_1160_, lean_object* v_beginPos_1161_, lean_object* v_snap_1162_, lean_object* v_cancelTk_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1158_, v_cmds_1159_, v_cmdState_1160_, v_beginPos_1161_, v_snap_1162_, v_cancelTk_1163_, v_a_1164_);
lean_dec_ref(v_a_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1167_, lean_object* v_h_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1168_, v_x_1169_, v___y_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_h_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1173_, v_h_1174_, v_x_1175_, v___y_1176_);
lean_dec_ref(v___y_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1179_, lean_object* v_x_1180_, uint8_t v_isolateStderr_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1180_, v_isolateStderr_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_x_1186_, lean_object* v_isolateStderr_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_isolateStderr_boxed_1190_; lean_object* v_res_1191_; 
v_isolateStderr_boxed_1190_ = lean_unbox(v_isolateStderr_1187_);
v_res_1191_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1185_, v_x_1186_, v_isolateStderr_boxed_1190_, v___y_1188_);
lean_dec_ref(v___y_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1192_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1202_){
_start:
{
lean_object* v_toSnapshotTreeM_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_toSnapshotTreeM_1203_ = lean_ctor_get(v_a_1202_, 1);
lean_inc_ref(v_toSnapshotTreeM_1203_);
lean_dec_ref(v_a_1202_);
v___x_1204_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1205_ = lean_apply_1(v_toSnapshotTreeM_1203_, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1206_){
_start:
{
lean_object* v_toSnapshot_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1217_; 
v_toSnapshot_1207_ = lean_ctor_get(v_a_1206_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_a_1206_, 1);
lean_dec(v_unused_1218_);
v___x_1209_ = v_a_1206_;
v_isShared_1210_ = v_isSharedCheck_1217_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_toSnapshot_1207_);
lean_dec(v_a_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1217_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1211_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1212_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1207_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1213_);
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1215_ = v___x_1209_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1221_ = l_Lean_Language_Snapshot_transform(v_a_1219_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1224_, lean_object* v_opt_1225_){
_start:
{
lean_object* v_name_1226_; lean_object* v_defValue_1227_; lean_object* v_map_1228_; lean_object* v___x_1229_; 
v_name_1226_ = lean_ctor_get(v_opt_1225_, 0);
v_defValue_1227_ = lean_ctor_get(v_opt_1225_, 1);
v_map_1228_ = lean_ctor_get(v_opts_1224_, 0);
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1228_, v_name_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_inc(v_defValue_1227_);
return v_defValue_1227_;
}
else
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
if (lean_obj_tag(v_val_1230_) == 3)
{
lean_object* v_v_1231_; 
v_v_1231_ = lean_ctor_get(v_val_1230_, 0);
lean_inc(v_v_1231_);
lean_dec_ref_known(v_val_1230_, 1);
return v_v_1231_;
}
else
{
lean_dec(v_val_1230_);
lean_inc(v_defValue_1227_);
return v_defValue_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1232_, lean_object* v_opt_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1232_, v_opt_1233_);
lean_dec_ref(v_opt_1233_);
lean_dec_ref(v_opts_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1237_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1235_, v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1244_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1245_ = l_Lean_Name_append(v___x_1244_, v___x_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1246_, lean_object* v___x_1247_, uint8_t v_val_1248_, lean_object* v_val_1249_, lean_object* v_val_1250_, lean_object* v___x_1251_, lean_object* v___x_1252_, uint8_t v___x_1253_, lean_object* v_a_1254_, lean_object* v_pos_1255_, lean_object* v___x_1256_, lean_object* v_infoSt_1257_){
_start:
{
lean_object* v___y_1260_; lean_object* v_msgLog_1261_; lean_object* v___y_1267_; lean_object* v_trees_1299_; lean_object* v_size_1300_; uint8_t v___x_1301_; 
v_trees_1299_ = lean_ctor_get(v_infoSt_1257_, 2);
v_size_1300_ = lean_ctor_get(v_trees_1299_, 2);
v___x_1301_ = lean_nat_dec_lt(v___x_1252_, v_size_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = l_outOfBounds___redArg(v___x_1256_);
v___y_1267_ = v___x_1302_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1256_, v_trees_1299_, v___x_1252_);
v___y_1267_ = v___x_1303_;
goto v___jp_1266_;
}
v___jp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1261_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1260_);
v___x_1264_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1246_);
lean_ctor_set(v___x_1264_, 1, v___x_1262_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
lean_ctor_set(v___x_1264_, 3, v___x_1247_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*4, v_val_1248_);
v___x_1265_ = lean_io_promise_resolve(v___x_1264_, v_val_1249_);
return v___x_1265_;
}
v___jp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_scopes_1270_; lean_object* v___x_1271_; lean_object* v_opts_1272_; uint8_t v_hasTrace_1273_; lean_object* v___x_1274_; 
v___x_1268_ = l_Lean_inheritedTraceOptions;
v___x_1269_ = lean_st_ref_get(v___x_1268_);
v_scopes_1270_ = lean_ctor_get(v_val_1250_, 2);
v___x_1271_ = l_List_head_x21___redArg(v___x_1251_, v_scopes_1270_);
v_opts_1272_ = lean_ctor_get(v___x_1271_, 1);
lean_inc_ref(v_opts_1272_);
lean_dec(v___x_1271_);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_opts_1272_, sizeof(void*)*1);
v___x_1274_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1273_ == 0)
{
lean_dec_ref(v_opts_1272_);
lean_dec(v___x_1269_);
lean_dec(v___x_1252_);
v___y_1260_ = v___y_1267_;
v_msgLog_1261_ = v___x_1274_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1276_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1277_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1269_, v_opts_1272_, v___x_1277_);
lean_dec_ref(v_opts_1272_);
lean_dec(v___x_1269_);
if (v___x_1278_ == 0)
{
lean_dec(v___x_1252_);
v___y_1260_ = v___y_1267_;
v_msgLog_1261_ = v___x_1274_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(0);
lean_inc_ref(v___y_1267_);
v___x_1280_ = l_Lean_Elab_InfoTree_format(v___y_1267_, v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; double v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_toProcessingContext_1285_; lean_object* v_fileName_1286_; lean_object* v_fileMap_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_float_of_nat(v___x_1252_);
v___x_1283_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1284_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1284_, 0, v___x_1275_);
lean_ctor_set(v___x_1284_, 1, v___x_1279_);
lean_ctor_set(v___x_1284_, 2, v___x_1283_);
lean_ctor_set_float(v___x_1284_, sizeof(void*)*3, v___x_1282_);
lean_ctor_set_float(v___x_1284_, sizeof(void*)*3 + 8, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*3 + 16, v___x_1253_);
v_toProcessingContext_1285_ = lean_ctor_get(v_a_1254_, 0);
v_fileName_1286_ = lean_ctor_get(v_toProcessingContext_1285_, 1);
v_fileMap_1287_ = lean_ctor_get(v_toProcessingContext_1285_, 2);
v___x_1288_ = l_Lean_MessageData_nil;
v___x_1289_ = l_Lean_MessageData_ofFormat(v_a_1281_);
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_mk_empty_array_with_capacity(v___x_1290_);
v___x_1292_ = lean_array_push(v___x_1291_, v___x_1289_);
v___x_1293_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1284_);
lean_ctor_set(v___x_1293_, 1, v___x_1288_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1276_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
lean_inc_ref(v_fileMap_1287_);
v___x_1295_ = l_Lean_FileMap_toPosition(v_fileMap_1287_, v_pos_1255_);
v___x_1296_ = 0;
lean_inc_ref(v_fileName_1286_);
v___x_1297_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1297_, 0, v_fileName_1286_);
lean_ctor_set(v___x_1297_, 1, v___x_1295_);
lean_ctor_set(v___x_1297_, 2, v___x_1279_);
lean_ctor_set(v___x_1297_, 3, v___x_1283_);
lean_ctor_set(v___x_1297_, 4, v___x_1294_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*5, v_val_1248_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*5 + 1, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*5 + 2, v_val_1248_);
v___x_1298_ = l_Lean_MessageLog_add(v___x_1297_, v___x_1274_);
v___y_1260_ = v___y_1267_;
v_msgLog_1261_ = v___x_1298_;
goto v___jp_1259_;
}
else
{
lean_dec_ref_known(v___x_1280_, 1);
lean_dec(v___x_1252_);
v___y_1260_ = v___y_1267_;
v_msgLog_1261_ = v___x_1274_;
goto v___jp_1259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v_val_1306_, lean_object* v_val_1307_, lean_object* v_val_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v_a_1312_, lean_object* v_pos_1313_, lean_object* v___x_1314_, lean_object* v_infoSt_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v_val_35107__boxed_1317_; uint8_t v___x_35112__boxed_1318_; lean_object* v_res_1319_; 
v_val_35107__boxed_1317_ = lean_unbox(v_val_1306_);
v___x_35112__boxed_1318_ = lean_unbox(v___x_1311_);
v_res_1319_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1304_, v___x_1305_, v_val_35107__boxed_1317_, v_val_1307_, v_val_1308_, v___x_1309_, v___x_1310_, v___x_35112__boxed_1318_, v_a_1312_, v_pos_1313_, v___x_1314_, v_infoSt_1315_);
lean_dec_ref(v_infoSt_1315_);
lean_dec_ref(v___x_1314_);
lean_dec(v_pos_1313_);
lean_dec_ref(v_a_1312_);
lean_dec_ref(v___x_1309_);
lean_dec_ref(v_val_1308_);
lean_dec(v_val_1307_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, uint8_t v_val_1323_, lean_object* v_as_1324_, size_t v_sz_1325_, size_t v_i_1326_, lean_object* v_b_1327_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_usize_dec_lt(v_i_1326_, v_sz_1325_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1320_);
return v_b_1327_;
}
else
{
lean_object* v_snd_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1348_; 
v_snd_1330_ = lean_ctor_get(v_b_1327_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_b_1327_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v_b_1327_, 0);
lean_dec(v_unused_1349_);
v___x_1332_ = v_b_1327_;
v_isShared_1333_ = v_isSharedCheck_1348_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_snd_1330_);
lean_dec(v_b_1327_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1348_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_a_1334_; lean_object* v_msg_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_a_1334_ = lean_array_uget_borrowed(v_as_1324_, v_i_1326_);
v_msg_1335_ = lean_ctor_get(v_a_1334_, 1);
v___x_1336_ = lean_box(0);
lean_inc_ref(v___x_1320_);
v___x_1337_ = l_Lean_FileMap_toPosition(v___x_1320_, v___x_1321_);
v___x_1338_ = 0;
v___x_1339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1335_);
lean_inc_ref(v___x_1322_);
v___x_1340_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1340_, 0, v___x_1322_);
lean_ctor_set(v___x_1340_, 1, v___x_1337_);
lean_ctor_set(v___x_1340_, 2, v___x_1336_);
lean_ctor_set(v___x_1340_, 3, v___x_1339_);
lean_ctor_set(v___x_1340_, 4, v_msg_1335_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5, v_val_1323_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5 + 1, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*5 + 2, v_val_1323_);
v___x_1341_ = l_Lean_MessageLog_add(v___x_1340_, v_snd_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___x_1341_);
lean_ctor_set(v___x_1332_, 0, v___x_1336_);
v___x_1343_ = v___x_1332_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
size_t v___x_1344_; size_t v___x_1345_; 
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1326_, v___x_1344_);
v_i_1326_ = v___x_1345_;
v_b_1327_ = v___x_1343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1350_, lean_object* v___x_1351_, lean_object* v___x_1352_, lean_object* v_val_1353_, lean_object* v_as_1354_, lean_object* v_sz_1355_, lean_object* v_i_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_){
_start:
{
uint8_t v_val_35220__boxed_1359_; size_t v_sz_boxed_1360_; size_t v_i_boxed_1361_; lean_object* v_res_1362_; 
v_val_35220__boxed_1359_ = lean_unbox(v_val_1353_);
v_sz_boxed_1360_ = lean_unbox_usize(v_sz_1355_);
lean_dec(v_sz_1355_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1356_);
lean_dec(v_i_1356_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1350_, v___x_1351_, v___x_1352_, v_val_35220__boxed_1359_, v_as_1354_, v_sz_boxed_1360_, v_i_boxed_1361_, v_b_1357_);
lean_dec_ref(v_as_1354_);
lean_dec(v___x_1351_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v___x_1365_, uint8_t v_val_1366_, lean_object* v_as_1367_, size_t v_sz_1368_, size_t v_i_1369_, lean_object* v_b_1370_){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_usize_dec_lt(v_i_1369_, v_sz_1368_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v___x_1365_);
lean_dec_ref(v___x_1363_);
return v_b_1370_;
}
else
{
lean_object* v_snd_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1391_; 
v_snd_1373_ = lean_ctor_get(v_b_1370_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_b_1370_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v_b_1370_, 0);
lean_dec(v_unused_1392_);
v___x_1375_ = v_b_1370_;
v_isShared_1376_ = v_isSharedCheck_1391_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_snd_1373_);
lean_dec(v_b_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1391_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_a_1377_; lean_object* v_msg_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v_a_1377_ = lean_array_uget_borrowed(v_as_1367_, v_i_1369_);
v_msg_1378_ = lean_ctor_get(v_a_1377_, 1);
v___x_1379_ = lean_box(0);
lean_inc_ref(v___x_1363_);
v___x_1380_ = l_Lean_FileMap_toPosition(v___x_1363_, v___x_1364_);
v___x_1381_ = 0;
v___x_1382_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1378_);
lean_inc_ref(v___x_1365_);
v___x_1383_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1383_, 0, v___x_1365_);
lean_ctor_set(v___x_1383_, 1, v___x_1380_);
lean_ctor_set(v___x_1383_, 2, v___x_1379_);
lean_ctor_set(v___x_1383_, 3, v___x_1382_);
lean_ctor_set(v___x_1383_, 4, v_msg_1378_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*5, v_val_1366_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*5 + 1, v___x_1381_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*5 + 2, v_val_1366_);
v___x_1384_ = l_Lean_MessageLog_add(v___x_1383_, v_snd_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1384_);
lean_ctor_set(v___x_1375_, 0, v___x_1379_);
v___x_1386_ = v___x_1375_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_add(v_i_1369_, v___x_1387_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1363_, v___x_1364_, v___x_1365_, v_val_1366_, v_as_1367_, v_sz_1368_, v___x_1388_, v___x_1386_);
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v_val_1396_, lean_object* v_as_1397_, lean_object* v_sz_1398_, lean_object* v_i_1399_, lean_object* v_b_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v_val_35272__boxed_1402_; size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_val_35272__boxed_1402_ = lean_unbox(v_val_1396_);
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1398_);
lean_dec(v_sz_1398_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1399_);
lean_dec(v_i_1399_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1393_, v___x_1394_, v___x_1395_, v_val_35272__boxed_1402_, v_as_1397_, v_sz_boxed_1403_, v_i_boxed_1404_, v_b_1400_);
lean_dec_ref(v_as_1397_);
lean_dec(v___x_1394_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1406_, lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, uint8_t v_val_1410_, lean_object* v_n_1411_, lean_object* v_b_1412_){
_start:
{
if (lean_obj_tag(v_n_1411_) == 0)
{
lean_object* v_cs_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; size_t v___x_1418_; lean_object* v___x_1419_; lean_object* v_fst_1420_; 
v_cs_1414_ = lean_ctor_get(v_n_1411_, 0);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_b_1412_);
v_sz_1417_ = lean_array_size(v_cs_1414_);
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1406_, v___x_1407_, v___x_1408_, v___x_1409_, v_val_1410_, v_cs_1414_, v_sz_1417_, v___x_1418_, v___x_1416_);
v_fst_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_fst_1420_);
if (lean_obj_tag(v_fst_1420_) == 0)
{
lean_object* v_snd_1421_; lean_object* v___x_1422_; 
v_snd_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_snd_1421_);
lean_dec_ref(v___x_1419_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_snd_1421_);
return v___x_1422_;
}
else
{
lean_object* v_val_1423_; 
lean_dec_ref(v___x_1419_);
v_val_1423_ = lean_ctor_get(v_fst_1420_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_fst_1420_, 1);
return v_val_1423_;
}
}
else
{
lean_object* v_vs_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; size_t v_sz_1427_; size_t v___x_1428_; lean_object* v___x_1429_; lean_object* v_fst_1430_; 
v_vs_1424_ = lean_ctor_get(v_n_1411_, 0);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_b_1412_);
v_sz_1427_ = lean_array_size(v_vs_1424_);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1407_, v___x_1408_, v___x_1409_, v_val_1410_, v_vs_1424_, v_sz_1427_, v___x_1428_, v___x_1426_);
v_fst_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_fst_1430_);
if (lean_obj_tag(v_fst_1430_) == 0)
{
lean_object* v_snd_1431_; lean_object* v___x_1432_; 
v_snd_1431_ = lean_ctor_get(v___x_1429_, 1);
lean_inc(v_snd_1431_);
lean_dec_ref(v___x_1429_);
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_snd_1431_);
return v___x_1432_;
}
else
{
lean_object* v_val_1433_; 
lean_dec_ref(v___x_1429_);
v_val_1433_ = lean_ctor_get(v_fst_1430_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v_fst_1430_, 1);
return v_val_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1434_, lean_object* v___x_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, uint8_t v_val_1438_, lean_object* v_as_1439_, size_t v_sz_1440_, size_t v_i_1441_, lean_object* v_b_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_lt(v_i_1441_, v_sz_1440_);
if (v___x_1444_ == 0)
{
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1435_);
return v_b_1442_;
}
else
{
lean_object* v_snd_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1463_; 
v_snd_1445_ = lean_ctor_get(v_b_1442_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_b_1442_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_b_1442_, 0);
lean_dec(v_unused_1464_);
v___x_1447_ = v_b_1442_;
v_isShared_1448_ = v_isSharedCheck_1463_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_snd_1445_);
lean_dec(v_b_1442_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1463_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_array_uget_borrowed(v_as_1439_, v_i_1441_);
lean_inc(v_snd_1445_);
lean_inc_ref(v___x_1437_);
lean_inc_ref(v___x_1435_);
v___x_1450_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1434_, v___x_1435_, v___x_1436_, v___x_1437_, v_val_1438_, v_a_1449_, v_snd_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1435_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1451_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_snd_1445_);
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
lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_snd_1445_);
v_a_1455_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1456_ = lean_box(0);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v_a_1455_);
lean_ctor_set(v___x_1447_, 0, v___x_1456_);
v___x_1458_ = v___x_1447_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_a_1455_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
size_t v___x_1459_; size_t v___x_1460_; 
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_add(v_i_1441_, v___x_1459_);
v_i_1441_ = v___x_1460_;
v_b_1442_ = v___x_1458_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1465_, lean_object* v___x_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v_val_1469_, lean_object* v_as_1470_, lean_object* v_sz_1471_, lean_object* v_i_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v_val_35323__boxed_1475_; size_t v_sz_boxed_1476_; size_t v_i_boxed_1477_; lean_object* v_res_1478_; 
v_val_35323__boxed_1475_ = lean_unbox(v_val_1469_);
v_sz_boxed_1476_ = lean_unbox_usize(v_sz_1471_);
lean_dec(v_sz_1471_);
v_i_boxed_1477_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1465_, v___x_1466_, v___x_1467_, v___x_1468_, v_val_35323__boxed_1475_, v_as_1470_, v_sz_boxed_1476_, v_i_boxed_1477_, v_b_1473_);
lean_dec_ref(v_as_1470_);
lean_dec(v___x_1467_);
lean_dec_ref(v_init_1465_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v_val_1483_, lean_object* v_n_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v_val_35339__boxed_1487_; lean_object* v_res_1488_; 
v_val_35339__boxed_1487_ = lean_unbox(v_val_1483_);
v_res_1488_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1479_, v___x_1480_, v___x_1481_, v___x_1482_, v_val_35339__boxed_1487_, v_n_1484_, v_b_1485_);
lean_dec_ref(v_n_1484_);
lean_dec(v___x_1481_);
lean_dec_ref(v_init_1479_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1489_, lean_object* v___x_1490_, lean_object* v___x_1491_, uint8_t v_val_1492_, lean_object* v_as_1493_, size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_b_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1498_ == 0)
{
lean_dec_ref(v___x_1491_);
lean_dec_ref(v___x_1489_);
return v_b_1496_;
}
else
{
lean_object* v_snd_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1517_; 
v_snd_1499_ = lean_ctor_get(v_b_1496_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_b_1496_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_b_1496_, 0);
lean_dec(v_unused_1518_);
v___x_1501_ = v_b_1496_;
v_isShared_1502_ = v_isSharedCheck_1517_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_snd_1499_);
lean_dec(v_b_1496_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1517_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v_a_1503_; lean_object* v_msg_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_a_1503_ = lean_array_uget_borrowed(v_as_1493_, v_i_1495_);
v_msg_1504_ = lean_ctor_get(v_a_1503_, 1);
v___x_1505_ = lean_box(0);
lean_inc_ref(v___x_1489_);
v___x_1506_ = l_Lean_FileMap_toPosition(v___x_1489_, v___x_1490_);
v___x_1507_ = 0;
v___x_1508_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1504_);
lean_inc_ref(v___x_1491_);
v___x_1509_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1509_, 0, v___x_1491_);
lean_ctor_set(v___x_1509_, 1, v___x_1506_);
lean_ctor_set(v___x_1509_, 2, v___x_1505_);
lean_ctor_set(v___x_1509_, 3, v___x_1508_);
lean_ctor_set(v___x_1509_, 4, v_msg_1504_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*5, v_val_1492_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*5 + 1, v___x_1507_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*5 + 2, v_val_1492_);
v___x_1510_ = l_Lean_MessageLog_add(v___x_1509_, v_snd_1499_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1510_);
lean_ctor_set(v___x_1501_, 0, v___x_1505_);
v___x_1512_ = v___x_1501_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
size_t v___x_1513_; size_t v___x_1514_; 
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1495_, v___x_1513_);
v_i_1495_ = v___x_1514_;
v_b_1496_ = v___x_1512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v___x_1521_, lean_object* v_val_1522_, lean_object* v_as_1523_, lean_object* v_sz_1524_, lean_object* v_i_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_){
_start:
{
uint8_t v_val_35421__boxed_1528_; size_t v_sz_boxed_1529_; size_t v_i_boxed_1530_; lean_object* v_res_1531_; 
v_val_35421__boxed_1528_ = lean_unbox(v_val_1522_);
v_sz_boxed_1529_ = lean_unbox_usize(v_sz_1524_);
lean_dec(v_sz_1524_);
v_i_boxed_1530_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_res_1531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1519_, v___x_1520_, v___x_1521_, v_val_35421__boxed_1528_, v_as_1523_, v_sz_boxed_1529_, v_i_boxed_1530_, v_b_1526_);
lean_dec_ref(v_as_1523_);
lean_dec(v___x_1520_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, uint8_t v_val_1535_, lean_object* v_as_1536_, size_t v_sz_1537_, size_t v_i_1538_, lean_object* v_b_1539_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_usize_dec_lt(v_i_1538_, v_sz_1537_);
if (v___x_1541_ == 0)
{
lean_dec_ref(v___x_1534_);
lean_dec_ref(v___x_1532_);
return v_b_1539_;
}
else
{
lean_object* v_snd_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1560_; 
v_snd_1542_ = lean_ctor_get(v_b_1539_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_b_1539_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_b_1539_, 0);
lean_dec(v_unused_1561_);
v___x_1544_ = v_b_1539_;
v_isShared_1545_ = v_isSharedCheck_1560_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_snd_1542_);
lean_dec(v_b_1539_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1560_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_a_1546_; lean_object* v_msg_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v_a_1546_ = lean_array_uget_borrowed(v_as_1536_, v_i_1538_);
v_msg_1547_ = lean_ctor_get(v_a_1546_, 1);
v___x_1548_ = lean_box(0);
lean_inc_ref(v___x_1532_);
v___x_1549_ = l_Lean_FileMap_toPosition(v___x_1532_, v___x_1533_);
v___x_1550_ = 0;
v___x_1551_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1547_);
lean_inc_ref(v___x_1534_);
v___x_1552_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1552_, 0, v___x_1534_);
lean_ctor_set(v___x_1552_, 1, v___x_1549_);
lean_ctor_set(v___x_1552_, 2, v___x_1548_);
lean_ctor_set(v___x_1552_, 3, v___x_1551_);
lean_ctor_set(v___x_1552_, 4, v_msg_1547_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*5, v_val_1535_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*5 + 1, v___x_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*5 + 2, v_val_1535_);
v___x_1553_ = l_Lean_MessageLog_add(v___x_1552_, v_snd_1542_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___x_1553_);
lean_ctor_set(v___x_1544_, 0, v___x_1548_);
v___x_1555_ = v___x_1544_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_add(v_i_1538_, v___x_1556_);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1532_, v___x_1533_, v___x_1534_, v_val_1535_, v_as_1536_, v_sz_1537_, v___x_1557_, v___x_1555_);
return v___x_1558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v___x_1564_, lean_object* v_val_1565_, lean_object* v_as_1566_, lean_object* v_sz_1567_, lean_object* v_i_1568_, lean_object* v_b_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v_val_35473__boxed_1571_; size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v_val_35473__boxed_1571_ = lean_unbox(v_val_1565_);
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1567_);
lean_dec(v_sz_1567_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1568_);
lean_dec(v_i_1568_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1562_, v___x_1563_, v___x_1564_, v_val_35473__boxed_1571_, v_as_1566_, v_sz_boxed_1572_, v_i_boxed_1573_, v_b_1569_);
lean_dec_ref(v_as_1566_);
lean_dec(v___x_1563_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, uint8_t v_val_1578_, lean_object* v_t_1579_, lean_object* v_init_1580_){
_start:
{
lean_object* v_root_1582_; lean_object* v_tail_1583_; lean_object* v___x_1584_; 
v_root_1582_ = lean_ctor_get(v_t_1579_, 0);
v_tail_1583_ = lean_ctor_get(v_t_1579_, 1);
lean_inc_ref(v___x_1577_);
lean_inc_ref(v___x_1575_);
lean_inc_ref(v_init_1580_);
v___x_1584_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1580_, v___x_1575_, v___x_1576_, v___x_1577_, v_val_1578_, v_root_1582_, v_init_1580_);
lean_dec_ref(v_init_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; 
lean_dec_ref(v___x_1577_);
lean_dec_ref(v___x_1575_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
return v_a_1585_;
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; size_t v_sz_1589_; size_t v___x_1590_; lean_object* v___x_1591_; lean_object* v_fst_1592_; 
v_a_1586_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v_a_1586_);
v_sz_1589_ = lean_array_size(v_tail_1583_);
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1575_, v___x_1576_, v___x_1577_, v_val_1578_, v_tail_1583_, v_sz_1589_, v___x_1590_, v___x_1588_);
v_fst_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_fst_1592_);
if (lean_obj_tag(v_fst_1592_) == 0)
{
lean_object* v_snd_1593_; 
v_snd_1593_ = lean_ctor_get(v___x_1591_, 1);
lean_inc(v_snd_1593_);
lean_dec_ref(v___x_1591_);
return v_snd_1593_;
}
else
{
lean_object* v_val_1594_; 
lean_dec_ref(v___x_1591_);
v_val_1594_ = lean_ctor_get(v_fst_1592_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_fst_1592_, 1);
return v_val_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v_val_1598_, lean_object* v_t_1599_, lean_object* v_init_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_val_35524__boxed_1602_; lean_object* v_res_1603_; 
v_val_35524__boxed_1602_ = lean_unbox(v_val_1598_);
v_res_1603_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1595_, v___x_1596_, v___x_1597_, v_val_35524__boxed_1602_, v_t_1599_, v_init_1600_);
lean_dec_ref(v_t_1599_);
lean_dec(v___x_1596_);
return v_res_1603_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = l_Lean_firstFrontendMacroScope;
v___x_1606_ = lean_nat_add(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1613_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v___x_1620_, size_t v___x_1621_, uint8_t v___x_1622_, lean_object* v_env_1623_, lean_object* v___x_1624_, lean_object* v___x_1625_, lean_object* v_a_1626_, lean_object* v_opts_1627_, lean_object* v___x_1628_, lean_object* v_pos_1629_, uint8_t v_val_1630_, lean_object* v___x_1631_, lean_object* v___x_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, uint8_t v___x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_toProcessingContext_1657_; lean_object* v_fileName_1658_; lean_object* v_fileMap_1659_; lean_object* v_env_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v_fileName_1666_; lean_object* v_fileMap_1667_; lean_object* v_currRecDepth_1668_; lean_object* v_ref_1669_; lean_object* v_currNamespace_1670_; lean_object* v_openDecls_1671_; lean_object* v_initHeartbeats_1672_; lean_object* v_maxHeartbeats_1673_; lean_object* v_quotContext_1674_; lean_object* v_currMacroScope_1675_; lean_object* v_cancelTk_x3f_1676_; uint8_t v_suppressElabErrors_1677_; lean_object* v_inheritedTraceOptions_1678_; lean_object* v___y_1679_; uint8_t v___y_1696_; uint8_t v___x_1716_; 
v___x_1638_ = l_Lean_firstFrontendMacroScope;
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1641_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_1642_ = lean_box(0);
lean_inc(v___x_1618_);
v___x_1643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1618_);
lean_ctor_set(v___x_1643_, 1, v___x_1639_);
lean_ctor_set(v___x_1643_, 2, v___x_1642_);
v___x_1644_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1645_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1619_);
lean_inc_ref(v___x_1646_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_inc_n(v___x_1620_, 2);
v___x_1648_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
lean_ctor_set(v___x_1648_, 2, v___x_1620_);
lean_ctor_set(v___x_1648_, 3, v___x_1620_);
lean_ctor_set_usize(v___x_1648_, 4, v___x_1621_);
v___x_1649_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1648_, 2);
v___x_1650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1648_);
lean_ctor_set(v___x_1650_, 2, v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1651_, 0, v___x_1644_);
lean_ctor_set(v___x_1651_, 1, v___x_1644_);
lean_ctor_set(v___x_1651_, 2, v___x_1648_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*3, v___x_1622_);
v___x_1652_ = lean_mk_empty_array_with_capacity(v___x_1620_);
lean_inc_ref(v___x_1652_);
lean_inc_ref(v___x_1624_);
v___x_1653_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1653_, 0, v_env_1623_);
lean_ctor_set(v___x_1653_, 1, v___x_1640_);
lean_ctor_set(v___x_1653_, 2, v___x_1641_);
lean_ctor_set(v___x_1653_, 3, v___x_1643_);
lean_ctor_set(v___x_1653_, 4, v___x_1624_);
lean_ctor_set(v___x_1653_, 5, v___x_1645_);
lean_ctor_set(v___x_1653_, 6, v___x_1650_);
lean_ctor_set(v___x_1653_, 7, v___x_1651_);
lean_ctor_set(v___x_1653_, 8, v___x_1652_);
v___x_1654_ = lean_st_mk_ref(v___x_1653_);
v___x_1655_ = lean_st_ref_get(v___x_1625_);
v___x_1656_ = lean_st_ref_get(v___x_1654_);
v_toProcessingContext_1657_ = lean_ctor_get(v_a_1626_, 0);
v_fileName_1658_ = lean_ctor_get(v_toProcessingContext_1657_, 1);
v_fileMap_1659_ = lean_ctor_get(v_toProcessingContext_1657_, 2);
v_env_1660_ = lean_ctor_get(v___x_1656_, 0);
lean_inc_ref(v_env_1660_);
lean_dec(v___x_1656_);
v___x_1661_ = lean_box(0);
v___x_1662_ = l_Lean_Core_getMaxHeartbeats(v_opts_1627_);
v___x_1663_ = l_Lean_diagnostics;
v___x_1664_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1627_, v___x_1663_);
v___x_1716_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1660_);
lean_dec_ref(v_env_1660_);
if (v___x_1664_ == 0)
{
if (v___x_1716_ == 0)
{
v___y_1696_ = v___x_1635_;
goto v___jp_1695_;
}
else
{
v___y_1696_ = v___x_1664_;
goto v___jp_1695_;
}
}
else
{
v___y_1696_ = v___x_1716_;
goto v___jp_1695_;
}
v___jp_1665_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = l_Lean_maxRecDepth;
v___x_1681_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1627_, v___x_1680_);
lean_inc(v_currMacroScope_1675_);
lean_inc(v_openDecls_1671_);
lean_inc(v_ref_1669_);
v___x_1682_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1682_, 0, v_fileName_1666_);
lean_ctor_set(v___x_1682_, 1, v_fileMap_1667_);
lean_ctor_set(v___x_1682_, 2, v_opts_1627_);
lean_ctor_set(v___x_1682_, 3, v_currRecDepth_1668_);
lean_ctor_set(v___x_1682_, 4, v___x_1681_);
lean_ctor_set(v___x_1682_, 5, v_ref_1669_);
lean_ctor_set(v___x_1682_, 6, v_currNamespace_1670_);
lean_ctor_set(v___x_1682_, 7, v_openDecls_1671_);
lean_ctor_set(v___x_1682_, 8, v_initHeartbeats_1672_);
lean_ctor_set(v___x_1682_, 9, v_maxHeartbeats_1673_);
lean_ctor_set(v___x_1682_, 10, v_quotContext_1674_);
lean_ctor_set(v___x_1682_, 11, v_currMacroScope_1675_);
lean_ctor_set(v___x_1682_, 12, v_cancelTk_x3f_1676_);
lean_ctor_set(v___x_1682_, 13, v_inheritedTraceOptions_1678_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*14, v___x_1664_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*14 + 1, v_suppressElabErrors_1677_);
v___x_1683_ = l_Lean_Language_SnapshotTree_trace(v___x_1628_, v___x_1682_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref_known(v___x_1682_, 14);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; lean_object* v_traceState_1685_; lean_object* v_traces_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec_ref_known(v___x_1683_, 1);
lean_dec_ref(v___x_1633_);
v___x_1684_ = lean_st_ref_get(v___x_1654_);
lean_dec(v___x_1654_);
v_traceState_1685_ = lean_ctor_get(v___x_1684_, 4);
lean_inc_ref(v_traceState_1685_);
lean_dec(v___x_1684_);
v_traces_1686_ = lean_ctor_get(v_traceState_1685_, 0);
lean_inc_ref(v_traces_1686_);
lean_dec_ref(v_traceState_1685_);
v___x_1687_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1658_);
lean_inc_ref(v_fileMap_1659_);
v___x_1688_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1659_, v_pos_1629_, v_fileName_1658_, v_val_1630_, v_traces_1686_, v___x_1687_);
lean_dec_ref(v_traces_1686_);
v___x_1689_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1688_);
v___x_1690_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1690_, 0, v___x_1631_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set(v___x_1690_, 2, v___x_1632_);
lean_ctor_set(v___x_1690_, 3, v___x_1624_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*4, v_val_1630_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v___x_1652_);
v___x_1692_ = lean_task_pure(v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec_ref_known(v___x_1683_, 1);
lean_dec(v___x_1654_);
lean_dec(v___x_1632_);
lean_dec_ref(v___x_1631_);
lean_dec_ref(v___x_1624_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1633_);
lean_ctor_set(v___x_1693_, 1, v___x_1652_);
v___x_1694_ = lean_task_pure(v___x_1693_);
return v___x_1694_;
}
}
v___jp_1695_:
{
if (v___y_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v_nextMacroScope_1699_; lean_object* v_ngen_1700_; lean_object* v_auxDeclNGen_1701_; lean_object* v_traceState_1702_; lean_object* v_messages_1703_; lean_object* v_infoState_1704_; lean_object* v_snapshotTasks_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1714_; 
v___x_1697_ = lean_st_ref_take(v___x_1654_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
v_nextMacroScope_1699_ = lean_ctor_get(v___x_1697_, 1);
v_ngen_1700_ = lean_ctor_get(v___x_1697_, 2);
v_auxDeclNGen_1701_ = lean_ctor_get(v___x_1697_, 3);
v_traceState_1702_ = lean_ctor_get(v___x_1697_, 4);
v_messages_1703_ = lean_ctor_get(v___x_1697_, 6);
v_infoState_1704_ = lean_ctor_get(v___x_1697_, 7);
v_snapshotTasks_1705_ = lean_ctor_get(v___x_1697_, 8);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v___x_1697_, 5);
lean_dec(v_unused_1715_);
v___x_1707_ = v___x_1697_;
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snapshotTasks_1705_);
lean_inc(v_infoState_1704_);
lean_inc(v_messages_1703_);
lean_inc(v_traceState_1702_);
lean_inc(v_auxDeclNGen_1701_);
lean_inc(v_ngen_1700_);
lean_inc(v_nextMacroScope_1699_);
lean_inc(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = l_Lean_Kernel_enableDiag(v_env_1698_, v___x_1664_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 5, v___x_1645_);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_nextMacroScope_1699_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_ngen_1700_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_auxDeclNGen_1701_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_traceState_1702_);
lean_ctor_set(v_reuseFailAlloc_1713_, 5, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1713_, 6, v_messages_1703_);
lean_ctor_set(v_reuseFailAlloc_1713_, 7, v_infoState_1704_);
lean_ctor_set(v_reuseFailAlloc_1713_, 8, v_snapshotTasks_1705_);
v___x_1711_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_st_ref_put(v___x_1654_, v___x_1711_);
lean_inc(v___x_1654_);
lean_inc(v___x_1618_);
lean_inc(v___x_1620_);
lean_inc_ref(v_fileMap_1659_);
lean_inc_ref(v_fileName_1658_);
v_fileName_1666_ = v_fileName_1658_;
v_fileMap_1667_ = v_fileMap_1659_;
v_currRecDepth_1668_ = v___x_1620_;
v_ref_1669_ = v___x_1661_;
v_currNamespace_1670_ = v___x_1618_;
v_openDecls_1671_ = v___x_1642_;
v_initHeartbeats_1672_ = v___x_1620_;
v_maxHeartbeats_1673_ = v___x_1662_;
v_quotContext_1674_ = v___x_1618_;
v_currMacroScope_1675_ = v___x_1638_;
v_cancelTk_x3f_1676_ = v___x_1634_;
v_suppressElabErrors_1677_ = v_val_1630_;
v_inheritedTraceOptions_1678_ = v___x_1655_;
v___y_1679_ = v___x_1654_;
goto v___jp_1665_;
}
}
}
else
{
lean_inc(v___x_1654_);
lean_inc(v___x_1618_);
lean_inc(v___x_1620_);
lean_inc_ref(v_fileMap_1659_);
lean_inc_ref(v_fileName_1658_);
v_fileName_1666_ = v_fileName_1658_;
v_fileMap_1667_ = v_fileMap_1659_;
v_currRecDepth_1668_ = v___x_1620_;
v_ref_1669_ = v___x_1661_;
v_currNamespace_1670_ = v___x_1618_;
v_openDecls_1671_ = v___x_1642_;
v_initHeartbeats_1672_ = v___x_1620_;
v_maxHeartbeats_1673_ = v___x_1662_;
v_quotContext_1674_ = v___x_1618_;
v_currMacroScope_1675_ = v___x_1638_;
v_cancelTk_x3f_1676_ = v___x_1634_;
v_suppressElabErrors_1677_ = v_val_1630_;
v_inheritedTraceOptions_1678_ = v___x_1655_;
v___y_1679_ = v___x_1654_;
goto v___jp_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v___x_1717_ = _args[0];
lean_object* v___x_1718_ = _args[1];
lean_object* v___x_1719_ = _args[2];
lean_object* v___x_1720_ = _args[3];
lean_object* v___x_1721_ = _args[4];
lean_object* v_env_1722_ = _args[5];
lean_object* v___x_1723_ = _args[6];
lean_object* v___x_1724_ = _args[7];
lean_object* v_a_1725_ = _args[8];
lean_object* v_opts_1726_ = _args[9];
lean_object* v___x_1727_ = _args[10];
lean_object* v_pos_1728_ = _args[11];
lean_object* v_val_1729_ = _args[12];
lean_object* v___x_1730_ = _args[13];
lean_object* v___x_1731_ = _args[14];
lean_object* v___x_1732_ = _args[15];
lean_object* v___x_1733_ = _args[16];
lean_object* v___x_1734_ = _args[17];
lean_object* v_x_1735_ = _args[18];
lean_object* v___y_1736_ = _args[19];
_start:
{
size_t v___x_35585__boxed_1737_; uint8_t v___x_35586__boxed_1738_; uint8_t v_val_35590__boxed_1739_; uint8_t v___x_35595__boxed_1740_; lean_object* v_res_1741_; 
v___x_35585__boxed_1737_ = lean_unbox_usize(v___x_1720_);
lean_dec(v___x_1720_);
v___x_35586__boxed_1738_ = lean_unbox(v___x_1721_);
v_val_35590__boxed_1739_ = lean_unbox(v_val_1729_);
v___x_35595__boxed_1740_ = lean_unbox(v___x_1734_);
v_res_1741_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v___x_1717_, v___x_1718_, v___x_1719_, v___x_35585__boxed_1737_, v___x_35586__boxed_1738_, v_env_1722_, v___x_1723_, v___x_1724_, v_a_1725_, v_opts_1726_, v___x_1727_, v_pos_1728_, v_val_35590__boxed_1739_, v___x_1730_, v___x_1731_, v___x_1732_, v___x_1733_, v___x_35595__boxed_1740_, v_x_1735_);
lean_dec(v_pos_1728_);
lean_dec_ref(v_a_1725_);
lean_dec(v___x_1724_);
lean_dec(v___x_1718_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1742_, lean_object* v___x_1743_, lean_object* v_parserState_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v_toProcessingContext_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_toProcessingContext_1746_ = lean_ctor_get(v_a_1742_, 0);
v___x_1747_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1746_);
v___x_1748_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1746_, v___x_1743_, v_parserState_1744_, v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1749_, lean_object* v___x_1750_, lean_object* v_parserState_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1749_, v___x_1750_, v_parserState_1751_, v_x_1752_);
lean_dec_ref(v_a_1749_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1755_, size_t v_i_1756_, size_t v_stop_1757_, lean_object* v_b_1758_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_eq(v_i_1756_, v_stop_1757_);
if (v___x_1760_ == 0)
{
lean_object* v___f_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; size_t v___x_1764_; size_t v___x_1765_; 
v___f_1761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1762_ = lean_array_uget_borrowed(v_as_1755_, v_i_1756_);
lean_inc(v___x_1762_);
v___x_1763_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1761_, v___x_1762_);
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1756_, v___x_1764_);
v_i_1756_ = v___x_1765_;
v_b_1758_ = v___x_1763_;
goto _start;
}
else
{
return v_b_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_stop_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_){
_start:
{
size_t v_i_boxed_1772_; size_t v_stop_boxed_1773_; lean_object* v_res_1774_; 
v_i_boxed_1772_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_stop_boxed_1773_ = lean_unbox_usize(v_stop_1769_);
lean_dec(v_stop_1769_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1767_, v_i_boxed_1772_, v_stop_boxed_1773_, v_b_1770_);
lean_dec_ref(v_as_1767_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1775_, lean_object* v_cmds_1776_, lean_object* v_stx_1777_, lean_object* v_newParserState_1778_, lean_object* v_val_1779_, lean_object* v_sync_1780_, lean_object* v_val_1781_, lean_object* v_a_1782_, lean_object* v_oldNext_1783_, lean_object* v___y_1784_){
_start:
{
uint8_t v_sync_boxed_1785_; lean_object* v_res_1786_; 
v_sync_boxed_1785_ = lean_unbox(v_sync_1780_);
v_res_1786_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1775_, v_cmds_1776_, v_stx_1777_, v_newParserState_1778_, v_val_1779_, v_sync_boxed_1785_, v_val_1781_, v_a_1782_, v_oldNext_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1787_, lean_object* v_cmds_1788_, lean_object* v_stx_1789_, lean_object* v_newParserState_1790_, lean_object* v_val_1791_, uint8_t v_sync_1792_, lean_object* v_val_1793_, lean_object* v_a_1794_, lean_object* v_oldResult_1795_){
_start:
{
lean_object* v_task_1797_; lean_object* v___x_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; 
v_task_1797_ = lean_ctor_get(v_val_1787_, 3);
lean_inc_ref(v_task_1797_);
lean_dec_ref(v_val_1787_);
v___x_1798_ = lean_box(v_sync_1792_);
lean_inc_ref(v_a_1794_);
v___f_1799_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1799_, 0, v_oldResult_1795_);
lean_closure_set(v___f_1799_, 1, v_cmds_1788_);
lean_closure_set(v___f_1799_, 2, v_stx_1789_);
lean_closure_set(v___f_1799_, 3, v_newParserState_1790_);
lean_closure_set(v___f_1799_, 4, v_val_1791_);
lean_closure_set(v___f_1799_, 5, v___x_1798_);
lean_closure_set(v___f_1799_, 6, v_val_1793_);
lean_closure_set(v___f_1799_, 7, v_a_1794_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = 1;
v___x_1802_ = l_BaseIO_chainTask___redArg(v_task_1797_, v___f_1799_, v___x_1800_, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1803_, lean_object* v_cmds_1804_, lean_object* v_stx_1805_, lean_object* v_newParserState_1806_, lean_object* v_val_1807_, lean_object* v_sync_1808_, lean_object* v_val_1809_, lean_object* v_a_1810_, lean_object* v_oldResult_1811_, lean_object* v___y_1812_){
_start:
{
uint8_t v_sync_boxed_1813_; lean_object* v_res_1814_; 
v_sync_boxed_1813_ = lean_unbox(v_sync_1808_);
v_res_1814_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1803_, v_cmds_1804_, v_stx_1805_, v_newParserState_1806_, v_val_1807_, v_sync_boxed_1813_, v_val_1809_, v_a_1810_, v_oldResult_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1814_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1823_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1824_ = l_Lean_Name_append(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1825_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1829_, lean_object* v_val_1830_, lean_object* v_cmds_1831_, lean_object* v_fst_1832_, lean_object* v_fst_1833_, uint8_t v_val_1834_, lean_object* v_a_1835_, lean_object* v_snd_1836_, lean_object* v___x_1837_, uint8_t v___x_1838_, lean_object* v_fst_1839_, lean_object* v_val_1840_, lean_object* v_val_1841_, lean_object* v_val_1842_, lean_object* v_snd_1843_, lean_object* v_prom_1844_, lean_object* v___x_1845_, lean_object* v___f_1846_, lean_object* v___f_1847_, lean_object* v___f_1848_, lean_object* v_pos_1849_, lean_object* v_cmdState_1850_, lean_object* v___x_1851_, lean_object* v_opts_1852_, lean_object* v___x_1853_, lean_object* v_old_x3f_1854_, lean_object* v_parseCancelTk_1855_, lean_object* v_next_x3f_1856_){
_start:
{
lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v_snapshotTasks_1863_; lean_object* v___y_1864_; lean_object* v_traceTask_1865_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; size_t v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v_env_1907_; lean_object* v_messages_1908_; lean_object* v_scopes_1909_; lean_object* v_infoState_1910_; lean_object* v_traceState_1911_; lean_object* v_snapshotTasks_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_reportedCmdState_1915_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; size_t v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v_reportedCmdState_1972_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; size_t v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; size_t v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2036_; 
if (lean_obj_tag(v_next_x3f_1856_) == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref(v_parseCancelTk_1855_);
v___x_2089_ = lean_box(0);
v___y_2036_ = v___x_2089_;
goto v___jp_2035_;
}
else
{
lean_object* v_toProcessingContext_2090_; lean_object* v_val_2091_; lean_object* v_pos_2092_; lean_object* v_endPos_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_toProcessingContext_2090_ = lean_ctor_get(v_a_1835_, 0);
v_val_2091_ = lean_ctor_get(v_next_x3f_1856_, 0);
v_pos_2092_ = lean_ctor_get(v_fst_1833_, 0);
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
lean_ctor_set(v___x_2097_, 0, v_parseCancelTk_1855_);
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
v___jp_1858_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1866_, 0, v___y_1860_);
lean_ctor_set(v___x_1866_, 1, v___x_1829_);
lean_ctor_set(v___x_1866_, 2, v___y_1864_);
lean_ctor_set(v___x_1866_, 3, v_traceTask_1865_);
v___x_1867_ = lean_array_push(v_snapshotTasks_1863_, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___y_1861_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_io_promise_resolve(v___x_1868_, v_val_1830_);
if (lean_obj_tag(v_next_x3f_1856_) == 1)
{
lean_object* v_val_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_val_1870_ = lean_ctor_get(v_next_x3f_1856_, 0);
lean_inc(v_val_1870_);
lean_dec_ref_known(v_next_x3f_1856_, 1);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_array_push(v_cmds_1831_, v_fst_1832_);
v___x_1873_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1871_, v_fst_1833_, v___y_1862_, v_val_1870_, v_val_1834_, v___y_1859_, v___x_1872_, v_a_1835_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; 
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1859_);
lean_dec(v_next_x3f_1856_);
lean_dec_ref(v_fst_1833_);
lean_dec(v_fst_1832_);
lean_dec_ref(v_cmds_1831_);
v___x_1874_ = lean_box(0);
return v___x_1874_;
}
}
v___jp_1875_:
{
lean_object* v_snapshotTasks_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_snapshotTasks_1882_ = lean_ctor_get(v___y_1879_, 10);
lean_inc_ref(v_snapshotTasks_1882_);
v___x_1883_ = lean_mk_empty_array_with_capacity(v___y_1876_);
lean_dec(v___y_1876_);
lean_inc_ref(v___y_1880_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___y_1880_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_task_pure(v___x_1884_);
v___y_1859_ = v___y_1877_;
v___y_1860_ = v___y_1878_;
v___y_1861_ = v___y_1880_;
v___y_1862_ = v___y_1879_;
v_snapshotTasks_1863_ = v_snapshotTasks_1882_;
v___y_1864_ = v___y_1881_;
v_traceTask_1865_ = v___x_1885_;
goto v___jp_1858_;
}
v___jp_1886_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_opts_1925_; uint8_t v_hasTrace_1926_; 
v___x_1916_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1908_);
v___x_1917_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1917_, 0, v___y_1904_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
lean_ctor_set(v___x_1917_, 2, v___y_1905_);
lean_ctor_set(v___x_1917_, 3, v_traceState_1911_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*4, v_val_1834_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v_reportedCmdState_1915_);
v___x_1919_ = lean_io_promise_resolve(v___x_1918_, v_val_1841_);
v___x_1920_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1910_);
lean_inc(v___y_1895_);
v___x_1921_ = l_BaseIO_chainTask___redArg(v___x_1920_, v___y_1903_, v___y_1895_, v___x_1838_);
v___x_1922_ = l_Lean_inheritedTraceOptions;
v___x_1923_ = lean_st_ref_get(v___x_1922_);
v___x_1924_ = l_List_head_x21___redArg(v___x_1845_, v_scopes_1909_);
lean_dec(v_scopes_1909_);
lean_dec_ref(v___x_1845_);
v_opts_1925_ = lean_ctor_get(v___x_1924_, 1);
lean_inc_ref(v_opts_1925_);
lean_dec(v___x_1924_);
v_hasTrace_1926_ = lean_ctor_get_uint8(v_opts_1925_, sizeof(void*)*1);
if (v_hasTrace_1926_ == 0)
{
lean_dec_ref(v_opts_1925_);
lean_dec(v___x_1923_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_snapshotTasks_1912_);
lean_dec_ref(v_env_1907_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1887_);
lean_dec(v_pos_1849_);
lean_dec_ref(v___f_1848_);
lean_dec_ref(v___f_1847_);
lean_dec_ref(v___f_1846_);
lean_dec(v___x_1837_);
v___y_1876_ = v___y_1895_;
v___y_1877_ = v___y_1896_;
v___y_1878_ = v___y_1898_;
v___y_1879_ = v___y_1906_;
v___y_1880_ = v___y_1899_;
v___y_1881_ = v___y_1900_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_1928_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1923_, v_opts_1925_, v___x_1927_);
lean_dec(v___x_1923_);
if (v___x_1928_ == 0)
{
lean_dec_ref(v_opts_1925_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_snapshotTasks_1912_);
lean_dec_ref(v_env_1907_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1887_);
lean_dec(v_pos_1849_);
lean_dec_ref(v___f_1848_);
lean_dec_ref(v___f_1847_);
lean_dec_ref(v___f_1846_);
lean_dec(v___x_1837_);
v___y_1876_ = v___y_1895_;
v___y_1877_ = v___y_1896_;
v___y_1878_ = v___y_1898_;
v___y_1879_ = v___y_1906_;
v___y_1880_ = v___y_1899_;
v___y_1881_ = v___y_1900_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; 
lean_inc_n(v___y_1895_, 3);
v___x_1929_ = lean_task_map(v___f_1846_, v___y_1897_, v___y_1895_, v___x_1838_);
lean_inc_n(v___y_1900_, 3);
lean_inc_n(v___y_1914_, 2);
lean_inc_n(v___y_1901_, 2);
v___x_1930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1930_, 0, v___y_1901_);
lean_ctor_set(v___x_1930_, 1, v___y_1914_);
lean_ctor_set(v___x_1930_, 2, v___y_1900_);
lean_ctor_set(v___x_1930_, 3, v___x_1929_);
v___x_1931_ = lean_task_map(v___f_1847_, v___y_1902_, v___y_1895_, v___x_1838_);
v___x_1932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1932_, 0, v___y_1901_);
lean_ctor_set(v___x_1932_, 1, v___y_1914_);
lean_ctor_set(v___x_1932_, 2, v___y_1900_);
lean_ctor_set(v___x_1932_, 3, v___x_1931_);
v___x_1933_ = lean_task_map(v___f_1848_, v___y_1913_, v___y_1895_, v___x_1838_);
v___x_1934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1934_, 0, v___y_1901_);
lean_ctor_set(v___x_1934_, 1, v___y_1914_);
lean_ctor_set(v___x_1934_, 2, v___y_1900_);
lean_ctor_set(v___x_1934_, 3, v___x_1933_);
v___x_1935_ = lean_unsigned_to_nat(3u);
v___x_1936_ = lean_mk_empty_array_with_capacity(v___x_1935_);
v___x_1937_ = lean_array_push(v___x_1936_, v___x_1930_);
v___x_1938_ = lean_array_push(v___x_1937_, v___x_1932_);
v___x_1939_ = lean_array_push(v___x_1938_, v___x_1934_);
v___x_1940_ = l_Array_append___redArg(v___x_1939_, v_snapshotTasks_1912_);
lean_inc_ref(v___y_1899_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___y_1899_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
lean_inc_ref(v___x_1941_);
v___x_1942_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1941_);
v___x_1943_ = lean_box_usize(v___y_1892_);
v___x_1944_ = lean_box(v___x_1838_);
v___x_1945_ = lean_box(v_val_1834_);
v___x_1946_ = lean_box(v___x_1928_);
lean_inc_ref(v_a_1835_);
lean_inc_ref(v___y_1888_);
v___f_1947_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1947_, 0, v___x_1837_);
lean_closure_set(v___f_1947_, 1, v___y_1890_);
lean_closure_set(v___f_1947_, 2, v___y_1894_);
lean_closure_set(v___f_1947_, 3, v___x_1943_);
lean_closure_set(v___f_1947_, 4, v___x_1944_);
lean_closure_set(v___f_1947_, 5, v_env_1907_);
lean_closure_set(v___f_1947_, 6, v___y_1888_);
lean_closure_set(v___f_1947_, 7, v___x_1922_);
lean_closure_set(v___f_1947_, 8, v_a_1835_);
lean_closure_set(v___f_1947_, 9, v_opts_1925_);
lean_closure_set(v___f_1947_, 10, v___x_1941_);
lean_closure_set(v___f_1947_, 11, v_pos_1849_);
lean_closure_set(v___f_1947_, 12, v___x_1945_);
lean_closure_set(v___f_1947_, 13, v___y_1891_);
lean_closure_set(v___f_1947_, 14, v___y_1889_);
lean_closure_set(v___f_1947_, 15, v___y_1887_);
lean_closure_set(v___f_1947_, 16, v___y_1893_);
lean_closure_set(v___f_1947_, 17, v___x_1946_);
v___x_1948_ = lean_io_bind_task(v___x_1942_, v___f_1947_, v___y_1895_, v_val_1834_);
v___y_1859_ = v___y_1896_;
v___y_1860_ = v___y_1898_;
v___y_1861_ = v___y_1899_;
v___y_1862_ = v___y_1906_;
v_snapshotTasks_1863_ = v_snapshotTasks_1912_;
v___y_1864_ = v___y_1900_;
v_traceTask_1865_ = v___x_1948_;
goto v___jp_1858_;
}
}
}
v___jp_1949_:
{
lean_object* v_env_1973_; lean_object* v_messages_1974_; lean_object* v_scopes_1975_; lean_object* v_infoState_1976_; lean_object* v_traceState_1977_; lean_object* v_snapshotTasks_1978_; 
v_env_1973_ = lean_ctor_get(v___y_1969_, 0);
lean_inc_ref(v_env_1973_);
v_messages_1974_ = lean_ctor_get(v___y_1969_, 1);
lean_inc_ref(v_messages_1974_);
v_scopes_1975_ = lean_ctor_get(v___y_1969_, 2);
lean_inc(v_scopes_1975_);
v_infoState_1976_ = lean_ctor_get(v___y_1969_, 8);
lean_inc_ref(v_infoState_1976_);
v_traceState_1977_ = lean_ctor_get(v___y_1969_, 9);
lean_inc_ref(v_traceState_1977_);
v_snapshotTasks_1978_ = lean_ctor_get(v___y_1969_, 10);
lean_inc_ref(v_snapshotTasks_1978_);
v___y_1887_ = v___y_1950_;
v___y_1888_ = v___y_1951_;
v___y_1889_ = v___y_1953_;
v___y_1890_ = v___y_1952_;
v___y_1891_ = v___y_1955_;
v___y_1892_ = v___y_1954_;
v___y_1893_ = v___y_1956_;
v___y_1894_ = v___y_1957_;
v___y_1895_ = v___y_1958_;
v___y_1896_ = v___y_1959_;
v___y_1897_ = v___y_1960_;
v___y_1898_ = v___y_1961_;
v___y_1899_ = v___y_1962_;
v___y_1900_ = v___y_1963_;
v___y_1901_ = v___y_1964_;
v___y_1902_ = v___y_1965_;
v___y_1903_ = v___y_1966_;
v___y_1904_ = v___y_1967_;
v___y_1905_ = v___y_1968_;
v___y_1906_ = v___y_1969_;
v_env_1907_ = v_env_1973_;
v_messages_1908_ = v_messages_1974_;
v_scopes_1909_ = v_scopes_1975_;
v_infoState_1910_ = v_infoState_1976_;
v_traceState_1911_ = v_traceState_1977_;
v_snapshotTasks_1912_ = v_snapshotTasks_1978_;
v___y_1913_ = v___y_1970_;
v___y_1914_ = v___y_1971_;
v_reportedCmdState_1915_ = v_reportedCmdState_1972_;
goto v___jp_1886_;
}
v___jp_1979_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___f_2008_; uint8_t v___x_2009_; 
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___y_2003_);
lean_ctor_set(v___x_2004_, 1, v_val_1840_);
lean_inc_ref(v___y_1990_);
lean_inc_n(v_pos_1849_, 2);
lean_inc_ref(v_cmds_1831_);
lean_inc(v_fst_1832_);
v___x_2005_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1832_, v_cmds_1831_, v_cmdState_1850_, v_pos_1849_, v___x_2004_, v___y_1990_, v_a_1835_);
v___x_2006_ = lean_box(v_val_1834_);
v___x_2007_ = lean_box(v___x_1838_);
lean_inc_ref(v_a_1835_);
lean_inc(v___y_1987_);
lean_inc_ref(v___x_1845_);
lean_inc_ref(v___x_2005_);
lean_inc_ref(v___y_1981_);
lean_inc_ref(v___y_1985_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2008_, 0, v___y_1985_);
lean_closure_set(v___f_2008_, 1, v___y_1981_);
lean_closure_set(v___f_2008_, 2, v___x_2006_);
lean_closure_set(v___f_2008_, 3, v_val_1842_);
lean_closure_set(v___f_2008_, 4, v___x_2005_);
lean_closure_set(v___f_2008_, 5, v___x_1845_);
lean_closure_set(v___f_2008_, 6, v___y_1987_);
lean_closure_set(v___f_2008_, 7, v___x_2007_);
lean_closure_set(v___f_2008_, 8, v_a_1835_);
lean_closure_set(v___f_2008_, 9, v_pos_1849_);
lean_closure_set(v___f_2008_, 10, v___x_1851_);
v___x_2009_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1852_, v___x_1853_);
if (v___x_2009_ == 0)
{
lean_dec(v___y_2001_);
lean_inc_ref(v___x_2005_);
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1982_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1985_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v___f_2008_;
v___y_1967_ = v___y_1997_;
v___y_1968_ = v___y_1998_;
v___y_1969_ = v___x_2005_;
v___y_1970_ = v___y_2000_;
v___y_1971_ = v___y_2002_;
v_reportedCmdState_1972_ = v___x_2005_;
goto v___jp_1949_;
}
else
{
uint8_t v___x_2010_; 
lean_inc(v_fst_1832_);
v___x_2010_ = l_Lean_Parser_isTerminalCommand(v_fst_1832_);
if (v___x_2010_ == 0)
{
if (v___x_2009_ == 0)
{
lean_dec(v___y_2001_);
lean_inc_ref(v___x_2005_);
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1982_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1985_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v___f_2008_;
v___y_1967_ = v___y_1997_;
v___y_1968_ = v___y_1998_;
v___y_1969_ = v___x_2005_;
v___y_1970_ = v___y_2000_;
v___y_1971_ = v___y_2002_;
v_reportedCmdState_1972_ = v___x_2005_;
goto v___jp_1949_;
}
else
{
lean_object* v_env_2011_; lean_object* v_messages_2012_; lean_object* v_scopes_2013_; lean_object* v_infoState_2014_; lean_object* v_traceState_2015_; lean_object* v_snapshotTasks_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
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
v___x_2017_ = lean_mk_empty_array_with_capacity(v___y_2001_);
lean_dec(v___y_2001_);
lean_inc_ref(v___x_2017_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_inc_n(v___y_1988_, 3);
v___x_2019_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
lean_ctor_set(v___x_2019_, 1, v___x_2017_);
lean_ctor_set(v___x_2019_, 2, v___y_1988_);
lean_ctor_set(v___x_2019_, 3, v___y_1988_);
lean_ctor_set_usize(v___x_2019_, 4, v___y_1999_);
v___x_2020_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2019_, 2);
v___x_2021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2019_);
lean_ctor_set(v___x_2021_, 2, v___x_2020_);
v___x_2022_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2023_ = l_Lean_Options_empty;
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_mk_empty_array_with_capacity(v___y_1988_);
lean_inc_ref_n(v___x_2025_, 3);
lean_inc_n(v___x_1837_, 2);
v___x_2026_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2026_, 0, v___x_2022_);
lean_ctor_set(v___x_2026_, 1, v___x_2023_);
lean_ctor_set(v___x_2026_, 2, v___x_1837_);
lean_ctor_set(v___x_2026_, 3, v___x_2024_);
lean_ctor_set(v___x_2026_, 4, v___x_2024_);
lean_ctor_set(v___x_2026_, 5, v___x_2025_);
lean_ctor_set(v___x_2026_, 6, v___x_2025_);
lean_ctor_set(v___x_2026_, 7, v___x_2024_);
lean_ctor_set(v___x_2026_, 8, v___x_2024_);
lean_ctor_set(v___x_2026_, 9, v___x_2024_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10, v_val_1834_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10 + 1, v_val_1834_);
lean_ctor_set_uint8(v___x_2026_, sizeof(void*)*10 + 2, v_val_1834_);
v___x_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___x_2024_);
v___x_2028_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2029_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2030_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1837_);
v___x_2031_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
lean_ctor_set(v___x_2032_, 2, v___x_2019_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*3, v___x_1838_);
v___x_2033_ = lean_box(0);
lean_inc_ref(v___y_1989_);
v___x_2034_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2034_, 0, v_env_2011_);
lean_ctor_set(v___x_2034_, 1, v___x_2021_);
lean_ctor_set(v___x_2034_, 2, v___x_2027_);
lean_ctor_set(v___x_2034_, 3, v___x_2020_);
lean_ctor_set(v___x_2034_, 4, v___x_2028_);
lean_ctor_set(v___x_2034_, 5, v___y_1988_);
lean_ctor_set(v___x_2034_, 6, v___x_2029_);
lean_ctor_set(v___x_2034_, 7, v___x_2030_);
lean_ctor_set(v___x_2034_, 8, v___x_2032_);
lean_ctor_set(v___x_2034_, 9, v___y_1989_);
lean_ctor_set(v___x_2034_, 10, v___x_2025_);
lean_ctor_set(v___x_2034_, 11, v___x_2033_);
lean_ctor_set(v___x_2034_, 12, v___x_2025_);
v___y_1887_ = v___y_1980_;
v___y_1888_ = v___y_1981_;
v___y_1889_ = v___y_1982_;
v___y_1890_ = v___y_1983_;
v___y_1891_ = v___y_1985_;
v___y_1892_ = v___y_1984_;
v___y_1893_ = v___y_1986_;
v___y_1894_ = v___y_1987_;
v___y_1895_ = v___y_1988_;
v___y_1896_ = v___y_1990_;
v___y_1897_ = v___y_1991_;
v___y_1898_ = v___y_1992_;
v___y_1899_ = v___y_1993_;
v___y_1900_ = v___y_1994_;
v___y_1901_ = v___y_1995_;
v___y_1902_ = v___y_1996_;
v___y_1903_ = v___f_2008_;
v___y_1904_ = v___y_1997_;
v___y_1905_ = v___y_1998_;
v___y_1906_ = v___x_2005_;
v_env_1907_ = v_env_2011_;
v_messages_1908_ = v_messages_2012_;
v_scopes_1909_ = v_scopes_2013_;
v_infoState_1910_ = v_infoState_2014_;
v_traceState_1911_ = v_traceState_2015_;
v_snapshotTasks_1912_ = v_snapshotTasks_2016_;
v___y_1913_ = v___y_2000_;
v___y_1914_ = v___y_2002_;
v_reportedCmdState_1915_ = v___x_2034_;
goto v___jp_1886_;
}
}
else
{
lean_dec(v___y_2001_);
lean_inc_ref(v___x_2005_);
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1983_;
v___y_1953_ = v___y_1982_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1985_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v___y_1966_ = v___f_2008_;
v___y_1967_ = v___y_1997_;
v___y_1968_ = v___y_1998_;
v___y_1969_ = v___x_2005_;
v___y_1970_ = v___y_2000_;
v___y_1971_ = v___y_2002_;
v_reportedCmdState_1972_ = v___x_2005_;
goto v___jp_1949_;
}
}
}
v___jp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2037_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1836_);
v___x_2038_ = l_IO_CancelToken_new();
v___x_2039_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1837_);
v___x_2040_ = l_Lean_Name_str___override(v___x_1837_, v___x_2039_);
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
v___x_2053_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2054_ = l_Lean_Name_str___override(v___x_2052_, v___x_2053_);
v___x_2055_ = l_Lean_Name_toString(v___x_2054_, v___x_1838_);
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
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*4, v_val_1834_);
v___x_2061_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2062_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2062_, 0, v___x_2055_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_ctor_set(v___x_2062_, 2, v___x_2056_);
lean_ctor_set(v___x_2062_, 3, v___x_2059_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*4, v_val_1834_);
lean_inc(v_fst_1839_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_fst_1839_);
v___x_2064_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2063_);
lean_inc_ref(v___x_2038_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2038_);
v___x_2066_ = l_IO_Promise_result_x21___redArg(v_val_1840_);
lean_inc_ref(v___x_2066_);
lean_inc(v___x_2064_);
lean_inc_ref_n(v___x_2063_, 3);
v___x_2067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2063_);
lean_ctor_set(v___x_2067_, 1, v___x_2064_);
lean_ctor_set(v___x_2067_, 2, v___x_2065_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
v___x_2068_ = l_IO_Promise_result_x21___redArg(v_val_1841_);
lean_inc_ref(v___x_2068_);
lean_inc_n(v___x_1829_, 3);
v___x_2069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2063_);
lean_ctor_set(v___x_2069_, 1, v___x_1829_);
lean_ctor_set(v___x_2069_, 2, v___x_2056_);
lean_ctor_set(v___x_2069_, 3, v___x_2068_);
v___x_2070_ = l_IO_Promise_result_x21___redArg(v_val_1842_);
lean_inc_ref(v___x_2070_);
v___x_2071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2063_);
lean_ctor_set(v___x_2071_, 1, v___x_1829_);
lean_ctor_set(v___x_2071_, 2, v___x_2056_);
lean_ctor_set(v___x_2071_, 3, v___x_2070_);
v___x_2072_ = l_IO_Promise_result_x21___redArg(v_val_1830_);
v___x_2073_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2056_);
lean_ctor_set(v___x_2073_, 1, v___x_1829_);
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
lean_ctor_set(v___x_2075_, 1, v_fst_1839_);
lean_ctor_set(v___x_2075_, 2, v_snd_1843_);
lean_ctor_set(v___x_2075_, 3, v___x_2074_);
lean_ctor_set(v___x_2075_, 4, v___y_2036_);
v___x_2076_ = lean_io_promise_resolve(v___x_2075_, v_prom_1844_);
if (lean_obj_tag(v_old_x3f_1854_) == 0)
{
lean_inc_ref(v___x_2055_);
lean_inc_ref(v___x_2062_);
v___y_1980_ = v___x_2062_;
v___y_1981_ = v___x_2059_;
v___y_1982_ = v___x_2056_;
v___y_1983_ = v___x_2057_;
v___y_1984_ = v___x_2058_;
v___y_1985_ = v___x_2055_;
v___y_1986_ = v___x_2056_;
v___y_1987_ = v___x_2046_;
v___y_1988_ = v___x_2046_;
v___y_1989_ = v___x_2059_;
v___y_1990_ = v___x_2038_;
v___y_1991_ = v___x_2066_;
v___y_1992_ = v___x_2056_;
v___y_1993_ = v___x_2062_;
v___y_1994_ = v___x_2056_;
v___y_1995_ = v___x_2063_;
v___y_1996_ = v___x_2068_;
v___y_1997_ = v___x_2055_;
v___y_1998_ = v___x_2056_;
v___y_1999_ = v___x_2058_;
v___y_2000_ = v___x_2070_;
v___y_2001_ = v___x_2057_;
v___y_2002_ = v___x_2064_;
v___y_2003_ = v___x_2056_;
goto v___jp_1979_;
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2088_; 
v_val_2077_ = lean_ctor_get(v_old_x3f_1854_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_old_x3f_1854_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2079_ = v_old_x3f_1854_;
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v_old_x3f_1854_);
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
lean_inc_ref(v___x_2055_);
lean_inc_ref(v___x_2062_);
v___y_1980_ = v___x_2062_;
v___y_1981_ = v___x_2059_;
v___y_1982_ = v___x_2056_;
v___y_1983_ = v___x_2057_;
v___y_1984_ = v___x_2058_;
v___y_1985_ = v___x_2055_;
v___y_1986_ = v___x_2056_;
v___y_1987_ = v___x_2046_;
v___y_1988_ = v___x_2046_;
v___y_1989_ = v___x_2059_;
v___y_1990_ = v___x_2038_;
v___y_1991_ = v___x_2066_;
v___y_1992_ = v___x_2056_;
v___y_1993_ = v___x_2062_;
v___y_1994_ = v___x_2056_;
v___y_1995_ = v___x_2063_;
v___y_1996_ = v___x_2068_;
v___y_1997_ = v___x_2055_;
v___y_1998_ = v___x_2056_;
v___y_1999_ = v___x_2058_;
v___y_2000_ = v___x_2070_;
v___y_2001_ = v___x_2057_;
v___y_2002_ = v___x_2064_;
v___y_2003_ = v___x_2086_;
goto v___jp_1979_;
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
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2104_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_cmds_2105_, lean_object* v_fst_2106_, lean_object* v_fst_2107_, uint8_t v_val_2108_, lean_object* v_a_2109_, lean_object* v_snd_2110_, lean_object* v___x_2111_, uint8_t v___x_2112_, lean_object* v_prom_2113_, lean_object* v___x_2114_, lean_object* v___f_2115_, lean_object* v___f_2116_, lean_object* v___f_2117_, lean_object* v_pos_2118_, lean_object* v_cmdState_2119_, lean_object* v___x_2120_, lean_object* v_opts_2121_, lean_object* v_old_x3f_2122_, lean_object* v_parseCancelTk_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v_traceTask_2138_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2162_; lean_object* v___y_2163_; size_t v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v_env_2180_; lean_object* v_messages_2181_; lean_object* v_scopes_2182_; lean_object* v_infoState_2183_; lean_object* v_traceState_2184_; lean_object* v_snapshotTasks_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v_reportedCmdState_2192_; lean_object* v___y_2227_; size_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v_reportedCmdState_2251_; lean_object* v___x_2258_; lean_object* v___y_2260_; lean_object* v___y_2261_; size_t v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; size_t v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; uint8_t v___x_2409_; 
v___x_2125_ = lean_io_promise_new();
v___x_2126_ = lean_io_promise_new();
v___x_2127_ = lean_io_promise_new();
v___x_2128_ = lean_io_promise_new();
v___x_2258_ = l_Lean_internal_cmdlineSnapshots;
v___x_2409_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2121_, v___x_2258_);
if (v___x_2409_ == 0)
{
lean_inc_ref(v_fst_2107_);
lean_inc(v_fst_2106_);
v_fst_2396_ = v_fst_2106_;
v_snd_2397_ = v_fst_2107_;
goto v___jp_2395_;
}
else
{
uint8_t v___x_2410_; 
lean_inc(v_fst_2106_);
v___x_2410_ = l_Lean_Parser_isTerminalCommand(v_fst_2106_);
if (v___x_2410_ == 0)
{
if (v___x_2409_ == 0)
{
lean_inc_ref(v_fst_2107_);
lean_inc(v_fst_2106_);
v_fst_2396_ = v_fst_2106_;
v_snd_2397_ = v_fst_2107_;
goto v___jp_2395_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_box(0);
v___x_2412_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2396_ = v___x_2411_;
v_snd_2397_ = v___x_2412_;
goto v___jp_2395_;
}
}
else
{
lean_inc_ref(v_fst_2107_);
lean_inc(v_fst_2106_);
v_fst_2396_ = v_fst_2106_;
v_snd_2397_ = v_fst_2107_;
goto v___jp_2395_;
}
}
v___jp_2129_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2139_, 0, v___y_2132_);
lean_ctor_set(v___x_2139_, 1, v___y_2136_);
lean_ctor_set(v___x_2139_, 2, v___y_2137_);
lean_ctor_set(v___x_2139_, 3, v_traceTask_2138_);
v___x_2140_ = lean_array_push(v_snapshotTasks_2134_, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___y_2130_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_io_promise_resolve(v___x_2141_, v___x_2128_);
lean_dec(v___x_2128_);
if (lean_obj_tag(v___y_2135_) == 1)
{
lean_object* v_val_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_val_2143_ = lean_ctor_get(v___y_2135_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v___y_2135_, 1);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_array_push(v_cmds_2105_, v_fst_2106_);
v___x_2146_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2144_, v_fst_2107_, v___y_2133_, v_val_2143_, v_val_2108_, v___y_2131_, v___x_2145_, v_a_2109_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; 
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_fst_2107_);
lean_dec(v_fst_2106_);
lean_dec_ref(v_cmds_2105_);
v___x_2147_ = lean_box(0);
return v___x_2147_;
}
}
v___jp_2148_:
{
lean_object* v_snapshotTasks_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_snapshotTasks_2157_ = lean_ctor_get(v___y_2150_, 10);
lean_inc_ref(v_snapshotTasks_2157_);
v___x_2158_ = lean_mk_empty_array_with_capacity(v___y_2155_);
lean_dec(v___y_2155_);
lean_inc_ref(v___y_2149_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___y_2149_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_task_pure(v___x_2159_);
v___y_2130_ = v___y_2149_;
v___y_2131_ = v___y_2152_;
v___y_2132_ = v___y_2151_;
v___y_2133_ = v___y_2150_;
v_snapshotTasks_2134_ = v_snapshotTasks_2157_;
v___y_2135_ = v___y_2153_;
v___y_2136_ = v___y_2154_;
v___y_2137_ = v___y_2156_;
v_traceTask_2138_ = v___x_2160_;
goto v___jp_2129_;
}
v___jp_2161_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_opts_2202_; uint8_t v_hasTrace_2203_; 
v___x_2193_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2181_);
v___x_2194_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2194_, 0, v___y_2177_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_ctor_set(v___x_2194_, 2, v___y_2175_);
lean_ctor_set(v___x_2194_, 3, v_traceState_2184_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*4, v_val_2108_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v_reportedCmdState_2192_);
v___x_2196_ = lean_io_promise_resolve(v___x_2195_, v___x_2126_);
lean_dec(v___x_2126_);
v___x_2197_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2183_);
lean_inc(v___y_2188_);
v___x_2198_ = l_BaseIO_chainTask___redArg(v___x_2197_, v___y_2191_, v___y_2188_, v___x_2112_);
v___x_2199_ = l_Lean_inheritedTraceOptions;
v___x_2200_ = lean_st_ref_get(v___x_2199_);
v___x_2201_ = l_List_head_x21___redArg(v___x_2114_, v_scopes_2182_);
lean_dec(v_scopes_2182_);
lean_dec_ref(v___x_2114_);
v_opts_2202_ = lean_ctor_get(v___x_2201_, 1);
lean_inc_ref(v_opts_2202_);
lean_dec(v___x_2201_);
v_hasTrace_2203_ = lean_ctor_get_uint8(v_opts_2202_, sizeof(void*)*1);
if (v_hasTrace_2203_ == 0)
{
lean_dec_ref(v_opts_2202_);
lean_dec(v___x_2200_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v_snapshotTasks_2185_);
lean_dec_ref(v_env_2180_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec(v_pos_2118_);
lean_dec_ref(v___f_2117_);
lean_dec_ref(v___f_2116_);
lean_dec_ref(v___f_2115_);
lean_dec(v___x_2111_);
v___y_2149_ = v___y_2178_;
v___y_2150_ = v___y_2179_;
v___y_2151_ = v___y_2172_;
v___y_2152_ = v___y_2186_;
v___y_2153_ = v___y_2187_;
v___y_2154_ = v___y_2173_;
v___y_2155_ = v___y_2188_;
v___y_2156_ = v___y_2174_;
goto v___jp_2148_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2205_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2200_, v_opts_2202_, v___x_2204_);
lean_dec(v___x_2200_);
if (v___x_2205_ == 0)
{
lean_dec_ref(v_opts_2202_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v_snapshotTasks_2185_);
lean_dec_ref(v_env_2180_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec(v_pos_2118_);
lean_dec_ref(v___f_2117_);
lean_dec_ref(v___f_2116_);
lean_dec_ref(v___f_2115_);
lean_dec(v___x_2111_);
v___y_2149_ = v___y_2178_;
v___y_2150_ = v___y_2179_;
v___y_2151_ = v___y_2172_;
v___y_2152_ = v___y_2186_;
v___y_2153_ = v___y_2187_;
v___y_2154_ = v___y_2173_;
v___y_2155_ = v___y_2188_;
v___y_2156_ = v___y_2174_;
goto v___jp_2148_;
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; 
lean_inc_n(v___y_2188_, 3);
v___x_2206_ = lean_task_map(v___f_2115_, v___y_2176_, v___y_2188_, v___x_2112_);
lean_inc_n(v___y_2174_, 3);
lean_inc_n(v___y_2190_, 2);
lean_inc_n(v___y_2189_, 2);
v___x_2207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2189_);
lean_ctor_set(v___x_2207_, 1, v___y_2190_);
lean_ctor_set(v___x_2207_, 2, v___y_2174_);
lean_ctor_set(v___x_2207_, 3, v___x_2206_);
v___x_2208_ = lean_task_map(v___f_2116_, v___y_2171_, v___y_2188_, v___x_2112_);
v___x_2209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2209_, 0, v___y_2189_);
lean_ctor_set(v___x_2209_, 1, v___y_2190_);
lean_ctor_set(v___x_2209_, 2, v___y_2174_);
lean_ctor_set(v___x_2209_, 3, v___x_2208_);
v___x_2210_ = lean_task_map(v___f_2117_, v___y_2170_, v___y_2188_, v___x_2112_);
v___x_2211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2189_);
lean_ctor_set(v___x_2211_, 1, v___y_2190_);
lean_ctor_set(v___x_2211_, 2, v___y_2174_);
lean_ctor_set(v___x_2211_, 3, v___x_2210_);
v___x_2212_ = lean_unsigned_to_nat(3u);
v___x_2213_ = lean_mk_empty_array_with_capacity(v___x_2212_);
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2207_);
v___x_2215_ = lean_array_push(v___x_2214_, v___x_2209_);
v___x_2216_ = lean_array_push(v___x_2215_, v___x_2211_);
v___x_2217_ = l_Array_append___redArg(v___x_2216_, v_snapshotTasks_2185_);
lean_inc_ref(v___y_2178_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___y_2178_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
lean_inc_ref(v___x_2218_);
v___x_2219_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2218_);
v___x_2220_ = lean_box_usize(v___y_2164_);
v___x_2221_ = lean_box(v___x_2112_);
v___x_2222_ = lean_box(v_val_2108_);
v___x_2223_ = lean_box(v___x_2205_);
lean_inc_ref(v_a_2109_);
lean_inc_ref(v___y_2165_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2224_, 0, v___x_2111_);
lean_closure_set(v___f_2224_, 1, v___y_2168_);
lean_closure_set(v___f_2224_, 2, v___y_2162_);
lean_closure_set(v___f_2224_, 3, v___x_2220_);
lean_closure_set(v___f_2224_, 4, v___x_2221_);
lean_closure_set(v___f_2224_, 5, v_env_2180_);
lean_closure_set(v___f_2224_, 6, v___y_2165_);
lean_closure_set(v___f_2224_, 7, v___x_2199_);
lean_closure_set(v___f_2224_, 8, v_a_2109_);
lean_closure_set(v___f_2224_, 9, v_opts_2202_);
lean_closure_set(v___f_2224_, 10, v___x_2218_);
lean_closure_set(v___f_2224_, 11, v_pos_2118_);
lean_closure_set(v___f_2224_, 12, v___x_2222_);
lean_closure_set(v___f_2224_, 13, v___y_2166_);
lean_closure_set(v___f_2224_, 14, v___y_2167_);
lean_closure_set(v___f_2224_, 15, v___y_2163_);
lean_closure_set(v___f_2224_, 16, v___y_2169_);
lean_closure_set(v___f_2224_, 17, v___x_2223_);
v___x_2225_ = lean_io_bind_task(v___x_2219_, v___f_2224_, v___y_2188_, v_val_2108_);
v___y_2130_ = v___y_2178_;
v___y_2131_ = v___y_2186_;
v___y_2132_ = v___y_2172_;
v___y_2133_ = v___y_2179_;
v_snapshotTasks_2134_ = v_snapshotTasks_2185_;
v___y_2135_ = v___y_2187_;
v___y_2136_ = v___y_2173_;
v___y_2137_ = v___y_2174_;
v_traceTask_2138_ = v___x_2225_;
goto v___jp_2129_;
}
}
}
v___jp_2226_:
{
lean_object* v_env_2252_; lean_object* v_messages_2253_; lean_object* v_scopes_2254_; lean_object* v_infoState_2255_; lean_object* v_traceState_2256_; lean_object* v_snapshotTasks_2257_; 
v_env_2252_ = lean_ctor_get(v___y_2244_, 0);
lean_inc_ref(v_env_2252_);
v_messages_2253_ = lean_ctor_get(v___y_2244_, 1);
lean_inc_ref(v_messages_2253_);
v_scopes_2254_ = lean_ctor_get(v___y_2244_, 2);
lean_inc(v_scopes_2254_);
v_infoState_2255_ = lean_ctor_get(v___y_2244_, 8);
lean_inc_ref(v_infoState_2255_);
v_traceState_2256_ = lean_ctor_get(v___y_2244_, 9);
lean_inc_ref(v_traceState_2256_);
v_snapshotTasks_2257_ = lean_ctor_get(v___y_2244_, 10);
lean_inc_ref(v_snapshotTasks_2257_);
v___y_2162_ = v___y_2227_;
v___y_2163_ = v___y_2229_;
v___y_2164_ = v___y_2228_;
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
v___y_2175_ = v___y_2240_;
v___y_2176_ = v___y_2241_;
v___y_2177_ = v___y_2242_;
v___y_2178_ = v___y_2243_;
v___y_2179_ = v___y_2244_;
v_env_2180_ = v_env_2252_;
v_messages_2181_ = v_messages_2253_;
v_scopes_2182_ = v_scopes_2254_;
v_infoState_2183_ = v_infoState_2255_;
v_traceState_2184_ = v_traceState_2256_;
v_snapshotTasks_2185_ = v_snapshotTasks_2257_;
v___y_2186_ = v___y_2245_;
v___y_2187_ = v___y_2246_;
v___y_2188_ = v___y_2247_;
v___y_2189_ = v___y_2248_;
v___y_2190_ = v___y_2249_;
v___y_2191_ = v___y_2250_;
v_reportedCmdState_2192_ = v_reportedCmdState_2251_;
goto v___jp_2161_;
}
v___jp_2259_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___f_2290_; uint8_t v___x_2291_; 
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___y_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2125_);
lean_inc_ref(v___y_2279_);
lean_inc_n(v_pos_2118_, 2);
lean_inc_ref(v_cmds_2105_);
lean_inc(v_fst_2106_);
v___x_2287_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2106_, v_cmds_2105_, v_cmdState_2119_, v_pos_2118_, v___x_2286_, v___y_2279_, v_a_2109_);
v___x_2288_ = lean_box(v_val_2108_);
v___x_2289_ = lean_box(v___x_2112_);
lean_inc_ref(v_a_2109_);
lean_inc(v___y_2260_);
lean_inc_ref(v___x_2114_);
lean_inc_ref(v___x_2287_);
lean_inc_ref(v___y_2263_);
lean_inc_ref(v___y_2264_);
v___f_2290_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2290_, 0, v___y_2264_);
lean_closure_set(v___f_2290_, 1, v___y_2263_);
lean_closure_set(v___f_2290_, 2, v___x_2288_);
lean_closure_set(v___f_2290_, 3, v___x_2127_);
lean_closure_set(v___f_2290_, 4, v___x_2287_);
lean_closure_set(v___f_2290_, 5, v___x_2114_);
lean_closure_set(v___f_2290_, 6, v___y_2260_);
lean_closure_set(v___f_2290_, 7, v___x_2289_);
lean_closure_set(v___f_2290_, 8, v_a_2109_);
lean_closure_set(v___f_2290_, 9, v_pos_2118_);
lean_closure_set(v___f_2290_, 10, v___x_2120_);
v___x_2291_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2121_, v___x_2258_);
if (v___x_2291_ == 0)
{
lean_dec(v___y_2281_);
lean_inc_ref(v___x_2287_);
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2262_;
v___y_2229_ = v___y_2261_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2268_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2270_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2272_;
v___y_2240_ = v___y_2274_;
v___y_2241_ = v___y_2276_;
v___y_2242_ = v___y_2278_;
v___y_2243_ = v___y_2277_;
v___y_2244_ = v___x_2287_;
v___y_2245_ = v___y_2279_;
v___y_2246_ = v___y_2280_;
v___y_2247_ = v___y_2283_;
v___y_2248_ = v___y_2282_;
v___y_2249_ = v___y_2284_;
v___y_2250_ = v___f_2290_;
v_reportedCmdState_2251_ = v___x_2287_;
goto v___jp_2226_;
}
else
{
uint8_t v___x_2292_; 
lean_inc(v_fst_2106_);
v___x_2292_ = l_Lean_Parser_isTerminalCommand(v_fst_2106_);
if (v___x_2292_ == 0)
{
if (v___x_2291_ == 0)
{
lean_dec(v___y_2281_);
lean_inc_ref(v___x_2287_);
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2262_;
v___y_2229_ = v___y_2261_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2268_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2270_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2272_;
v___y_2240_ = v___y_2274_;
v___y_2241_ = v___y_2276_;
v___y_2242_ = v___y_2278_;
v___y_2243_ = v___y_2277_;
v___y_2244_ = v___x_2287_;
v___y_2245_ = v___y_2279_;
v___y_2246_ = v___y_2280_;
v___y_2247_ = v___y_2283_;
v___y_2248_ = v___y_2282_;
v___y_2249_ = v___y_2284_;
v___y_2250_ = v___f_2290_;
v_reportedCmdState_2251_ = v___x_2287_;
goto v___jp_2226_;
}
else
{
lean_object* v_env_2293_; lean_object* v_messages_2294_; lean_object* v_scopes_2295_; lean_object* v_infoState_2296_; lean_object* v_traceState_2297_; lean_object* v_snapshotTasks_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_env_2293_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_ref_n(v_env_2293_, 2);
v_messages_2294_ = lean_ctor_get(v___x_2287_, 1);
lean_inc_ref(v_messages_2294_);
v_scopes_2295_ = lean_ctor_get(v___x_2287_, 2);
lean_inc(v_scopes_2295_);
v_infoState_2296_ = lean_ctor_get(v___x_2287_, 8);
lean_inc_ref(v_infoState_2296_);
v_traceState_2297_ = lean_ctor_get(v___x_2287_, 9);
lean_inc_ref(v_traceState_2297_);
v_snapshotTasks_2298_ = lean_ctor_get(v___x_2287_, 10);
lean_inc_ref(v_snapshotTasks_2298_);
v___x_2299_ = lean_mk_empty_array_with_capacity(v___y_2281_);
lean_dec(v___y_2281_);
lean_inc_ref(v___x_2299_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_inc_n(v___y_2283_, 3);
v___x_2301_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2299_);
lean_ctor_set(v___x_2301_, 2, v___y_2283_);
lean_ctor_set(v___x_2301_, 3, v___y_2283_);
lean_ctor_set_usize(v___x_2301_, 4, v___y_2273_);
v___x_2302_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2301_, 2);
v___x_2303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2301_);
lean_ctor_set(v___x_2303_, 2, v___x_2302_);
v___x_2304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2305_ = l_Lean_Options_empty;
v___x_2306_ = lean_box(0);
v___x_2307_ = lean_mk_empty_array_with_capacity(v___y_2283_);
lean_inc_ref_n(v___x_2307_, 3);
lean_inc_n(v___x_2111_, 2);
v___x_2308_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2308_, 0, v___x_2304_);
lean_ctor_set(v___x_2308_, 1, v___x_2305_);
lean_ctor_set(v___x_2308_, 2, v___x_2111_);
lean_ctor_set(v___x_2308_, 3, v___x_2306_);
lean_ctor_set(v___x_2308_, 4, v___x_2306_);
lean_ctor_set(v___x_2308_, 5, v___x_2307_);
lean_ctor_set(v___x_2308_, 6, v___x_2307_);
lean_ctor_set(v___x_2308_, 7, v___x_2306_);
lean_ctor_set(v___x_2308_, 8, v___x_2306_);
lean_ctor_set(v___x_2308_, 9, v___x_2306_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*10, v_val_2108_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*10 + 1, v_val_2108_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*10 + 2, v_val_2108_);
v___x_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___x_2306_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2311_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2312_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2111_);
v___x_2313_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2314_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
lean_ctor_set(v___x_2314_, 2, v___x_2301_);
lean_ctor_set_uint8(v___x_2314_, sizeof(void*)*3, v___x_2112_);
v___x_2315_ = lean_box(0);
lean_inc_ref(v___y_2275_);
v___x_2316_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_2316_, 0, v_env_2293_);
lean_ctor_set(v___x_2316_, 1, v___x_2303_);
lean_ctor_set(v___x_2316_, 2, v___x_2309_);
lean_ctor_set(v___x_2316_, 3, v___x_2302_);
lean_ctor_set(v___x_2316_, 4, v___x_2310_);
lean_ctor_set(v___x_2316_, 5, v___y_2283_);
lean_ctor_set(v___x_2316_, 6, v___x_2311_);
lean_ctor_set(v___x_2316_, 7, v___x_2312_);
lean_ctor_set(v___x_2316_, 8, v___x_2314_);
lean_ctor_set(v___x_2316_, 9, v___y_2275_);
lean_ctor_set(v___x_2316_, 10, v___x_2307_);
lean_ctor_set(v___x_2316_, 11, v___x_2315_);
lean_ctor_set(v___x_2316_, 12, v___x_2307_);
v___y_2162_ = v___y_2260_;
v___y_2163_ = v___y_2261_;
v___y_2164_ = v___y_2262_;
v___y_2165_ = v___y_2263_;
v___y_2166_ = v___y_2264_;
v___y_2167_ = v___y_2265_;
v___y_2168_ = v___y_2266_;
v___y_2169_ = v___y_2267_;
v___y_2170_ = v___y_2268_;
v___y_2171_ = v___y_2269_;
v___y_2172_ = v___y_2270_;
v___y_2173_ = v___y_2271_;
v___y_2174_ = v___y_2272_;
v___y_2175_ = v___y_2274_;
v___y_2176_ = v___y_2276_;
v___y_2177_ = v___y_2278_;
v___y_2178_ = v___y_2277_;
v___y_2179_ = v___x_2287_;
v_env_2180_ = v_env_2293_;
v_messages_2181_ = v_messages_2294_;
v_scopes_2182_ = v_scopes_2295_;
v_infoState_2183_ = v_infoState_2296_;
v_traceState_2184_ = v_traceState_2297_;
v_snapshotTasks_2185_ = v_snapshotTasks_2298_;
v___y_2186_ = v___y_2279_;
v___y_2187_ = v___y_2280_;
v___y_2188_ = v___y_2283_;
v___y_2189_ = v___y_2282_;
v___y_2190_ = v___y_2284_;
v___y_2191_ = v___f_2290_;
v_reportedCmdState_2192_ = v___x_2316_;
goto v___jp_2161_;
}
}
else
{
lean_dec(v___y_2281_);
lean_inc_ref(v___x_2287_);
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2262_;
v___y_2229_ = v___y_2261_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2268_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2270_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2272_;
v___y_2240_ = v___y_2274_;
v___y_2241_ = v___y_2276_;
v___y_2242_ = v___y_2278_;
v___y_2243_ = v___y_2277_;
v___y_2244_ = v___x_2287_;
v___y_2245_ = v___y_2279_;
v___y_2246_ = v___y_2280_;
v___y_2247_ = v___y_2283_;
v___y_2248_ = v___y_2282_;
v___y_2249_ = v___y_2284_;
v___y_2250_ = v___f_2290_;
v_reportedCmdState_2251_ = v___x_2287_;
goto v___jp_2226_;
}
}
}
v___jp_2317_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2323_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2110_);
v___x_2324_ = l_IO_CancelToken_new();
v___x_2325_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2111_);
v___x_2326_ = l_Lean_Name_str___override(v___x_2111_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2328_ = l_Lean_Name_str___override(v___x_2326_, v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2330_ = l_Lean_Name_str___override(v___x_2328_, v___x_2329_);
v___x_2331_ = l_Lean_Name_str___override(v___x_2330_, v___x_2327_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v___x_2333_ = l_Lean_Name_num___override(v___x_2331_, v___x_2332_);
v___x_2334_ = l_Lean_Name_str___override(v___x_2333_, v___x_2327_);
v___x_2335_ = l_Lean_Name_str___override(v___x_2334_, v___x_2329_);
v___x_2336_ = l_Lean_Name_str___override(v___x_2335_, v___x_2327_);
v___x_2337_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2338_ = l_Lean_Name_str___override(v___x_2336_, v___x_2337_);
v___x_2339_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2340_ = l_Lean_Name_str___override(v___x_2338_, v___x_2339_);
v___x_2341_ = l_Lean_Name_toString(v___x_2340_, v___x_2112_);
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_unsigned_to_nat(32u);
v___x_2344_ = lean_mk_empty_array_with_capacity(v___x_2343_);
lean_dec_ref(v___x_2344_);
v___x_2345_ = ((size_t)5ULL);
v___x_2346_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2341_, 2);
v___x_2347_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2341_);
lean_ctor_set(v___x_2347_, 1, v___x_2323_);
lean_ctor_set(v___x_2347_, 2, v___x_2342_);
lean_ctor_set(v___x_2347_, 3, v___x_2346_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*4, v_val_2108_);
v___x_2348_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2349_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2349_, 0, v___x_2341_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
lean_ctor_set(v___x_2349_, 2, v___x_2342_);
lean_ctor_set(v___x_2349_, 3, v___x_2346_);
lean_ctor_set_uint8(v___x_2349_, sizeof(void*)*4, v_val_2108_);
lean_inc(v___y_2321_);
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2321_);
v___x_2351_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2350_);
lean_inc_ref(v___x_2324_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2324_);
v___x_2353_ = l_IO_Promise_result_x21___redArg(v___x_2125_);
lean_inc_ref(v___x_2353_);
lean_inc(v___x_2351_);
lean_inc_ref_n(v___x_2350_, 3);
v___x_2354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2350_);
lean_ctor_set(v___x_2354_, 1, v___x_2351_);
lean_ctor_set(v___x_2354_, 2, v___x_2352_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
v___x_2355_ = l_IO_Promise_result_x21___redArg(v___x_2126_);
lean_inc_ref(v___x_2355_);
lean_inc_n(v___y_2320_, 3);
v___x_2356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2350_);
lean_ctor_set(v___x_2356_, 1, v___y_2320_);
lean_ctor_set(v___x_2356_, 2, v___x_2342_);
lean_ctor_set(v___x_2356_, 3, v___x_2355_);
v___x_2357_ = l_IO_Promise_result_x21___redArg(v___x_2127_);
lean_inc_ref(v___x_2357_);
v___x_2358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2350_);
lean_ctor_set(v___x_2358_, 1, v___y_2320_);
lean_ctor_set(v___x_2358_, 2, v___x_2342_);
lean_ctor_set(v___x_2358_, 3, v___x_2357_);
v___x_2359_ = l_IO_Promise_result_x21___redArg(v___x_2128_);
v___x_2360_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2342_);
lean_ctor_set(v___x_2360_, 1, v___y_2320_);
lean_ctor_set(v___x_2360_, 2, v___x_2342_);
lean_ctor_set(v___x_2360_, 3, v___x_2359_);
lean_inc_ref(v___x_2349_);
v___x_2361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2349_);
lean_ctor_set(v___x_2361_, 1, v___x_2354_);
lean_ctor_set(v___x_2361_, 2, v___x_2356_);
lean_ctor_set(v___x_2361_, 3, v___x_2358_);
lean_ctor_set(v___x_2361_, 4, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2347_);
lean_ctor_set(v___x_2362_, 1, v___y_2321_);
lean_ctor_set(v___x_2362_, 2, v___y_2318_);
lean_ctor_set(v___x_2362_, 3, v___x_2361_);
lean_ctor_set(v___x_2362_, 4, v___y_2322_);
v___x_2363_ = lean_io_promise_resolve(v___x_2362_, v_prom_2113_);
if (lean_obj_tag(v_old_x3f_2122_) == 0)
{
lean_inc_ref(v___x_2341_);
lean_inc_ref(v___x_2349_);
v___y_2260_ = v___x_2332_;
v___y_2261_ = v___x_2349_;
v___y_2262_ = v___x_2345_;
v___y_2263_ = v___x_2346_;
v___y_2264_ = v___x_2341_;
v___y_2265_ = v___x_2342_;
v___y_2266_ = v___x_2343_;
v___y_2267_ = v___x_2342_;
v___y_2268_ = v___x_2357_;
v___y_2269_ = v___x_2355_;
v___y_2270_ = v___x_2342_;
v___y_2271_ = v___y_2320_;
v___y_2272_ = v___x_2342_;
v___y_2273_ = v___x_2345_;
v___y_2274_ = v___x_2342_;
v___y_2275_ = v___x_2346_;
v___y_2276_ = v___x_2353_;
v___y_2277_ = v___x_2349_;
v___y_2278_ = v___x_2341_;
v___y_2279_ = v___x_2324_;
v___y_2280_ = v___y_2319_;
v___y_2281_ = v___x_2343_;
v___y_2282_ = v___x_2350_;
v___y_2283_ = v___x_2332_;
v___y_2284_ = v___x_2351_;
v___y_2285_ = v___x_2342_;
goto v___jp_2259_;
}
else
{
lean_object* v_val_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2375_; 
v_val_2364_ = lean_ctor_get(v_old_x3f_2122_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_old_x3f_2122_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2366_ = v_old_x3f_2122_;
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_val_2364_);
lean_dec(v_old_x3f_2122_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_elabSnap_2368_; lean_object* v_stx_2369_; lean_object* v_elabSnap_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v_elabSnap_2368_ = lean_ctor_get(v_val_2364_, 3);
lean_inc_ref(v_elabSnap_2368_);
v_stx_2369_ = lean_ctor_get(v_val_2364_, 1);
lean_inc(v_stx_2369_);
lean_dec(v_val_2364_);
v_elabSnap_2370_ = lean_ctor_get(v_elabSnap_2368_, 1);
lean_inc_ref(v_elabSnap_2370_);
lean_dec_ref(v_elabSnap_2368_);
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_stx_2369_);
lean_ctor_set(v___x_2371_, 1, v_elabSnap_2370_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2371_);
v___x_2373_ = v___x_2366_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_inc_ref(v___x_2341_);
lean_inc_ref(v___x_2349_);
v___y_2260_ = v___x_2332_;
v___y_2261_ = v___x_2349_;
v___y_2262_ = v___x_2345_;
v___y_2263_ = v___x_2346_;
v___y_2264_ = v___x_2341_;
v___y_2265_ = v___x_2342_;
v___y_2266_ = v___x_2343_;
v___y_2267_ = v___x_2342_;
v___y_2268_ = v___x_2357_;
v___y_2269_ = v___x_2355_;
v___y_2270_ = v___x_2342_;
v___y_2271_ = v___y_2320_;
v___y_2272_ = v___x_2342_;
v___y_2273_ = v___x_2345_;
v___y_2274_ = v___x_2342_;
v___y_2275_ = v___x_2346_;
v___y_2276_ = v___x_2353_;
v___y_2277_ = v___x_2349_;
v___y_2278_ = v___x_2341_;
v___y_2279_ = v___x_2324_;
v___y_2280_ = v___y_2319_;
v___y_2281_ = v___x_2343_;
v___y_2282_ = v___x_2350_;
v___y_2283_ = v___x_2332_;
v___y_2284_ = v___x_2351_;
v___y_2285_ = v___x_2373_;
goto v___jp_2259_;
}
}
}
}
v___jp_2376_:
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2379_);
lean_inc(v_fst_2106_);
v___x_2381_ = l_Lean_Parser_isTerminalCommand(v_fst_2106_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v_toProcessingContext_2383_; lean_object* v_pos_2384_; lean_object* v_endPos_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2382_ = lean_io_promise_new();
v_toProcessingContext_2383_ = lean_ctor_get(v_a_2109_, 0);
v_pos_2384_ = lean_ctor_get(v_fst_2107_, 0);
v_endPos_2385_ = lean_ctor_get(v_toProcessingContext_2383_, 3);
lean_inc(v___x_2382_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2382_);
v___x_2387_ = lean_box(0);
lean_inc(v_endPos_2385_);
lean_inc(v_pos_2384_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_pos_2384_);
lean_ctor_set(v___x_2388_, 1, v_endPos_2385_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
v___x_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2390_, 0, v_parseCancelTk_2123_);
v___x_2391_ = l_IO_Promise_result_x21___redArg(v___x_2382_);
lean_dec(v___x_2382_);
v___x_2392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2387_);
lean_ctor_set(v___x_2392_, 1, v___x_2389_);
lean_ctor_set(v___x_2392_, 2, v___x_2390_);
lean_ctor_set(v___x_2392_, 3, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
v___y_2318_ = v___y_2377_;
v___y_2319_ = v___x_2386_;
v___y_2320_ = v___x_2380_;
v___y_2321_ = v___y_2378_;
v___y_2322_ = v___x_2393_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2394_; 
lean_dec_ref(v_parseCancelTk_2123_);
v___x_2394_ = lean_box(0);
v___y_2318_ = v___y_2377_;
v___y_2319_ = v___x_2394_;
v___y_2320_ = v___x_2380_;
v___y_2321_ = v___y_2378_;
v___y_2322_ = v___x_2394_;
goto v___jp_2317_;
}
}
v___jp_2395_:
{
lean_object* v___x_2398_; 
lean_inc(v_fst_2106_);
v___x_2398_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2106_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_box(0);
v___y_2377_ = v_snd_2397_;
v___y_2378_ = v_fst_2396_;
v___y_2379_ = v___x_2399_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_val_2400_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v___x_2398_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_val_2400_);
lean_dec(v___x_2398_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_inc(v_val_2400_);
v___x_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2404_, 0, v_val_2400_);
lean_ctor_set(v___x_2404_, 1, v_val_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
v___y_2377_ = v_snd_2397_;
v___y_2378_ = v_fst_2396_;
v___y_2379_ = v___x_2406_;
goto v___jp_2376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_cmds_2413_ = _args[0];
lean_object* v_fst_2414_ = _args[1];
lean_object* v_fst_2415_ = _args[2];
lean_object* v_val_2416_ = _args[3];
lean_object* v_a_2417_ = _args[4];
lean_object* v_snd_2418_ = _args[5];
lean_object* v___x_2419_ = _args[6];
lean_object* v___x_2420_ = _args[7];
lean_object* v_prom_2421_ = _args[8];
lean_object* v___x_2422_ = _args[9];
lean_object* v___f_2423_ = _args[10];
lean_object* v___f_2424_ = _args[11];
lean_object* v___f_2425_ = _args[12];
lean_object* v_pos_2426_ = _args[13];
lean_object* v_cmdState_2427_ = _args[14];
lean_object* v___x_2428_ = _args[15];
lean_object* v_opts_2429_ = _args[16];
lean_object* v_old_x3f_2430_ = _args[17];
lean_object* v_parseCancelTk_2431_ = _args[18];
lean_object* v___y_2432_ = _args[19];
_start:
{
uint8_t v_val_36225__boxed_2433_; uint8_t v___x_36228__boxed_2434_; lean_object* v_res_2435_; 
v_val_36225__boxed_2433_ = lean_unbox(v_val_2416_);
v___x_36228__boxed_2434_ = lean_unbox(v___x_2420_);
v_res_2435_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_cmds_2413_, v_fst_2414_, v_fst_2415_, v_val_36225__boxed_2433_, v_a_2417_, v_snd_2418_, v___x_2419_, v___x_36228__boxed_2434_, v_prom_2421_, v___x_2422_, v___f_2423_, v___f_2424_, v___f_2425_, v_pos_2426_, v_cmdState_2427_, v___x_2428_, v_opts_2429_, v_old_x3f_2430_, v_parseCancelTk_2431_);
lean_dec_ref(v_opts_2429_);
lean_dec(v_prom_2421_);
lean_dec_ref(v_a_2417_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2438_, lean_object* v_parserState_2439_, lean_object* v_cmdState_2440_, lean_object* v_prom_2441_, uint8_t v_sync_2442_, lean_object* v_parseCancelTk_2443_, lean_object* v_cmds_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___y_2450_; lean_object* v_toSnapshot_2452_; lean_object* v_stx_2453_; lean_object* v_parserState_2454_; lean_object* v_elabSnap_2455_; lean_object* v_val_2456_; lean_object* v_newParserState_2457_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; uint8_t v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v_fst_2533_; lean_object* v_snd_2534_; lean_object* v___y_2547_; uint8_t v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2583_; uint8_t v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___x_2628_; 
v___f_2488_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2489_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2490_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2491_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2492_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2628_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
if (lean_obj_tag(v_old_x3f_2438_) == 1)
{
lean_object* v_val_2661_; lean_object* v_nextCmdSnap_x3f_2662_; 
v_val_2661_ = lean_ctor_get(v_old_x3f_2438_, 0);
v_nextCmdSnap_x3f_2662_ = lean_ctor_get(v_val_2661_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2662_) == 0)
{
goto v___jp_2629_;
}
else
{
lean_object* v_toSnapshot_2663_; lean_object* v_stx_2664_; lean_object* v_parserState_2665_; lean_object* v_elabSnap_2666_; lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_toSnapshot_2663_ = lean_ctor_get(v_val_2661_, 0);
v_stx_2664_ = lean_ctor_get(v_val_2661_, 1);
v_parserState_2665_ = lean_ctor_get(v_val_2661_, 2);
v_elabSnap_2666_ = lean_ctor_get(v_val_2661_, 3);
v_val_2667_ = lean_ctor_get(v_nextCmdSnap_x3f_2662_, 0);
lean_inc(v_val_2667_);
v___x_2668_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2667_);
if (lean_obj_tag(v___x_2668_) == 1)
{
lean_object* v_val_2669_; lean_object* v_nextCmdSnap_x3f_2670_; 
v_val_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v_nextCmdSnap_x3f_2670_ = lean_ctor_get(v_val_2669_, 4);
lean_inc(v_nextCmdSnap_x3f_2670_);
lean_dec(v_val_2669_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2670_) == 0)
{
goto v___jp_2629_;
}
else
{
lean_object* v_val_2671_; lean_object* v___x_2672_; 
v_val_2671_ = lean_ctor_get(v_nextCmdSnap_x3f_2670_, 0);
lean_inc(v_val_2671_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2670_, 1);
v___x_2672_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2671_);
if (lean_obj_tag(v___x_2672_) == 1)
{
lean_object* v_val_2673_; lean_object* v_parserState_2674_; lean_object* v_pos_2675_; uint8_t v___x_2676_; 
v_val_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_val_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v_parserState_2674_ = lean_ctor_get(v_val_2673_, 2);
lean_inc_ref(v_parserState_2674_);
lean_dec(v_val_2673_);
v_pos_2675_ = lean_ctor_get(v_parserState_2674_, 0);
lean_inc(v_pos_2675_);
lean_dec_ref(v_parserState_2674_);
v___x_2676_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2675_, v_a_2445_);
lean_dec(v_pos_2675_);
if (v___x_2676_ == 0)
{
goto v___jp_2629_;
}
else
{
lean_inc(v_val_2667_);
lean_inc_ref(v_elabSnap_2666_);
lean_inc_ref_n(v_parserState_2665_, 2);
lean_inc(v_stx_2664_);
lean_inc_ref(v_toSnapshot_2663_);
lean_dec_ref_known(v_old_x3f_2438_, 1);
lean_dec_ref(v_parseCancelTk_2443_);
lean_dec_ref(v_cmdState_2440_);
lean_dec_ref(v_parserState_2439_);
v_toSnapshot_2452_ = v_toSnapshot_2663_;
v_stx_2453_ = v_stx_2664_;
v_parserState_2454_ = v_parserState_2665_;
v_elabSnap_2455_ = v_elabSnap_2666_;
v_val_2456_ = v_val_2667_;
v_newParserState_2457_ = v_parserState_2665_;
goto v___jp_2451_;
}
}
else
{
lean_dec(v___x_2672_);
goto v___jp_2629_;
}
}
}
else
{
lean_dec(v___x_2668_);
goto v___jp_2629_;
}
}
}
else
{
goto v___jp_2629_;
}
v___jp_2447_:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_box(0);
return v___x_2448_;
}
v___jp_2449_:
{
goto v___jp_2447_;
}
v___jp_2451_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_resultSnap_2460_; lean_object* v_task_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2484_; 
v___x_2458_ = lean_io_promise_new();
v___x_2459_ = l_IO_CancelToken_new();
v_resultSnap_2460_ = lean_ctor_get(v_elabSnap_2455_, 2);
lean_inc_ref(v_resultSnap_2460_);
v_task_2461_ = lean_ctor_get(v_resultSnap_2460_, 3);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_resultSnap_2460_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; lean_object* v_unused_2486_; lean_object* v_unused_2487_; 
v_unused_2485_ = lean_ctor_get(v_resultSnap_2460_, 2);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_resultSnap_2460_, 1);
lean_dec(v_unused_2486_);
v_unused_2487_ = lean_ctor_get(v_resultSnap_2460_, 0);
lean_dec(v_unused_2487_);
v___x_2463_ = v_resultSnap_2460_;
v_isShared_2464_ = v_isSharedCheck_2484_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_task_2461_);
lean_dec(v_resultSnap_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2484_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v_toProcessingContext_2470_; lean_object* v_pos_2471_; lean_object* v_endPos_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2465_ = lean_box(v_sync_2442_);
lean_inc_ref(v_a_2445_);
lean_inc_ref(v___x_2459_);
lean_inc(v___x_2458_);
lean_inc_ref(v_newParserState_2457_);
lean_inc(v_stx_2453_);
v___f_2466_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2466_, 0, v_val_2456_);
lean_closure_set(v___f_2466_, 1, v_cmds_2444_);
lean_closure_set(v___f_2466_, 2, v_stx_2453_);
lean_closure_set(v___f_2466_, 3, v_newParserState_2457_);
lean_closure_set(v___f_2466_, 4, v___x_2458_);
lean_closure_set(v___f_2466_, 5, v___x_2465_);
lean_closure_set(v___f_2466_, 6, v___x_2459_);
lean_closure_set(v___f_2466_, 7, v_a_2445_);
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = 1;
v___x_2469_ = l_BaseIO_chainTask___redArg(v_task_2461_, v___f_2466_, v___x_2467_, v___x_2468_);
v_toProcessingContext_2470_ = lean_ctor_get(v_a_2445_, 0);
v_pos_2471_ = lean_ctor_get(v_newParserState_2457_, 0);
lean_inc(v_pos_2471_);
lean_dec_ref(v_newParserState_2457_);
v_endPos_2472_ = lean_ctor_get(v_toProcessingContext_2470_, 3);
v___x_2473_ = lean_box(0);
lean_inc(v_endPos_2472_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_pos_2471_);
lean_ctor_set(v___x_2474_, 1, v_endPos_2472_);
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2459_);
v___x_2477_ = l_IO_Promise_result_x21___redArg(v___x_2458_);
lean_dec(v___x_2458_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 3, v___x_2477_);
lean_ctor_set(v___x_2463_, 2, v___x_2476_);
lean_ctor_set(v___x_2463_, 1, v___x_2475_);
lean_ctor_set(v___x_2463_, 0, v___x_2473_);
v___x_2479_ = v___x_2463_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
v___x_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2481_, 0, v_toSnapshot_2452_);
lean_ctor_set(v___x_2481_, 1, v_stx_2453_);
lean_ctor_set(v___x_2481_, 2, v_parserState_2454_);
lean_ctor_set(v___x_2481_, 3, v_elabSnap_2455_);
lean_ctor_set(v___x_2481_, 4, v___x_2480_);
v___x_2482_ = lean_io_promise_resolve(v___x_2481_, v_prom_2441_);
lean_dec(v_prom_2441_);
return v___x_2482_;
}
}
}
v___jp_2493_:
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2511_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2510_);
v___x_2512_ = l_Lean_Parser_isTerminalCommand(v___y_2506_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_io_promise_new();
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
v___x_2515_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2511_, v___y_2494_, v_cmds_2444_, v___y_2503_, v___y_2496_, v___y_2498_, v_a_2445_, v___y_2508_, v___y_2509_, v___y_2507_, v___y_2504_, v___y_2497_, v___y_2505_, v___y_2495_, v___y_2500_, v_prom_2441_, v___x_2491_, v___f_2490_, v___f_2489_, v___f_2488_, v___y_2501_, v_cmdState_2440_, v___x_2492_, v___y_2499_, v___y_2502_, v_old_x3f_2438_, v_parseCancelTk_2443_, v___x_2514_);
lean_dec_ref(v___y_2499_);
lean_dec(v_prom_2441_);
lean_dec(v___y_2505_);
lean_dec(v___y_2494_);
v___y_2450_ = v___x_2515_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_box(0);
v___x_2517_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2511_, v___y_2494_, v_cmds_2444_, v___y_2503_, v___y_2496_, v___y_2498_, v_a_2445_, v___y_2508_, v___y_2509_, v___y_2507_, v___y_2504_, v___y_2497_, v___y_2505_, v___y_2495_, v___y_2500_, v_prom_2441_, v___x_2491_, v___f_2490_, v___f_2489_, v___f_2488_, v___y_2501_, v_cmdState_2440_, v___x_2492_, v___y_2499_, v___y_2502_, v_old_x3f_2438_, v_parseCancelTk_2443_, v___x_2516_);
lean_dec_ref(v___y_2499_);
lean_dec(v_prom_2441_);
lean_dec(v___y_2505_);
lean_dec(v___y_2494_);
v___y_2450_ = v___x_2517_;
goto v___jp_2449_;
}
}
v___jp_2518_:
{
lean_object* v___x_2535_; 
lean_inc(v___y_2532_);
v___x_2535_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2532_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_box(0);
v___y_2494_ = v___y_2519_;
v___y_2495_ = v___y_2520_;
v___y_2496_ = v___y_2521_;
v___y_2497_ = v___y_2522_;
v___y_2498_ = v___y_2523_;
v___y_2499_ = v___y_2524_;
v___y_2500_ = v_snd_2534_;
v___y_2501_ = v___y_2525_;
v___y_2502_ = v___y_2526_;
v___y_2503_ = v___y_2527_;
v___y_2504_ = v_fst_2533_;
v___y_2505_ = v___y_2528_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2529_;
v___y_2508_ = v___y_2530_;
v___y_2509_ = v___y_2531_;
v___y_2510_ = v___x_2536_;
goto v___jp_2493_;
}
else
{
lean_object* v_val_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2545_; 
v_val_2537_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2539_ = v___x_2535_;
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_val_2537_);
lean_dec(v___x_2535_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_inc(v_val_2537_);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v_val_2537_);
lean_ctor_set(v___x_2541_, 1, v_val_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
v___y_2494_ = v___y_2519_;
v___y_2495_ = v___y_2520_;
v___y_2496_ = v___y_2521_;
v___y_2497_ = v___y_2522_;
v___y_2498_ = v___y_2523_;
v___y_2499_ = v___y_2524_;
v___y_2500_ = v_snd_2534_;
v___y_2501_ = v___y_2525_;
v___y_2502_ = v___y_2526_;
v___y_2503_ = v___y_2527_;
v___y_2504_ = v_fst_2533_;
v___y_2505_ = v___y_2528_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2529_;
v___y_2508_ = v___y_2530_;
v___y_2509_ = v___y_2531_;
v___y_2510_ = v___x_2543_;
goto v___jp_2493_;
}
}
}
}
v___jp_2546_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2551_ = l_Lean_Name_str___override(v___y_2549_, v___x_2550_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2553_ = l_Lean_Name_str___override(v___x_2551_, v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2555_ = l_Lean_Name_str___override(v___x_2553_, v___x_2554_);
v___x_2556_ = l_Lean_Name_str___override(v___x_2555_, v___x_2552_);
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = l_Lean_Name_num___override(v___x_2556_, v___x_2557_);
v___x_2559_ = l_Lean_Name_str___override(v___x_2558_, v___x_2552_);
v___x_2560_ = l_Lean_Name_str___override(v___x_2559_, v___x_2554_);
v___x_2561_ = l_Lean_Name_str___override(v___x_2560_, v___x_2552_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2563_ = l_Lean_Name_str___override(v___x_2561_, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2565_ = l_Lean_Name_str___override(v___x_2563_, v___x_2564_);
v___x_2566_ = l_Lean_Name_toString(v___x_2565_, v___y_2548_);
v___x_2567_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2568_ = lean_box(0);
v___x_2569_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2570_ = 0;
v___x_2571_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2571_, 0, v___x_2566_);
lean_ctor_set(v___x_2571_, 1, v___x_2567_);
lean_ctor_set(v___x_2571_, 2, v___x_2568_);
lean_ctor_set(v___x_2571_, 3, v___x_2569_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*4, v___x_2570_);
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
lean_inc_ref_n(v___x_2571_, 3);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2571_);
lean_ctor_set(v___x_2574_, 1, v_cmdState_2440_);
v___x_2575_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2568_, v___x_2574_);
v___x_2576_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2568_, v___x_2571_);
v___x_2577_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4);
v___x_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2571_);
lean_ctor_set(v___x_2578_, 1, v___x_2573_);
lean_ctor_set(v___x_2578_, 2, v___x_2575_);
lean_ctor_set(v___x_2578_, 3, v___x_2576_);
lean_ctor_set(v___x_2578_, 4, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2571_);
lean_ctor_set(v___x_2579_, 1, v___x_2572_);
lean_ctor_set(v___x_2579_, 2, v___y_2547_);
lean_ctor_set(v___x_2579_, 3, v___x_2578_);
lean_ctor_set(v___x_2579_, 4, v___x_2568_);
v___x_2580_ = lean_io_promise_resolve(v___x_2579_, v_prom_2441_);
lean_dec(v_prom_2441_);
v___x_2581_ = lean_box(0);
return v___x_2581_;
}
v___jp_2582_:
{
v___y_2547_ = v___y_2583_;
v___y_2548_ = v___y_2584_;
v___y_2549_ = v___y_2585_;
goto v___jp_2546_;
}
v___jp_2587_:
{
uint8_t v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = l_IO_CancelToken_isSet(v_parseCancelTk_2443_);
v___x_2599_ = 1;
if (v___x_2598_ == 0)
{
lean_dec(v___y_2597_);
if (v_sync_2442_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2600_ = lean_io_promise_new();
v___x_2601_ = lean_io_promise_new();
v___x_2602_ = lean_io_promise_new();
v___x_2603_ = lean_io_promise_new();
v___x_2604_ = l_Lean_internal_cmdlineSnapshots;
v___x_2605_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2596_, v___x_2604_);
lean_dec_ref(v___y_2596_);
if (v___x_2605_ == 0)
{
lean_inc(v___y_2594_);
v___y_2519_ = v___x_2603_;
v___y_2520_ = v___x_2602_;
v___y_2521_ = v___y_2589_;
v___y_2522_ = v___x_2600_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___y_2590_;
v___y_2525_ = v___y_2591_;
v___y_2526_ = v___x_2604_;
v___y_2527_ = v___y_2588_;
v___y_2528_ = v___x_2601_;
v___y_2529_ = v___x_2599_;
v___y_2530_ = v___y_2592_;
v___y_2531_ = v___y_2593_;
v___y_2532_ = v___y_2594_;
v_fst_2533_ = v___y_2594_;
v_snd_2534_ = v___y_2595_;
goto v___jp_2518_;
}
else
{
uint8_t v___x_2606_; 
lean_inc(v___y_2594_);
v___x_2606_ = l_Lean_Parser_isTerminalCommand(v___y_2594_);
if (v___x_2606_ == 0)
{
if (v___x_2605_ == 0)
{
lean_inc(v___y_2594_);
v___y_2519_ = v___x_2603_;
v___y_2520_ = v___x_2602_;
v___y_2521_ = v___y_2589_;
v___y_2522_ = v___x_2600_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___y_2590_;
v___y_2525_ = v___y_2591_;
v___y_2526_ = v___x_2604_;
v___y_2527_ = v___y_2588_;
v___y_2528_ = v___x_2601_;
v___y_2529_ = v___x_2599_;
v___y_2530_ = v___y_2592_;
v___y_2531_ = v___y_2593_;
v___y_2532_ = v___y_2594_;
v_fst_2533_ = v___y_2594_;
v_snd_2534_ = v___y_2595_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec_ref(v___y_2595_);
v___x_2607_ = lean_box(0);
v___x_2608_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2519_ = v___x_2603_;
v___y_2520_ = v___x_2602_;
v___y_2521_ = v___y_2589_;
v___y_2522_ = v___x_2600_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___y_2590_;
v___y_2525_ = v___y_2591_;
v___y_2526_ = v___x_2604_;
v___y_2527_ = v___y_2588_;
v___y_2528_ = v___x_2601_;
v___y_2529_ = v___x_2599_;
v___y_2530_ = v___y_2592_;
v___y_2531_ = v___y_2593_;
v___y_2532_ = v___y_2594_;
v_fst_2533_ = v___x_2607_;
v_snd_2534_ = v___x_2608_;
goto v___jp_2518_;
}
}
else
{
lean_inc(v___y_2594_);
v___y_2519_ = v___x_2603_;
v___y_2520_ = v___x_2602_;
v___y_2521_ = v___y_2589_;
v___y_2522_ = v___x_2600_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___y_2590_;
v___y_2525_ = v___y_2591_;
v___y_2526_ = v___x_2604_;
v___y_2527_ = v___y_2588_;
v___y_2528_ = v___x_2601_;
v___y_2529_ = v___x_2599_;
v___y_2530_ = v___y_2592_;
v___y_2531_ = v___y_2593_;
v___y_2532_ = v___y_2594_;
v_fst_2533_ = v___y_2594_;
v_snd_2534_ = v___y_2595_;
goto v___jp_2518_;
}
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_dec_ref(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
v___x_2609_ = lean_box(v___x_2598_);
v___x_2610_ = lean_box(v___x_2599_);
lean_inc_ref(v_a_2445_);
v___f_2611_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2611_, 0, v_cmds_2444_);
lean_closure_set(v___f_2611_, 1, v___y_2588_);
lean_closure_set(v___f_2611_, 2, v___y_2589_);
lean_closure_set(v___f_2611_, 3, v___x_2609_);
lean_closure_set(v___f_2611_, 4, v_a_2445_);
lean_closure_set(v___f_2611_, 5, v___y_2592_);
lean_closure_set(v___f_2611_, 6, v___y_2593_);
lean_closure_set(v___f_2611_, 7, v___x_2610_);
lean_closure_set(v___f_2611_, 8, v_prom_2441_);
lean_closure_set(v___f_2611_, 9, v___x_2491_);
lean_closure_set(v___f_2611_, 10, v___f_2490_);
lean_closure_set(v___f_2611_, 11, v___f_2489_);
lean_closure_set(v___f_2611_, 12, v___f_2488_);
lean_closure_set(v___f_2611_, 13, v___y_2591_);
lean_closure_set(v___f_2611_, 14, v_cmdState_2440_);
lean_closure_set(v___f_2611_, 15, v___x_2492_);
lean_closure_set(v___f_2611_, 16, v___y_2590_);
lean_closure_set(v___f_2611_, 17, v_old_x3f_2438_);
lean_closure_set(v___f_2611_, 18, v_parseCancelTk_2443_);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_io_as_task(v___f_2611_, v___x_2612_);
lean_dec_ref(v___x_2613_);
goto v___jp_2447_;
}
}
else
{
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v_cmds_2444_);
lean_dec_ref(v_parseCancelTk_2443_);
if (lean_obj_tag(v_old_x3f_2438_) == 1)
{
lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v_children_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v_val_2614_ = lean_ctor_get(v_old_x3f_2438_, 0);
lean_inc(v_val_2614_);
lean_dec_ref_known(v_old_x3f_2438_, 1);
v___x_2615_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2614_);
v_children_2616_ = lean_ctor_get(v___x_2615_, 1);
lean_inc_ref(v_children_2616_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_array_get_size(v_children_2616_);
v___x_2619_ = lean_nat_dec_lt(v___x_2617_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v_children_2616_);
v___y_2547_ = v___y_2595_;
v___y_2548_ = v___x_2599_;
v___y_2549_ = v___y_2597_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_nat_dec_le(v___x_2618_, v___x_2618_);
if (v___x_2621_ == 0)
{
if (v___x_2619_ == 0)
{
lean_dec_ref(v_children_2616_);
v___y_2547_ = v___y_2595_;
v___y_2548_ = v___x_2599_;
v___y_2549_ = v___y_2597_;
goto v___jp_2546_;
}
else
{
size_t v___x_2622_; size_t v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = ((size_t)0ULL);
v___x_2623_ = lean_usize_of_nat(v___x_2618_);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2616_, v___x_2622_, v___x_2623_, v___x_2620_);
lean_dec_ref(v_children_2616_);
v___y_2583_ = v___y_2595_;
v___y_2584_ = v___x_2599_;
v___y_2585_ = v___y_2597_;
v___y_2586_ = v___x_2624_;
goto v___jp_2582_;
}
}
else
{
size_t v___x_2625_; size_t v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = lean_usize_of_nat(v___x_2618_);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2616_, v___x_2625_, v___x_2626_, v___x_2620_);
lean_dec_ref(v_children_2616_);
v___y_2583_ = v___y_2595_;
v___y_2584_ = v___x_2599_;
v___y_2585_ = v___y_2597_;
v___y_2586_ = v___x_2627_;
goto v___jp_2582_;
}
}
}
else
{
lean_dec(v_old_x3f_2438_);
v___y_2547_ = v___y_2595_;
v___y_2548_ = v___x_2599_;
v___y_2549_ = v___y_2597_;
goto v___jp_2546_;
}
}
}
v___jp_2629_:
{
lean_object* v_env_2630_; lean_object* v_scopes_2631_; lean_object* v___x_2632_; lean_object* v_opts_2633_; lean_object* v_currNamespace_2634_; lean_object* v_openDecls_2635_; lean_object* v___x_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_snd_2641_; 
v_env_2630_ = lean_ctor_get(v_cmdState_2440_, 0);
v_scopes_2631_ = lean_ctor_get(v_cmdState_2440_, 2);
v___x_2632_ = l_List_head_x21___redArg(v___x_2491_, v_scopes_2631_);
v_opts_2633_ = lean_ctor_get(v___x_2632_, 1);
lean_inc_ref_n(v_opts_2633_, 2);
v_currNamespace_2634_ = lean_ctor_get(v___x_2632_, 2);
lean_inc(v_currNamespace_2634_);
v_openDecls_2635_ = lean_ctor_get(v___x_2632_, 3);
lean_inc(v_openDecls_2635_);
lean_dec(v___x_2632_);
lean_inc_ref(v_env_2630_);
v___x_2636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2636_, 0, v_env_2630_);
lean_ctor_set(v___x_2636_, 1, v_opts_2633_);
lean_ctor_set(v___x_2636_, 2, v_currNamespace_2634_);
lean_ctor_set(v___x_2636_, 3, v_openDecls_2635_);
lean_inc_ref(v_parserState_2439_);
lean_inc_ref(v_a_2445_);
v___f_2637_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2637_, 0, v_a_2445_);
lean_closure_set(v___f_2637_, 1, v___x_2636_);
lean_closure_set(v___f_2637_, 2, v_parserState_2439_);
v___x_2638_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
v___x_2639_ = lean_box(0);
v___x_2640_ = lean_profileit(v___x_2638_, v_opts_2633_, v___f_2637_, v___x_2639_);
v_snd_2641_ = lean_ctor_get(v___x_2640_, 1);
lean_inc(v_snd_2641_);
if (lean_obj_tag(v_old_x3f_2438_) == 1)
{
lean_object* v_val_2642_; lean_object* v_fst_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v_pos_2646_; lean_object* v_toSnapshot_2647_; lean_object* v_stx_2648_; lean_object* v_parserState_2649_; lean_object* v_elabSnap_2650_; lean_object* v_nextCmdSnap_x3f_2651_; uint8_t v___x_2652_; 
v_val_2642_ = lean_ctor_get(v_old_x3f_2438_, 0);
v_fst_2643_ = lean_ctor_get(v___x_2640_, 0);
lean_inc_n(v_fst_2643_, 2);
lean_dec(v___x_2640_);
v_fst_2644_ = lean_ctor_get(v_snd_2641_, 0);
lean_inc(v_fst_2644_);
v_snd_2645_ = lean_ctor_get(v_snd_2641_, 1);
lean_inc(v_snd_2645_);
lean_dec(v_snd_2641_);
v_pos_2646_ = lean_ctor_get(v_parserState_2439_, 0);
lean_inc(v_pos_2646_);
lean_dec_ref(v_parserState_2439_);
v_toSnapshot_2647_ = lean_ctor_get(v_val_2642_, 0);
v_stx_2648_ = lean_ctor_get(v_val_2642_, 1);
v_parserState_2649_ = lean_ctor_get(v_val_2642_, 2);
v_elabSnap_2650_ = lean_ctor_get(v_val_2642_, 3);
v_nextCmdSnap_x3f_2651_ = lean_ctor_get(v_val_2642_, 4);
lean_inc(v_stx_2648_);
v___x_2652_ = l_Lean_Syntax_eqWithInfo(v_fst_2643_, v_stx_2648_);
if (v___x_2652_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2651_) == 0)
{
lean_inc_ref(v_opts_2633_);
lean_inc(v_fst_2644_);
lean_inc(v_fst_2643_);
v___y_2588_ = v_fst_2643_;
v___y_2589_ = v_fst_2644_;
v___y_2590_ = v_opts_2633_;
v___y_2591_ = v_pos_2646_;
v___y_2592_ = v_snd_2645_;
v___y_2593_ = v___x_2639_;
v___y_2594_ = v_fst_2643_;
v___y_2595_ = v_fst_2644_;
v___y_2596_ = v_opts_2633_;
v___y_2597_ = v___x_2639_;
goto v___jp_2587_;
}
else
{
lean_object* v_val_2653_; lean_object* v___x_2654_; 
v_val_2653_ = lean_ctor_get(v_nextCmdSnap_x3f_2651_, 0);
lean_inc(v_val_2653_);
v___x_2654_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2628_, v_val_2653_);
lean_inc_ref(v_opts_2633_);
lean_inc(v_fst_2644_);
lean_inc(v_fst_2643_);
v___y_2588_ = v_fst_2643_;
v___y_2589_ = v_fst_2644_;
v___y_2590_ = v_opts_2633_;
v___y_2591_ = v_pos_2646_;
v___y_2592_ = v_snd_2645_;
v___y_2593_ = v___x_2639_;
v___y_2594_ = v_fst_2643_;
v___y_2595_ = v_fst_2644_;
v___y_2596_ = v_opts_2633_;
v___y_2597_ = v___x_2639_;
goto v___jp_2587_;
}
}
else
{
lean_inc(v_val_2642_);
lean_dec(v_pos_2646_);
lean_dec(v_snd_2645_);
lean_dec(v_fst_2643_);
lean_dec_ref_known(v_old_x3f_2438_, 1);
lean_dec_ref(v_opts_2633_);
lean_dec_ref(v_parseCancelTk_2443_);
lean_dec_ref(v_cmdState_2440_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2651_) == 1)
{
lean_object* v_val_2655_; 
lean_inc_ref(v_nextCmdSnap_x3f_2651_);
lean_inc_ref(v_elabSnap_2650_);
lean_inc_ref(v_parserState_2649_);
lean_inc(v_stx_2648_);
lean_inc_ref(v_toSnapshot_2647_);
lean_dec(v_val_2642_);
v_val_2655_ = lean_ctor_get(v_nextCmdSnap_x3f_2651_, 0);
lean_inc(v_val_2655_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2651_, 1);
v_toSnapshot_2452_ = v_toSnapshot_2647_;
v_stx_2453_ = v_stx_2648_;
v_parserState_2454_ = v_parserState_2649_;
v_elabSnap_2455_ = v_elabSnap_2650_;
v_val_2456_ = v_val_2655_;
v_newParserState_2457_ = v_fst_2644_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2656_; 
lean_dec(v_fst_2644_);
lean_dec_ref(v_cmds_2444_);
v___x_2656_ = lean_io_promise_resolve(v_val_2642_, v_prom_2441_);
lean_dec(v_prom_2441_);
return v___x_2656_;
}
}
}
else
{
lean_object* v_fst_2657_; lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v_pos_2660_; 
v_fst_2657_ = lean_ctor_get(v___x_2640_, 0);
lean_inc_n(v_fst_2657_, 2);
lean_dec(v___x_2640_);
v_fst_2658_ = lean_ctor_get(v_snd_2641_, 0);
lean_inc_n(v_fst_2658_, 2);
v_snd_2659_ = lean_ctor_get(v_snd_2641_, 1);
lean_inc(v_snd_2659_);
lean_dec(v_snd_2641_);
v_pos_2660_ = lean_ctor_get(v_parserState_2439_, 0);
lean_inc(v_pos_2660_);
lean_dec_ref(v_parserState_2439_);
lean_inc_ref(v_opts_2633_);
v___y_2588_ = v_fst_2657_;
v___y_2589_ = v_fst_2658_;
v___y_2590_ = v_opts_2633_;
v___y_2591_ = v_pos_2660_;
v___y_2592_ = v_snd_2659_;
v___y_2593_ = v___x_2639_;
v___y_2594_ = v_fst_2657_;
v___y_2595_ = v_fst_2658_;
v___y_2596_ = v_opts_2633_;
v___y_2597_ = v___x_2639_;
goto v___jp_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2677_, lean_object* v_cmds_2678_, lean_object* v_stx_2679_, lean_object* v_newParserState_2680_, lean_object* v_val_2681_, uint8_t v_sync_2682_, lean_object* v_val_2683_, lean_object* v_a_2684_, lean_object* v_oldNext_2685_){
_start:
{
lean_object* v_cmdState_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_cmdState_2687_ = lean_ctor_get(v_oldResult_2677_, 1);
lean_inc_ref(v_cmdState_2687_);
lean_dec_ref(v_oldResult_2677_);
v___x_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_oldNext_2685_);
v___x_2689_ = lean_array_push(v_cmds_2678_, v_stx_2679_);
v___x_2690_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2688_, v_newParserState_2680_, v_cmdState_2687_, v_val_2681_, v_sync_2682_, v_val_2683_, v___x_2689_, v_a_2684_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2691_ = _args[0];
lean_object* v_val_2692_ = _args[1];
lean_object* v_cmds_2693_ = _args[2];
lean_object* v_fst_2694_ = _args[3];
lean_object* v_fst_2695_ = _args[4];
lean_object* v_val_2696_ = _args[5];
lean_object* v_a_2697_ = _args[6];
lean_object* v_snd_2698_ = _args[7];
lean_object* v___x_2699_ = _args[8];
lean_object* v___x_2700_ = _args[9];
lean_object* v_fst_2701_ = _args[10];
lean_object* v_val_2702_ = _args[11];
lean_object* v_val_2703_ = _args[12];
lean_object* v_val_2704_ = _args[13];
lean_object* v_snd_2705_ = _args[14];
lean_object* v_prom_2706_ = _args[15];
lean_object* v___x_2707_ = _args[16];
lean_object* v___f_2708_ = _args[17];
lean_object* v___f_2709_ = _args[18];
lean_object* v___f_2710_ = _args[19];
lean_object* v_pos_2711_ = _args[20];
lean_object* v_cmdState_2712_ = _args[21];
lean_object* v___x_2713_ = _args[22];
lean_object* v_opts_2714_ = _args[23];
lean_object* v___x_2715_ = _args[24];
lean_object* v_old_x3f_2716_ = _args[25];
lean_object* v_parseCancelTk_2717_ = _args[26];
lean_object* v_next_x3f_2718_ = _args[27];
lean_object* v___y_2719_ = _args[28];
_start:
{
uint8_t v_val_36007__boxed_2720_; uint8_t v___x_36010__boxed_2721_; lean_object* v_res_2722_; 
v_val_36007__boxed_2720_ = lean_unbox(v_val_2696_);
v___x_36010__boxed_2721_ = lean_unbox(v___x_2700_);
v_res_2722_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2691_, v_val_2692_, v_cmds_2693_, v_fst_2694_, v_fst_2695_, v_val_36007__boxed_2720_, v_a_2697_, v_snd_2698_, v___x_2699_, v___x_36010__boxed_2721_, v_fst_2701_, v_val_2702_, v_val_2703_, v_val_2704_, v_snd_2705_, v_prom_2706_, v___x_2707_, v___f_2708_, v___f_2709_, v___f_2710_, v_pos_2711_, v_cmdState_2712_, v___x_2713_, v_opts_2714_, v___x_2715_, v_old_x3f_2716_, v_parseCancelTk_2717_, v_next_x3f_2718_);
lean_dec_ref(v___x_2715_);
lean_dec_ref(v_opts_2714_);
lean_dec(v_prom_2706_);
lean_dec(v_val_2703_);
lean_dec_ref(v_a_2697_);
lean_dec(v_val_2692_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2723_, lean_object* v_parserState_2724_, lean_object* v_cmdState_2725_, lean_object* v_prom_2726_, lean_object* v_sync_2727_, lean_object* v_parseCancelTk_2728_, lean_object* v_cmds_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
uint8_t v_sync_boxed_2732_; lean_object* v_res_2733_; 
v_sync_boxed_2732_ = lean_unbox(v_sync_2727_);
v_res_2733_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2723_, v_parserState_2724_, v_cmdState_2725_, v_prom_2726_, v_sync_boxed_2732_, v_parseCancelTk_2728_, v_cmds_2729_, v_a_2730_);
lean_dec_ref(v_a_2730_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2734_, size_t v_i_2735_, size_t v_stop_2736_, lean_object* v_b_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2734_, v_i_2735_, v_stop_2736_, v_b_2737_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2741_, lean_object* v_i_2742_, lean_object* v_stop_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
size_t v_i_boxed_2747_; size_t v_stop_boxed_2748_; lean_object* v_res_2749_; 
v_i_boxed_2747_ = lean_unbox_usize(v_i_2742_);
lean_dec(v_i_2742_);
v_stop_boxed_2748_ = lean_unbox_usize(v_stop_2743_);
lean_dec(v_stop_2743_);
v_res_2749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2741_, v_i_boxed_2747_, v_stop_boxed_2748_, v_b_2744_, v___y_2745_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v_as_2741_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2750_, lean_object* v_opt_2751_){
_start:
{
lean_object* v_name_2752_; lean_object* v_map_2753_; lean_object* v___x_2754_; 
v_name_2752_ = lean_ctor_get(v_opt_2751_, 0);
v_map_2753_ = lean_ctor_get(v_opts_2750_, 0);
v___x_2754_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2753_, v_name_2752_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_box(0);
return v___x_2755_;
}
else
{
lean_object* v_val_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2765_; 
v_val_2756_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2758_ = v___x_2754_;
v_isShared_2759_ = v_isSharedCheck_2765_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_val_2756_);
lean_dec(v___x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2765_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
if (lean_obj_tag(v_val_2756_) == 0)
{
lean_object* v_v_2760_; lean_object* v___x_2762_; 
v_v_2760_ = lean_ctor_get(v_val_2756_, 0);
lean_inc_ref(v_v_2760_);
lean_dec_ref_known(v_val_2756_, 1);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_v_2760_);
v___x_2762_ = v___x_2758_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_v_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
else
{
lean_object* v___x_2764_; 
lean_del_object(v___x_2758_);
lean_dec(v_val_2756_);
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2766_, lean_object* v_opt_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2766_, v_opt_2767_);
lean_dec_ref(v_opt_2767_);
lean_dec_ref(v_opts_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2769_, lean_object* v_x_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2769_);
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2773_, 0, v_x_2770_);
lean_ctor_set(v___x_2773_, 1, v___x_2771_);
lean_ctor_set(v___x_2773_, 2, v___x_2772_);
return v___x_2773_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2780_ = l_Lean_Array_toPArray_x27___redArg(v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
if (lean_obj_tag(v_a_2781_) == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = l_List_reverse___redArg(v_a_2782_);
return v___x_2783_;
}
else
{
lean_object* v_head_2784_; lean_object* v_tail_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2798_; 
v_head_2784_ = lean_ctor_get(v_a_2781_, 0);
v_tail_2785_ = lean_ctor_get(v_a_2781_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_a_2781_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2787_ = v_a_2781_;
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_tail_2785_);
lean_inc(v_head_2784_);
lean_dec(v_a_2781_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2789_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v_head_2784_);
v___x_2791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
v___x_2792_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v_a_2782_);
lean_ctor_set(v___x_2787_, 0, v___x_2793_);
v___x_2795_ = v___x_2787_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_a_2782_);
v___x_2795_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
v_a_2781_ = v_tail_2785_;
v_a_2782_ = v___x_2795_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2809_; double v___x_2810_; 
v___x_2809_ = lean_unsigned_to_nat(1000000000u);
v___x_2810_ = lean_float_of_nat(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2818_ = l_Lean_MessageData_ofFormat(v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2819_, lean_object* v_stx_2820_, lean_object* v_origStx_2821_, lean_object* v_toProcessingContext_2822_, lean_object* v___x_2823_, lean_object* v_fileMap_2824_, lean_object* v_parserState_2825_, lean_object* v_a_2826_, lean_object* v___x_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_toProcessingContext_2832_; lean_object* v___x_2833_; 
v_toProcessingContext_2832_ = lean_ctor_get(v___y_2830_, 0);
lean_inc_ref(v_toProcessingContext_2832_);
lean_inc(v_stx_2820_);
v___x_2833_ = lean_apply_3(v_setupImports_2819_, v_stx_2820_, v_toProcessingContext_2832_, lean_box(0));
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_3047_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_3047_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_3047_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
if (lean_obj_tag(v_a_2834_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; 
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2827_);
lean_dec_ref(v_parserState_2825_);
lean_dec_ref(v_fileMap_2824_);
lean_dec(v___x_2823_);
lean_dec_ref(v_toProcessingContext_2822_);
lean_dec(v_origStx_2821_);
lean_dec(v_stx_2820_);
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
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_3046_; 
v_a_2842_ = lean_ctor_get(v_a_2834_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_a_2834_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_2844_ = v_a_2834_;
v_isShared_2845_ = v_isSharedCheck_3046_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v_a_2834_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_3046_;
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
v___x_2855_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2820_);
v___x_2856_ = l_Lean_MessageLog_empty;
v___x_2857_ = 1;
lean_inc(v_stx_2820_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_stx_2820_);
v___x_2859_ = v___x_2844_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_stx_2820_);
v___x_2859_ = v_reuseFailAlloc_3045_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_origStx_2821_);
lean_inc_ref(v___x_2859_);
lean_inc_ref(v_opts_2851_);
v___x_2861_ = l_Lean_Elab_processHeaderCore(v___x_2855_, v_imports_2850_, v_isModule_2849_, v_opts_2851_, v___x_2856_, v_toProcessingContext_2822_, v_trustLevel_2852_, v_plugins_2854_, v___x_2857_, v_mainModuleName_2847_, v_package_x3f_2848_, v_importArts_2853_, v___x_2859_, v___x_2860_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_3036_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_3036_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_3036_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_fst_2866_; lean_object* v_snd_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_3035_; 
v_fst_2866_ = lean_ctor_get(v_a_2862_, 0);
v_snd_2867_ = lean_ctor_get(v_a_2862_, 1);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2869_ = v_a_2862_;
v_isShared_2870_ = v_isSharedCheck_3035_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_snd_2867_);
lean_inc(v_fst_2866_);
lean_dec(v_a_2862_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_3035_;
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
double v___x_2983_; double v___x_2984_; double v___x_2985_; double v___x_2986_; double v___x_2987_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_del_object(v___x_2836_);
lean_dec_ref(v___x_2829_);
v___x_2983_ = lean_float_of_nat(v___x_2846_);
v___x_2984_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2985_ = lean_float_div(v___x_2983_, v___x_2984_);
v___x_2986_ = lean_float_of_nat(v___x_2871_);
v___x_2987_ = lean_float_div(v___x_2986_, v___x_2984_);
v___x_3004_ = l_Lean_trace_profiler_output;
v___x_3005_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2851_, v___x_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = l_Lean_trace_profiler_serve;
v___x_3007_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2851_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2889_ = v___x_3008_;
goto v___jp_2888_;
}
else
{
goto v___jp_2988_;
}
}
else
{
lean_dec_ref_known(v___x_3005_, 1);
goto v___jp_2988_;
}
v___jp_2988_:
{
uint64_t v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_2989_ = 0ULL;
v___x_2990_ = lean_box(0);
v___x_2991_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2992_ = lean_box(0);
v___x_2993_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2994_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2994_, 0, v___x_2991_);
lean_ctor_set(v___x_2994_, 1, v___x_2992_);
lean_ctor_set(v___x_2994_, 2, v___x_2993_);
lean_ctor_set_float(v___x_2994_, sizeof(void*)*3, v___x_2985_);
lean_ctor_set_float(v___x_2994_, sizeof(void*)*3 + 8, v___x_2987_);
lean_ctor_set_uint8(v___x_2994_, sizeof(void*)*3 + 16, v___x_2857_);
v___x_2995_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2996_ = lean_mk_empty_array_with_capacity(v___x_2823_);
v___x_2997_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2995_);
lean_ctor_set(v___x_2997_, 2, v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2990_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_unsigned_to_nat(1u);
v___x_3000_ = lean_mk_empty_array_with_capacity(v___x_2999_);
v___x_3001_ = lean_array_push(v___x_3000_, v___x_2998_);
v___x_3002_ = l_Lean_Array_toPArray_x27___redArg(v___x_3001_);
lean_dec_ref(v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set_uint64(v___x_3003_, sizeof(void*)*1, v___x_2989_);
v_traceState_2889_ = v___x_3003_;
goto v___jp_2888_;
}
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint64_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
lean_dec(v___x_2871_);
lean_del_object(v___x_2869_);
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_del_object(v___x_2864_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_opts_2851_);
lean_dec(v___x_2846_);
lean_dec(v___x_2827_);
lean_dec_ref(v_parserState_2825_);
lean_dec_ref(v_fileMap_2824_);
lean_dec(v_stx_2820_);
v___x_3009_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3010_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3011_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2823_, 2);
v___x_3012_ = l_Lean_Name_num___override(v___x_3011_, v___x_2823_);
v___x_3013_ = l_Lean_Name_str___override(v___x_3012_, v___x_3009_);
v___x_3014_ = l_Lean_Name_str___override(v___x_3013_, v___x_3010_);
v___x_3015_ = l_Lean_Name_str___override(v___x_3014_, v___x_3009_);
v___x_3016_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3017_ = l_Lean_Name_str___override(v___x_3015_, v___x_3016_);
v___x_3018_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3019_ = l_Lean_Name_str___override(v___x_3017_, v___x_3018_);
v___x_3020_ = l_Lean_Name_toString(v___x_3019_, v___x_2857_);
v___x_3021_ = lean_box(0);
v___x_3022_ = 0ULL;
v___x_3023_ = lean_unsigned_to_nat(32u);
v___x_3024_ = lean_mk_empty_array_with_capacity(v___x_3023_);
v___x_3025_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3026_ = ((size_t)5ULL);
v___x_3027_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3024_);
lean_ctor_set(v___x_3027_, 2, v___x_2823_);
lean_ctor_set(v___x_3027_, 3, v___x_2823_);
lean_ctor_set_usize(v___x_3027_, 4, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set_uint64(v___x_3028_, sizeof(void*)*1, v___x_3022_);
v___x_3029_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3029_, 0, v___x_3020_);
lean_ctor_set(v___x_3029_, 1, v___x_2872_);
lean_ctor_set(v___x_3029_, 2, v___x_3021_);
lean_ctor_set(v___x_3029_, 3, v___x_3028_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*4, v___x_2873_);
v___x_3030_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2829_);
v___x_3031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
lean_ctor_set(v___x_3031_, 2, v___x_3021_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_3031_);
v___x_3033_ = v___x_2836_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
v___jp_2874_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___y_2880_);
v___x_2882_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2882_, 0, v___y_2875_);
lean_ctor_set(v___x_2882_, 1, v___x_2872_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
lean_ctor_set(v___x_2882_, 3, v___y_2876_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*4, v___x_2873_);
v___x_2883_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2878_, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2884_, 0, v___y_2879_);
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
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_env_2897_; lean_object* v_messages_2898_; lean_object* v_scopes_2899_; lean_object* v_usedQuotCtxts_2900_; lean_object* v_nextMacroScope_2901_; lean_object* v_maxRecDepth_2902_; lean_object* v_ngen_2903_; lean_object* v_auxDeclNGen_2904_; lean_object* v_snapshotTasks_2905_; lean_object* v_prevLinterStates_2906_; lean_object* v_codeQualityEntryTasks_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2972_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2823_, 4);
v___x_2893_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2823_);
lean_ctor_set(v___x_2893_, 1, v___x_2823_);
lean_ctor_set(v___x_2893_, 2, v___x_2823_);
lean_ctor_set(v___x_2893_, 3, v___x_2823_);
lean_ctor_set(v___x_2893_, 4, v___x_2892_);
lean_ctor_set(v___x_2893_, 5, v___x_2892_);
lean_ctor_set(v___x_2893_, 6, v___x_2892_);
lean_ctor_set(v___x_2893_, 7, v___x_2892_);
lean_ctor_set(v___x_2893_, 8, v___x_2892_);
lean_ctor_set(v___x_2893_, 9, v___x_2892_);
lean_ctor_set(v___x_2893_, 10, v___x_2892_);
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
v_prevLinterStates_2906_ = lean_ctor_get(v___x_2896_, 11);
v_codeQualityEntryTasks_2907_ = lean_ctor_get(v___x_2896_, 12);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; lean_object* v_unused_2974_; 
v_unused_2973_ = lean_ctor_get(v___x_2896_, 9);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v___x_2896_, 8);
lean_dec(v_unused_2974_);
v___x_2909_ = v___x_2896_;
v_isShared_2910_ = v_isSharedCheck_2972_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2907_);
lean_inc(v_prevLinterStates_2906_);
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
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2972_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2911_ = lean_box(0);
v___x_2912_ = l_Lean_Options_empty;
v___x_2913_ = lean_box(0);
v___x_2914_ = lean_box(0);
v___x_2915_ = lean_unsigned_to_nat(1u);
v___x_2916_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2917_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2917_, 0, v_fst_2866_);
lean_ctor_set(v___x_2917_, 1, v___x_2911_);
lean_ctor_set(v___x_2917_, 2, v_fileMap_2824_);
lean_ctor_set(v___x_2917_, 3, v___x_2893_);
lean_ctor_set(v___x_2917_, 4, v___x_2912_);
lean_ctor_set(v___x_2917_, 5, v___x_2913_);
lean_ctor_set(v___x_2917_, 6, v___x_2914_);
lean_ctor_set(v___x_2917_, 7, v___x_2916_);
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
v___x_2919_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2820_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v_stx_2820_);
lean_ctor_set(v___x_2869_, 0, v___x_2919_);
v___x_2921_ = v___x_2869_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_stx_2820_);
v___x_2921_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
v___x_2923_ = lean_unsigned_to_nat(2u);
v___x_2924_ = l_Lean_Syntax_getArg(v_stx_2820_, v___x_2923_);
lean_dec(v_stx_2820_);
v___x_2925_ = l_Lean_Syntax_getArgs(v___x_2924_);
lean_dec(v___x_2924_);
v___x_2926_ = lean_array_to_list(v___x_2925_);
v___x_2927_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2926_, v___x_2914_);
v___x_2928_ = l_Lean_List_toPArray_x27___redArg(v___x_2927_);
v___x_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2922_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2918_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_mk_empty_array_with_capacity(v___x_2915_);
v___x_2932_ = lean_array_push(v___x_2931_, v___x_2930_);
v___x_2933_ = l_Lean_Array_toPArray_x27___redArg(v___x_2932_);
lean_dec_ref(v___x_2932_);
lean_inc_ref(v___x_2933_);
v___x_2934_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2934_, 0, v___x_2892_);
lean_ctor_set(v___x_2934_, 1, v___x_2892_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
lean_ctor_set_uint8(v___x_2934_, sizeof(void*)*3, v___x_2857_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 9, v_traceState_2889_);
lean_ctor_set(v___x_2909_, 8, v___x_2934_);
v___x_2936_ = v___x_2909_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_env_2897_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_messages_2898_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_scopes_2899_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_usedQuotCtxts_2900_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_nextMacroScope_2901_);
lean_ctor_set(v_reuseFailAlloc_2970_, 5, v_maxRecDepth_2902_);
lean_ctor_set(v_reuseFailAlloc_2970_, 6, v_ngen_2903_);
lean_ctor_set(v_reuseFailAlloc_2970_, 7, v_auxDeclNGen_2904_);
lean_ctor_set(v_reuseFailAlloc_2970_, 8, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2970_, 9, v_traceState_2889_);
lean_ctor_set(v_reuseFailAlloc_2970_, 10, v_snapshotTasks_2905_);
lean_ctor_set(v_reuseFailAlloc_2970_, 11, v_prevLinterStates_2906_);
lean_ctor_set(v_reuseFailAlloc_2970_, 12, v_codeQualityEntryTasks_2907_);
v___x_2936_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; lean_object* v_size_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint64_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2937_ = lean_mk_empty_array_with_capacity(v___x_2823_);
lean_inc_ref(v___x_2895_);
lean_inc(v___x_2894_);
lean_inc_ref(v___x_2936_);
v___x_2938_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2911_, v_parserState_2825_, v___x_2936_, v___x_2894_, v___x_2857_, v___x_2895_, v___x_2937_, v_a_2826_);
v___x_2939_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2940_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2941_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2823_, 3);
v___x_2942_ = l_Lean_Name_num___override(v___x_2941_, v___x_2823_);
v___x_2943_ = lean_unsigned_to_nat(32u);
v___x_2944_ = lean_mk_empty_array_with_capacity(v___x_2943_);
v___x_2945_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2946_ = ((size_t)5ULL);
v___x_2947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2944_);
lean_ctor_set(v___x_2947_, 2, v___x_2823_);
lean_ctor_set(v___x_2947_, 3, v___x_2823_);
lean_ctor_set_usize(v___x_2947_, 4, v___x_2946_);
v_size_2948_ = lean_ctor_get(v___x_2933_, 2);
lean_inc(v_size_2948_);
v___x_2949_ = l_Lean_Name_str___override(v___x_2942_, v___x_2939_);
v___x_2950_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2827_);
v___x_2951_ = l_Lean_Name_str___override(v___x_2949_, v___x_2940_);
v___x_2952_ = l_Lean_Name_str___override(v___x_2951_, v___x_2939_);
v___x_2953_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2954_ = l_Lean_Name_str___override(v___x_2952_, v___x_2953_);
v___x_2955_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2956_ = l_Lean_Name_str___override(v___x_2954_, v___x_2955_);
v___x_2957_ = l_Lean_Name_toString(v___x_2956_, v___x_2857_);
v___x_2958_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2959_ = 0ULL;
v___x_2960_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2960_, 0, v___x_2947_);
lean_ctor_set_uint64(v___x_2960_, sizeof(void*)*1, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2895_);
v___x_2962_ = l_IO_Promise_result_x21___redArg(v___x_2894_);
lean_dec(v___x_2894_);
v___x_2963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2827_);
lean_ctor_set(v___x_2963_, 1, v___x_2950_);
lean_ctor_set(v___x_2963_, 2, v___x_2961_);
lean_ctor_set(v___x_2963_, 3, v___x_2962_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2936_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_inc_ref(v___x_2960_);
lean_inc_ref(v___x_2957_);
v___x_2966_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2966_, 0, v___x_2957_);
lean_ctor_set(v___x_2966_, 1, v___x_2958_);
lean_ctor_set(v___x_2966_, 2, v___x_2911_);
lean_ctor_set(v___x_2966_, 3, v___x_2960_);
lean_ctor_set_uint8(v___x_2966_, sizeof(void*)*4, v___x_2873_);
v___x_2967_ = lean_nat_dec_lt(v___x_2823_, v_size_2948_);
lean_dec(v_size_2948_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
lean_dec_ref(v___x_2933_);
lean_dec(v___x_2823_);
v___x_2968_ = l_outOfBounds___redArg(v___x_2828_);
v___y_2875_ = v___x_2957_;
v___y_2876_ = v___x_2960_;
v___y_2877_ = v___x_2965_;
v___y_2878_ = v___x_2859_;
v___y_2879_ = v___x_2966_;
v___y_2880_ = v___x_2968_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2828_, v___x_2933_, v___x_2823_);
lean_dec(v___x_2823_);
lean_dec_ref(v___x_2933_);
v___y_2875_ = v___x_2957_;
v___y_2876_ = v___x_2960_;
v___y_2877_ = v___x_2965_;
v___y_2878_ = v___x_2859_;
v___y_2879_ = v___x_2966_;
v___y_2880_ = v___x_2969_;
goto v___jp_2874_;
}
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v_traceState_2889_);
lean_dec_ref(v___x_2872_);
lean_del_object(v___x_2869_);
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_del_object(v___x_2864_);
lean_dec_ref(v___x_2859_);
lean_dec(v___x_2827_);
lean_dec_ref(v_parserState_2825_);
lean_dec_ref(v_fileMap_2824_);
lean_dec(v___x_2823_);
lean_dec(v_stx_2820_);
v_a_2975_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2890_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2890_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_opts_2851_);
lean_dec(v___x_2846_);
lean_del_object(v___x_2836_);
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2827_);
lean_dec_ref(v_parserState_2825_);
lean_dec_ref(v_fileMap_2824_);
lean_dec(v___x_2823_);
lean_dec(v_stx_2820_);
v_a_3037_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2861_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2861_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
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
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2827_);
lean_dec_ref(v_parserState_2825_);
lean_dec_ref(v_fileMap_2824_);
lean_dec(v___x_2823_);
lean_dec_ref(v_toProcessingContext_2822_);
lean_dec(v_origStx_2821_);
lean_dec(v_stx_2820_);
v_a_3048_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2833_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2833_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3056_, lean_object* v_stx_3057_, lean_object* v_origStx_3058_, lean_object* v_toProcessingContext_3059_, lean_object* v___x_3060_, lean_object* v_fileMap_3061_, lean_object* v_parserState_3062_, lean_object* v_a_3063_, lean_object* v___x_3064_, lean_object* v___x_3065_, lean_object* v___x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3056_, v_stx_3057_, v_origStx_3058_, v_toProcessingContext_3059_, v___x_3060_, v_fileMap_3061_, v_parserState_3062_, v_a_3063_, v___x_3064_, v___x_3065_, v___x_3066_, v___y_3067_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v___x_3065_);
lean_dec_ref(v_a_3063_);
return v_res_3069_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___f_3071_; 
v___x_3070_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3071_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3071_, 0, v___x_3070_);
return v___f_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3072_, lean_object* v_stx_3073_, lean_object* v_origStx_3074_, lean_object* v_parserState_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_toProcessingContext_3078_; lean_object* v_fileMap_3079_; lean_object* v_endPos_3080_; lean_object* v___x_3081_; lean_object* v___f_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_toProcessingContext_3078_ = lean_ctor_get(v_a_3076_, 0);
v_fileMap_3079_ = lean_ctor_get(v_toProcessingContext_3078_, 2);
v_endPos_3080_ = lean_ctor_get(v_toProcessingContext_3078_, 3);
v___x_3081_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3082_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3083_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3076_, 2);
lean_inc_ref(v_fileMap_3079_);
lean_inc_ref(v_toProcessingContext_3078_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3086_, 0, v_setupImports_3072_);
lean_closure_set(v___f_3086_, 1, v_stx_3073_);
lean_closure_set(v___f_3086_, 2, v_origStx_3074_);
lean_closure_set(v___f_3086_, 3, v_toProcessingContext_3078_);
lean_closure_set(v___f_3086_, 4, v___x_3085_);
lean_closure_set(v___f_3086_, 5, v_fileMap_3079_);
lean_closure_set(v___f_3086_, 6, v_parserState_3075_);
lean_closure_set(v___f_3086_, 7, v_a_3076_);
lean_closure_set(v___f_3086_, 8, v___x_3084_);
lean_closure_set(v___f_3086_, 9, v___x_3083_);
lean_closure_set(v___f_3086_, 10, v___x_3081_);
lean_inc(v_endPos_3080_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v_endPos_3080_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3089_, 0, lean_box(0));
lean_closure_set(v___x_3089_, 1, v___f_3082_);
lean_closure_set(v___x_3089_, 2, v___f_3086_);
lean_closure_set(v___x_3089_, 3, v_a_3076_);
v___x_3090_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3084_, v___x_3084_, v___x_3088_, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3091_, lean_object* v_stx_3092_, lean_object* v_origStx_3093_, lean_object* v_parserState_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3091_, v_stx_3092_, v_origStx_3093_, v_parserState_3094_, v_a_3095_);
lean_dec_ref(v_a_3095_);
return v_res_3097_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_box(0);
v___x_3101_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3100_);
return v___x_3101_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = 1;
v___x_3107_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3108_ = l_Lean_Name_toString(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3109_ = 0;
v___x_3110_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3111_ = lean_box(0);
v___x_3112_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3113_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3114_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
lean_ctor_set(v___x_3114_, 1, v___x_3112_);
lean_ctor_set(v___x_3114_, 2, v___x_3111_);
lean_ctor_set(v___x_3114_, 3, v___x_3110_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*4, v___x_3109_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3115_, lean_object* v_cmdState_3116_, lean_object* v_a_3117_, lean_object* v_toSnapshot_3118_, lean_object* v_newStx_3119_, lean_object* v_oldCmd_3120_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v_diagnostics_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3150_; 
v___x_3122_ = lean_io_promise_new();
v___x_3123_ = l_IO_CancelToken_new();
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_oldCmd_3120_);
v___x_3125_ = 1;
v___x_3126_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3123_);
lean_inc(v___x_3122_);
lean_inc_ref(v_cmdState_3116_);
v___x_3127_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3124_, v_newParserState_3115_, v_cmdState_3116_, v___x_3122_, v___x_3125_, v___x_3123_, v___x_3126_, v_a_3117_);
v_diagnostics_3128_ = lean_ctor_get(v_toSnapshot_3118_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_toSnapshot_3118_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; 
v_unused_3151_ = lean_ctor_get(v_toSnapshot_3118_, 3);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_toSnapshot_3118_, 2);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_toSnapshot_3118_, 0);
lean_dec(v_unused_3153_);
v___x_3130_ = v_toSnapshot_3118_;
v_isShared_3131_ = v_isSharedCheck_3150_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_diagnostics_3128_);
lean_dec(v_toSnapshot_3118_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3150_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3134_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3135_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3123_);
v___x_3137_ = l_IO_Promise_result_x21___redArg(v___x_3122_);
lean_dec(v___x_3122_);
v___x_3138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3132_);
lean_ctor_set(v___x_3138_, 1, v___x_3133_);
lean_ctor_set(v___x_3138_, 2, v___x_3136_);
lean_ctor_set(v___x_3138_, 3, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_cmdState_3116_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
v___x_3141_ = 0;
v___x_3142_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v_newStx_3119_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 3, v___x_3135_);
lean_ctor_set(v___x_3130_, 2, v___x_3132_);
lean_ctor_set(v___x_3130_, 0, v___x_3134_);
v___x_3145_ = v___x_3130_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_diagnostics_3128_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v___x_3135_);
v___x_3145_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*4, v___x_3141_);
v___x_3146_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3143_, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3142_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
lean_ctor_set(v___x_3147_, 2, v___x_3140_);
v___x_3148_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3132_, v___x_3147_);
return v___x_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3154_, lean_object* v_cmdState_3155_, lean_object* v_a_3156_, lean_object* v_toSnapshot_3157_, lean_object* v_newStx_3158_, lean_object* v_oldCmd_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3154_, v_cmdState_3155_, v_a_3156_, v_toSnapshot_3157_, v_newStx_3158_, v_oldCmd_3159_);
lean_dec_ref(v_a_3156_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3162_, lean_object* v_a_3163_, lean_object* v_newStx_3164_, lean_object* v___x_3165_, lean_object* v_oldProcessed_3166_){
_start:
{
lean_object* v_result_x3f_3168_; 
v_result_x3f_3168_ = lean_ctor_get(v_oldProcessed_3166_, 2);
if (lean_obj_tag(v_result_x3f_3168_) == 1)
{
lean_object* v_val_3169_; lean_object* v_firstCmdSnap_3170_; lean_object* v_toSnapshot_3171_; lean_object* v_cmdState_3172_; lean_object* v_stx_x3f_3173_; lean_object* v___f_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; 
v_val_3169_ = lean_ctor_get(v_result_x3f_3168_, 0);
lean_inc(v_val_3169_);
v_firstCmdSnap_3170_ = lean_ctor_get(v_val_3169_, 1);
lean_inc_ref(v_firstCmdSnap_3170_);
v_toSnapshot_3171_ = lean_ctor_get(v_oldProcessed_3166_, 0);
lean_inc_ref(v_toSnapshot_3171_);
lean_dec_ref(v_oldProcessed_3166_);
v_cmdState_3172_ = lean_ctor_get(v_val_3169_, 0);
lean_inc_ref(v_cmdState_3172_);
lean_dec(v_val_3169_);
v_stx_x3f_3173_ = lean_ctor_get(v_firstCmdSnap_3170_, 0);
lean_inc(v_stx_x3f_3173_);
lean_inc_ref(v_a_3163_);
v___f_3174_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3174_, 0, v_newParserState_3162_);
lean_closure_set(v___f_3174_, 1, v_cmdState_3172_);
lean_closure_set(v___f_3174_, 2, v_a_3163_);
lean_closure_set(v___f_3174_, 3, v_toSnapshot_3171_);
lean_closure_set(v___f_3174_, 4, v_newStx_3164_);
v___x_3175_ = lean_box(0);
v___x_3176_ = 1;
v___x_3177_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3170_, v___f_3174_, v_stx_x3f_3173_, v___x_3165_, v___x_3175_, v___x_3176_);
return v___x_3177_;
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v___x_3165_);
lean_dec_ref(v_newParserState_3162_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_newStx_3164_);
v___x_3179_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3178_, v_oldProcessed_3166_);
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3180_, lean_object* v_a_3181_, lean_object* v_newStx_3182_, lean_object* v___x_3183_, lean_object* v_oldProcessed_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3180_, v_a_3181_, v_newStx_3182_, v___x_3183_, v_oldProcessed_3184_);
lean_dec_ref(v_a_3181_);
return v_res_3186_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3187_ = 0;
v___x_3188_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3189_ = lean_box(0);
v___x_3190_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3191_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3192_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___x_3190_);
lean_ctor_set(v___x_3192_, 2, v___x_3189_);
lean_ctor_set(v___x_3192_, 3, v___x_3188_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*4, v___x_3187_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3193_, lean_object* v_a_3194_, lean_object* v_old_3195_, lean_object* v_newStx_3196_, lean_object* v_newParserState_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_result_x3f_3200_; 
v_result_x3f_3200_ = lean_ctor_get(v_old_3195_, 4);
lean_inc(v_result_x3f_3200_);
if (lean_obj_tag(v_result_x3f_3200_) == 1)
{
lean_object* v_val_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3255_; 
v_val_3201_ = lean_ctor_get(v_result_x3f_3200_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_result_x3f_3200_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3203_ = v_result_x3f_3200_;
v_isShared_3204_ = v_isSharedCheck_3255_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_val_3201_);
lean_dec(v_result_x3f_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3255_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_processedSnap_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3253_; 
v_processedSnap_3205_ = lean_ctor_get(v_val_3201_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_val_3201_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v_val_3201_, 0);
lean_dec(v_unused_3254_);
v___x_3207_ = v_val_3201_;
v_isShared_3208_ = v_isSharedCheck_3253_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_processedSnap_3205_);
lean_dec(v_val_3201_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3253_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_toSnapshot_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3248_; 
v_toSnapshot_3209_ = lean_ctor_get(v_old_3195_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_old_3195_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; lean_object* v_unused_3250_; lean_object* v_unused_3251_; lean_object* v_unused_3252_; 
v_unused_3249_ = lean_ctor_get(v_old_3195_, 4);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_old_3195_, 3);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v_old_3195_, 2);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v_old_3195_, 1);
lean_dec(v_unused_3252_);
v___x_3211_ = v_old_3195_;
v_isShared_3212_ = v_isSharedCheck_3248_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_toSnapshot_3209_);
lean_dec(v_old_3195_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3248_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_pos_3213_; lean_object* v_endPos_3214_; lean_object* v_stx_x3f_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; lean_object* v___x_3221_; lean_object* v_diagnostics_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3244_; 
v_pos_3213_ = lean_ctor_get(v_newParserState_3197_, 0);
v_endPos_3214_ = lean_ctor_get(v_toProcessingContext_3193_, 3);
v_stx_x3f_3215_ = lean_ctor_get(v_processedSnap_3205_, 0);
lean_inc(v_stx_x3f_3215_);
lean_inc(v_endPos_3214_);
lean_inc(v_pos_3213_);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v_pos_3213_);
lean_ctor_set(v___x_3216_, 1, v_endPos_3214_);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_inc_ref(v___x_3217_);
lean_inc(v_newStx_3196_);
lean_inc_ref(v_a_3194_);
lean_inc_ref(v_newParserState_3197_);
v___f_3218_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3218_, 0, v_newParserState_3197_);
lean_closure_set(v___f_3218_, 1, v_a_3194_);
lean_closure_set(v___f_3218_, 2, v_newStx_3196_);
lean_closure_set(v___f_3218_, 3, v___x_3217_);
v___x_3219_ = lean_box(0);
v___x_3220_ = 1;
v___x_3221_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3205_, v___f_3218_, v_stx_x3f_3215_, v___x_3217_, v___x_3219_, v___x_3220_);
v_diagnostics_3222_ = lean_ctor_get(v_toSnapshot_3209_, 1);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_toSnapshot_3209_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; lean_object* v_unused_3246_; lean_object* v_unused_3247_; 
v_unused_3245_ = lean_ctor_get(v_toSnapshot_3209_, 3);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_toSnapshot_3209_, 2);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_toSnapshot_3209_, 0);
lean_dec(v_unused_3247_);
v___x_3224_ = v_toSnapshot_3209_;
v_isShared_3225_ = v_isSharedCheck_3244_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_diagnostics_3222_);
lean_dec(v_toSnapshot_3209_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3244_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3226_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3227_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3221_);
lean_ctor_set(v___x_3207_, 0, v_newParserState_3197_);
v___x_3229_ = v___x_3207_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_newParserState_3197_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___x_3221_);
v___x_3229_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3231_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3229_);
v___x_3231_ = v___x_3203_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3232_ = 0;
v___x_3233_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3196_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_newStx_3196_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 3, v___x_3227_);
lean_ctor_set(v___x_3224_, 2, v___x_3219_);
lean_ctor_set(v___x_3224_, 0, v___x_3226_);
v___x_3236_ = v___x_3224_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_diagnostics_3222_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3241_, 3, v___x_3227_);
v___x_3236_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*4, v___x_3232_);
v___x_3237_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3234_, v___x_3236_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 4, v___x_3231_);
lean_ctor_set(v___x_3211_, 3, v_newStx_3196_);
lean_ctor_set(v___x_3211_, 2, v_toProcessingContext_3193_);
lean_ctor_set(v___x_3211_, 1, v___x_3237_);
lean_ctor_set(v___x_3211_, 0, v___x_3233_);
v___x_3239_ = v___x_3211_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_toProcessingContext_3193_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v_newStx_3196_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v___x_3231_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
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
lean_dec(v_result_x3f_3200_);
lean_dec_ref(v_newParserState_3197_);
lean_dec(v_newStx_3196_);
lean_dec_ref(v_toProcessingContext_3193_);
return v_old_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3256_, lean_object* v_a_3257_, lean_object* v_old_3258_, lean_object* v_newStx_3259_, lean_object* v_newParserState_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3256_, v_a_3257_, v_old_3258_, v_newStx_3259_, v_newParserState_3260_, v___y_3261_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v_a_3257_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3264_, lean_object* v_setupImports_3265_, lean_object* v_old_x3f_3266_, lean_object* v___x_3267_, lean_object* v___f_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; 
lean_inc_ref(v_toProcessingContext_3264_);
v___x_3271_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3264_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3340_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3340_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3340_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_snd_3276_; lean_object* v_fst_3277_; lean_object* v_fst_3278_; lean_object* v_snd_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3339_; 
v_snd_3276_ = lean_ctor_get(v_a_3272_, 1);
lean_inc(v_snd_3276_);
v_fst_3277_ = lean_ctor_get(v_a_3272_, 0);
lean_inc(v_fst_3277_);
lean_dec(v_a_3272_);
v_fst_3278_ = lean_ctor_get(v_snd_3276_, 0);
v_snd_3279_ = lean_ctor_get(v_snd_3276_, 1);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_snd_3276_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3281_ = v_snd_3276_;
v_isShared_3282_ = v_isSharedCheck_3339_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_snd_3279_);
lean_inc(v_fst_3278_);
lean_dec(v_snd_3276_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3339_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
uint8_t v___x_3283_; 
v___x_3283_ = l_Lean_MessageLog_hasErrors(v_snd_3279_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___y_3286_; 
lean_inc(v_fst_3277_);
v___x_3284_ = l_Lean_Syntax_unsetTrailing(v_fst_3277_);
if (lean_obj_tag(v_old_x3f_3266_) == 1)
{
lean_object* v_val_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3322_; 
v_val_3307_ = lean_ctor_get(v_old_x3f_3266_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_old_x3f_3266_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3309_ = v_old_x3f_3266_;
v_isShared_3310_ = v_isSharedCheck_3322_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_val_3307_);
lean_dec(v_old_x3f_3266_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3322_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v_stx_3311_; lean_object* v_result_x3f_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_stx_3311_ = lean_ctor_get(v_val_3307_, 3);
v_result_x3f_3312_ = lean_ctor_get(v_val_3307_, 4);
lean_inc(v_stx_3311_);
v___x_3313_ = l_Lean_Syntax_unsetTrailing(v_stx_3311_);
lean_inc(v___x_3284_);
v___x_3314_ = l_Lean_Syntax_eqWithInfo(v___x_3284_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_inc(v_result_x3f_3312_);
lean_del_object(v___x_3309_);
lean_dec(v_val_3307_);
lean_dec_ref(v___f_3268_);
if (lean_obj_tag(v_result_x3f_3312_) == 0)
{
lean_dec_ref(v___x_3267_);
v___y_3286_ = v___y_3269_;
goto v___jp_3285_;
}
else
{
lean_object* v_val_3315_; lean_object* v_processedSnap_3316_; lean_object* v___x_3317_; 
v_val_3315_ = lean_ctor_get(v_result_x3f_3312_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v_result_x3f_3312_, 1);
v_processedSnap_3316_ = lean_ctor_get(v_val_3315_, 1);
lean_inc_ref(v_processedSnap_3316_);
lean_dec(v_val_3315_);
v___x_3317_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3267_, v_processedSnap_3316_);
v___y_3286_ = v___y_3269_;
goto v___jp_3285_;
}
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3320_; 
lean_dec(v___x_3284_);
lean_del_object(v___x_3281_);
lean_dec(v_snd_3279_);
lean_del_object(v___x_3274_);
lean_dec_ref(v___x_3267_);
lean_dec_ref(v_setupImports_3265_);
lean_dec_ref(v_toProcessingContext_3264_);
lean_inc_ref(v___y_3269_);
v___x_3318_ = lean_apply_5(v___f_3268_, v_val_3307_, v_fst_3277_, v_fst_3278_, v___y_3269_, lean_box(0));
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3318_);
v___x_3320_ = v___x_3309_;
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
lean_dec_ref(v___f_3268_);
lean_dec_ref(v___x_3267_);
lean_dec(v_old_x3f_3266_);
v___y_3286_ = v___y_3269_;
goto v___jp_3285_;
}
v___jp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3287_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3279_);
lean_inc(v_fst_3278_);
lean_inc(v_fst_3277_);
v___x_3288_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3265_, v___x_3284_, v_fst_3277_, v_fst_3278_, v___y_3286_);
v___x_3289_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3290_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_unsigned_to_nat(32u);
v___x_3293_ = lean_mk_empty_array_with_capacity(v___x_3292_);
lean_dec_ref(v___x_3293_);
v___x_3294_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v___x_3288_);
v___x_3296_ = v___x_3281_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_fst_3278_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___x_3288_);
v___x_3296_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3298_, 0, v___x_3289_);
lean_ctor_set(v___x_3298_, 1, v___x_3290_);
lean_ctor_set(v___x_3298_, 2, v___x_3291_);
lean_ctor_set(v___x_3298_, 3, v___x_3294_);
lean_ctor_set_uint8(v___x_3298_, sizeof(void*)*4, v___x_3283_);
lean_inc(v_fst_3277_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_fst_3277_);
v___x_3300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3300_, 0, v___x_3289_);
lean_ctor_set(v___x_3300_, 1, v___x_3287_);
lean_ctor_set(v___x_3300_, 2, v___x_3291_);
lean_ctor_set(v___x_3300_, 3, v___x_3294_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*4, v___x_3283_);
v___x_3301_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3299_, v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3298_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
lean_ctor_set(v___x_3302_, 2, v_toProcessingContext_3264_);
lean_ctor_set(v___x_3302_, 3, v_fst_3277_);
lean_ctor_set(v___x_3302_, 4, v___x_3297_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3302_);
v___x_3304_ = v___x_3274_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
lean_del_object(v___x_3281_);
lean_dec(v_fst_3278_);
lean_dec_ref(v___f_3268_);
lean_dec_ref(v___x_3267_);
lean_dec(v_old_x3f_3266_);
lean_dec_ref(v_setupImports_3265_);
v___x_3323_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3279_);
v___x_3324_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3325_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_unsigned_to_nat(32u);
v___x_3328_ = lean_mk_empty_array_with_capacity(v___x_3327_);
lean_dec_ref(v___x_3328_);
v___x_3329_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3330_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3330_, 0, v___x_3324_);
lean_ctor_set(v___x_3330_, 1, v___x_3325_);
lean_ctor_set(v___x_3330_, 2, v___x_3326_);
lean_ctor_set(v___x_3330_, 3, v___x_3329_);
lean_ctor_set_uint8(v___x_3330_, sizeof(void*)*4, v___x_3283_);
lean_inc(v_fst_3277_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_fst_3277_);
v___x_3332_ = 0;
v___x_3333_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3333_, 0, v___x_3324_);
lean_ctor_set(v___x_3333_, 1, v___x_3323_);
lean_ctor_set(v___x_3333_, 2, v___x_3326_);
lean_ctor_set(v___x_3333_, 3, v___x_3329_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*4, v___x_3332_);
v___x_3334_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3331_, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3330_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
lean_ctor_set(v___x_3335_, 2, v_toProcessingContext_3264_);
lean_ctor_set(v___x_3335_, 3, v_fst_3277_);
lean_ctor_set(v___x_3335_, 4, v___x_3326_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3335_);
v___x_3337_ = v___x_3274_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v___f_3268_);
lean_dec_ref(v___x_3267_);
lean_dec(v_old_x3f_3266_);
lean_dec_ref(v_setupImports_3265_);
lean_dec_ref(v_toProcessingContext_3264_);
v_a_3341_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3271_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3271_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3349_, lean_object* v_setupImports_3350_, lean_object* v_old_x3f_3351_, lean_object* v___x_3352_, lean_object* v___f_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3349_, v_setupImports_3350_, v_old_x3f_3351_, v___x_3352_, v___f_3353_, v___y_3354_);
lean_dec_ref(v___y_3354_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3357_, lean_object* v_toProcessingContext_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3360_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3357_);
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3363_, 0, v_x_3359_);
lean_ctor_set(v___x_3363_, 1, v___x_3360_);
lean_ctor_set(v___x_3363_, 2, v_toProcessingContext_3358_);
lean_ctor_set(v___x_3363_, 3, v___x_3361_);
lean_ctor_set(v___x_3363_, 4, v___x_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3364_, lean_object* v_old_x3f_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_toProcessingContext_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___f_3371_; lean_object* v___f_3372_; lean_object* v___f_3373_; 
v_toProcessingContext_3368_ = lean_ctor_get(v_a_3366_, 0);
v___x_3369_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3370_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3366_);
lean_inc_ref_n(v_toProcessingContext_3368_, 3);
v___f_3371_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3371_, 0, v_toProcessingContext_3368_);
lean_closure_set(v___f_3371_, 1, v_a_3366_);
lean_inc(v_old_x3f_3365_);
v___f_3372_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3372_, 0, v_toProcessingContext_3368_);
lean_closure_set(v___f_3372_, 1, v_setupImports_3364_);
lean_closure_set(v___f_3372_, 2, v_old_x3f_3365_);
lean_closure_set(v___f_3372_, 3, v___x_3370_);
lean_closure_set(v___f_3372_, 4, v___f_3371_);
v___f_3373_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3373_, 0, v___x_3369_);
lean_closure_set(v___f_3373_, 1, v_toProcessingContext_3368_);
if (lean_obj_tag(v_old_x3f_3365_) == 1)
{
lean_object* v_val_3374_; lean_object* v_result_x3f_3375_; 
v_val_3374_ = lean_ctor_get(v_old_x3f_3365_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v_old_x3f_3365_, 1);
v_result_x3f_3375_ = lean_ctor_get(v_val_3374_, 4);
if (lean_obj_tag(v_result_x3f_3375_) == 1)
{
lean_object* v_stx_3376_; lean_object* v_val_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_stx_3376_ = lean_ctor_get(v_val_3374_, 3);
lean_inc(v_stx_3376_);
v_val_3377_ = lean_ctor_get(v_result_x3f_3375_, 0);
lean_inc(v_val_3374_);
v___x_3378_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3374_);
v___x_3379_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3378_);
if (lean_obj_tag(v___x_3379_) == 1)
{
lean_object* v_val_3380_; 
v_val_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_val_3380_);
lean_dec_ref_known(v___x_3379_, 1);
if (lean_obj_tag(v_val_3380_) == 1)
{
lean_object* v_val_3381_; lean_object* v_firstCmdSnap_3382_; lean_object* v___x_3383_; 
v_val_3381_ = lean_ctor_get(v_val_3380_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v_val_3380_, 1);
v_firstCmdSnap_3382_ = lean_ctor_get(v_val_3381_, 1);
lean_inc_ref(v_firstCmdSnap_3382_);
lean_dec(v_val_3381_);
v___x_3383_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3382_);
if (lean_obj_tag(v___x_3383_) == 1)
{
lean_object* v_val_3384_; lean_object* v_nextCmdSnap_x3f_3385_; 
v_val_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_val_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v_nextCmdSnap_x3f_3385_ = lean_ctor_get(v_val_3384_, 4);
lean_inc(v_nextCmdSnap_x3f_3385_);
lean_dec(v_val_3384_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3385_) == 0)
{
lean_object* v___x_3386_; 
lean_dec(v_stx_3376_);
lean_dec(v_val_3374_);
v___x_3386_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3386_;
}
else
{
lean_object* v_val_3387_; lean_object* v___x_3388_; 
v_val_3387_ = lean_ctor_get(v_nextCmdSnap_x3f_3385_, 0);
lean_inc(v_val_3387_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3385_, 1);
v___x_3388_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3387_);
if (lean_obj_tag(v___x_3388_) == 1)
{
lean_object* v_val_3389_; lean_object* v_parserState_3390_; lean_object* v_pos_3391_; uint8_t v___x_3392_; 
v_val_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v_parserState_3390_ = lean_ctor_get(v_val_3389_, 2);
lean_inc_ref(v_parserState_3390_);
lean_dec(v_val_3389_);
v_pos_3391_ = lean_ctor_get(v_parserState_3390_, 0);
lean_inc(v_pos_3391_);
lean_dec_ref(v_parserState_3390_);
v___x_3392_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3391_, v_a_3366_);
lean_dec(v_pos_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; 
lean_dec(v_stx_3376_);
lean_dec(v_val_3374_);
v___x_3393_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3393_;
}
else
{
lean_object* v_parserState_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v___f_3373_);
lean_dec_ref(v___f_3372_);
v_parserState_3394_ = lean_ctor_get(v_val_3377_, 0);
lean_inc_ref(v_parserState_3394_);
lean_inc_ref(v_toProcessingContext_3368_);
v___x_3395_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3368_, v_a_3366_, v_val_3374_, v_stx_3376_, v_parserState_3394_, v_a_3366_);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3396_; 
lean_dec(v___x_3388_);
lean_dec(v_stx_3376_);
lean_dec(v_val_3374_);
v___x_3396_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3396_;
}
}
}
else
{
lean_object* v___x_3397_; 
lean_dec(v___x_3383_);
lean_dec(v_stx_3376_);
lean_dec(v_val_3374_);
v___x_3397_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3397_;
}
}
else
{
lean_object* v___x_3398_; 
lean_dec(v_val_3380_);
lean_dec(v_stx_3376_);
lean_dec(v_val_3374_);
v___x_3398_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3398_;
}
}
else
{
lean_object* v___x_3399_; 
lean_dec(v___x_3379_);
lean_dec(v_stx_3376_);
lean_dec(v_val_3374_);
v___x_3399_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3399_;
}
}
else
{
lean_object* v___x_3400_; 
lean_dec(v_val_3374_);
v___x_3400_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3400_;
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v_old_x3f_3365_);
v___x_3401_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3373_, v___f_3372_, v_a_3366_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3402_, lean_object* v_old_x3f_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3402_, v_old_x3f_3403_, v_a_3404_);
lean_dec_ref(v_a_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3407_, lean_object* v_old_x3f_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v___x_3411_; 
lean_inc(v_old_x3f_3408_);
v___x_3411_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3411_, 0, v_setupImports_3407_);
lean_closure_set(v___x_3411_, 1, v_old_x3f_3408_);
if (lean_obj_tag(v_old_x3f_3408_) == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_box(0);
v___x_3413_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3411_, v___x_3412_, v_a_3409_);
return v___x_3413_;
}
else
{
lean_object* v_val_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3423_; 
v_val_3414_ = lean_ctor_get(v_old_x3f_3408_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_old_x3f_3408_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3416_ = v_old_x3f_3408_;
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_val_3414_);
lean_dec(v_old_x3f_3408_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3423_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_ictx_3418_; lean_object* v___x_3420_; 
v_ictx_3418_ = lean_ctor_get(v_val_3414_, 2);
lean_inc_ref(v_ictx_3418_);
lean_dec(v_val_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_ictx_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_ictx_3418_);
v___x_3420_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3411_, v___x_3420_, v_a_3409_);
return v___x_3421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3424_, lean_object* v_old_x3f_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Language_Lean_process(v_setupImports_3424_, v_old_x3f_3425_, v_a_3426_);
lean_dec_ref(v_a_3426_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3429_, lean_object* v_parserState_3430_, lean_object* v_commandState_3431_, lean_object* v_old_x3f_3432_){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3442_; 
v___x_3434_ = lean_io_promise_new();
v___x_3435_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3432_) == 0)
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_box(0);
v___y_3442_ = v___x_3457_;
goto v___jp_3441_;
}
else
{
lean_object* v_val_3458_; lean_object* v_snd_3459_; lean_object* v___x_3460_; 
v_val_3458_ = lean_ctor_get(v_old_x3f_3432_, 0);
v_snd_3459_ = lean_ctor_get(v_val_3458_, 1);
lean_inc(v_snd_3459_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_snd_3459_);
v___y_3442_ = v___x_3460_;
goto v___jp_3441_;
}
v___jp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3437_, v___y_3438_, v_inputCtx_3429_);
lean_dec(v___x_3439_);
v___x_3440_ = l_IO_Promise_result_x21___redArg(v___x_3434_);
lean_dec(v___x_3434_);
return v___x_3440_;
}
v___jp_3441_:
{
uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3443_ = 1;
v___x_3444_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
v___x_3445_ = lean_box(v___x_3443_);
lean_inc(v___x_3434_);
v___x_3446_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3446_, 0, v___y_3442_);
lean_closure_set(v___x_3446_, 1, v_parserState_3430_);
lean_closure_set(v___x_3446_, 2, v_commandState_3431_);
lean_closure_set(v___x_3446_, 3, v___x_3434_);
lean_closure_set(v___x_3446_, 4, v___x_3445_);
lean_closure_set(v___x_3446_, 5, v___x_3435_);
lean_closure_set(v___x_3446_, 6, v___x_3444_);
if (lean_obj_tag(v_old_x3f_3432_) == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_box(0);
v___y_3437_ = v___x_3446_;
v___y_3438_ = v___x_3447_;
goto v___jp_3436_;
}
else
{
lean_object* v_val_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3456_; 
v_val_3448_ = lean_ctor_get(v_old_x3f_3432_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_old_x3f_3432_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3450_ = v_old_x3f_3432_;
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_val_3448_);
lean_dec(v_old_x3f_3432_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_fst_3452_; lean_object* v___x_3454_; 
v_fst_3452_ = lean_ctor_get(v_val_3448_, 0);
lean_inc(v_fst_3452_);
lean_dec(v_val_3448_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v_fst_3452_);
v___x_3454_ = v___x_3450_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
v___y_3437_ = v___x_3446_;
v___y_3438_ = v___x_3454_;
goto v___jp_3436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3461_, lean_object* v_parserState_3462_, lean_object* v_commandState_3463_, lean_object* v_old_x3f_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3461_, v_parserState_3462_, v_commandState_3463_, v_old_x3f_3464_);
lean_dec_ref(v_inputCtx_3461_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3467_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3468_; 
v_nextCmdSnap_x3f_3468_ = lean_ctor_get(v_snap_3467_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3468_) == 1)
{
lean_object* v_val_3469_; lean_object* v___x_3470_; 
lean_inc_ref(v_nextCmdSnap_x3f_3468_);
lean_dec_ref(v_snap_3467_);
v_val_3469_ = lean_ctor_get(v_nextCmdSnap_x3f_3468_, 0);
lean_inc(v_val_3469_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3468_, 1);
v___x_3470_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3469_);
v_snap_3467_ = v___x_3470_;
goto _start;
}
else
{
lean_object* v_elabSnap_3472_; lean_object* v_resultSnap_3473_; lean_object* v___x_3474_; lean_object* v_cmdState_3475_; lean_object* v___x_3476_; 
v_elabSnap_3472_ = lean_ctor_get(v_snap_3467_, 3);
lean_inc_ref(v_elabSnap_3472_);
lean_dec_ref(v_snap_3467_);
v_resultSnap_3473_ = lean_ctor_get(v_elabSnap_3472_, 2);
lean_inc_ref(v_resultSnap_3473_);
lean_dec_ref(v_elabSnap_3472_);
v___x_3474_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3473_);
v_cmdState_3475_ = lean_ctor_get(v___x_3474_, 1);
lean_inc_ref(v_cmdState_3475_);
lean_dec(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3476_, 0, v_cmdState_3475_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3477_){
_start:
{
lean_object* v_result_x3f_3478_; 
v_result_x3f_3478_ = lean_ctor_get(v_snap_3477_, 4);
lean_inc(v_result_x3f_3478_);
lean_dec_ref(v_snap_3477_);
if (lean_obj_tag(v_result_x3f_3478_) == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_box(0);
return v___x_3479_;
}
else
{
lean_object* v_val_3480_; lean_object* v_processedSnap_3481_; lean_object* v___x_3482_; lean_object* v_result_x3f_3483_; 
v_val_3480_ = lean_ctor_get(v_result_x3f_3478_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_result_x3f_3478_, 1);
v_processedSnap_3481_ = lean_ctor_get(v_val_3480_, 1);
lean_inc_ref(v_processedSnap_3481_);
lean_dec(v_val_3480_);
v___x_3482_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3481_);
v_result_x3f_3483_ = lean_ctor_get(v___x_3482_, 2);
lean_inc(v_result_x3f_3483_);
lean_dec(v___x_3482_);
if (lean_obj_tag(v_result_x3f_3483_) == 0)
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_box(0);
return v___x_3484_;
}
else
{
lean_object* v_val_3485_; lean_object* v_firstCmdSnap_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_val_3485_ = lean_ctor_get(v_result_x3f_3483_, 0);
lean_inc(v_val_3485_);
lean_dec_ref_known(v_result_x3f_3483_, 1);
v_firstCmdSnap_3486_ = lean_ctor_get(v_val_3485_, 1);
lean_inc_ref(v_firstCmdSnap_3486_);
lean_dec(v_val_3485_);
v___x_3487_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3486_);
v___x_3488_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3487_);
return v___x_3488_;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = 1;
v___x_3495_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3496_ = l_Lean_Name_toString(v___x_3495_, v___x_3494_);
return v___x_3496_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3497_ = 0;
v___x_3498_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3499_ = lean_box(0);
v___x_3500_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3501_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3502_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3500_);
lean_ctor_set(v___x_3502_, 2, v___x_3499_);
lean_ctor_set(v___x_3502_, 3, v___x_3498_);
lean_ctor_set_uint8(v___x_3502_, sizeof(void*)*4, v___x_3497_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3504_ = lean_box(0);
v___x_3505_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3504_, v___x_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3506_){
_start:
{
lean_object* v_result_x3f_3507_; 
v_result_x3f_3507_ = lean_ctor_get(v_snap_3506_, 4);
lean_inc(v_result_x3f_3507_);
if (lean_obj_tag(v_result_x3f_3507_) == 1)
{
lean_object* v_val_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3582_; 
v_val_3508_ = lean_ctor_get(v_result_x3f_3507_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_result_x3f_3507_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3510_ = v_result_x3f_3507_;
v_isShared_3511_ = v_isSharedCheck_3582_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_val_3508_);
lean_dec(v_result_x3f_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3582_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_toSnapshot_3512_; lean_object* v_metaSnap_3513_; lean_object* v_ictx_3514_; lean_object* v_stx_3515_; lean_object* v_parserState_3516_; lean_object* v_processedSnap_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3581_; 
v_toSnapshot_3512_ = lean_ctor_get(v_snap_3506_, 0);
v_metaSnap_3513_ = lean_ctor_get(v_snap_3506_, 1);
v_ictx_3514_ = lean_ctor_get(v_snap_3506_, 2);
v_stx_3515_ = lean_ctor_get(v_snap_3506_, 3);
v_parserState_3516_ = lean_ctor_get(v_val_3508_, 0);
v_processedSnap_3517_ = lean_ctor_get(v_val_3508_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_val_3508_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3519_ = v_val_3508_;
v_isShared_3520_ = v_isSharedCheck_3581_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_processedSnap_3517_);
lean_inc(v_parserState_3516_);
lean_dec(v_val_3508_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3581_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_processed_3521_; lean_object* v_result_x3f_3522_; 
v_processed_3521_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3517_);
v_result_x3f_3522_ = lean_ctor_get(v_processed_3521_, 2);
lean_inc(v_result_x3f_3522_);
if (lean_obj_tag(v_result_x3f_3522_) == 1)
{
lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3575_; 
lean_inc(v_stx_3515_);
lean_inc_ref(v_ictx_3514_);
lean_inc_ref(v_metaSnap_3513_);
lean_inc_ref(v_toSnapshot_3512_);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_snap_3506_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; 
v_unused_3576_ = lean_ctor_get(v_snap_3506_, 4);
lean_dec(v_unused_3576_);
v_unused_3577_ = lean_ctor_get(v_snap_3506_, 3);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_snap_3506_, 2);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_snap_3506_, 1);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_snap_3506_, 0);
lean_dec(v_unused_3580_);
v___x_3524_ = v_snap_3506_;
v_isShared_3525_ = v_isSharedCheck_3575_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v_snap_3506_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3575_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3574_; 
v_val_3526_ = lean_ctor_get(v_result_x3f_3522_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_result_x3f_3522_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3528_ = v_result_x3f_3522_;
v_isShared_3529_ = v_isSharedCheck_3574_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_result_x3f_3522_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3574_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_toSnapshot_3530_; lean_object* v_metaSnap_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3572_; 
v_toSnapshot_3530_ = lean_ctor_get(v_processed_3521_, 0);
v_metaSnap_3531_ = lean_ctor_get(v_processed_3521_, 1);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_processed_3521_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_processed_3521_, 2);
lean_dec(v_unused_3573_);
v___x_3533_ = v_processed_3521_;
v_isShared_3534_ = v_isSharedCheck_3572_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_metaSnap_3531_);
lean_inc(v_toSnapshot_3530_);
lean_dec(v_processed_3521_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3572_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_cmdState_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3570_; 
v_cmdState_3535_ = lean_ctor_get(v_val_3526_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_val_3526_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_val_3526_, 1);
lean_dec(v_unused_3571_);
v___x_3537_ = v_val_3526_;
v_isShared_3538_ = v_isSharedCheck_3570_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_cmdState_3535_);
lean_dec(v_val_3526_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3570_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v_resultSnap_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v_elabSnap_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v_termCmd_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3539_ = lean_box(0);
v___x_3540_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
lean_inc_ref(v_cmdState_3535_);
v_resultSnap_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_resultSnap_3541_, 0, v___x_3540_);
lean_ctor_set(v_resultSnap_3541_, 1, v_cmdState_3535_);
v___x_3542_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3543_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3539_, v_resultSnap_3541_);
v___x_3544_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3545_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4);
v_elabSnap_3546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3546_, 0, v___x_3540_);
lean_ctor_set(v_elabSnap_3546_, 1, v___x_3542_);
lean_ctor_set(v_elabSnap_3546_, 2, v___x_3543_);
lean_ctor_set(v_elabSnap_3546_, 3, v___x_3544_);
lean_ctor_set(v_elabSnap_3546_, 4, v___x_3545_);
v___x_3547_ = lean_box(0);
v___x_3548_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3549_, 0, v___x_3540_);
lean_ctor_set(v_termCmd_3549_, 1, v___x_3547_);
lean_ctor_set(v_termCmd_3549_, 2, v___x_3548_);
lean_ctor_set(v_termCmd_3549_, 3, v_elabSnap_3546_);
lean_ctor_set(v_termCmd_3549_, 4, v___x_3539_);
v___x_3550_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3539_, v_termCmd_3549_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 1, v___x_3550_);
v___x_3552_ = v___x_3537_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_cmdState_3535_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3554_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3552_);
v___x_3554_ = v___x_3528_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v_newProcessed_3556_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 2, v___x_3554_);
v_newProcessed_3556_ = v___x_3533_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_toSnapshot_3530_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_metaSnap_3531_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v___x_3554_);
v_newProcessed_3556_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3539_, v_newProcessed_3556_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3557_);
v___x_3559_ = v___x_3519_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_parserState_3516_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3561_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3559_);
v___x_3561_ = v___x_3510_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 4, v___x_3561_);
v___x_3563_ = v___x_3524_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_toSnapshot_3512_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_metaSnap_3513_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_ictx_3514_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_stx_3515_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
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
lean_dec(v_result_x3f_3522_);
lean_dec(v_processed_3521_);
lean_del_object(v___x_3519_);
lean_dec_ref(v_parserState_3516_);
lean_del_object(v___x_3510_);
return v_snap_3506_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3507_);
return v_snap_3506_;
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

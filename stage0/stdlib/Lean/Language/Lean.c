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
lean_object* v___x_512_; lean_object* v_infoState_513_; lean_object* v_trees_514_; lean_object* v___x_515_; lean_object* v_infoState_516_; lean_object* v_env_517_; lean_object* v_messages_518_; lean_object* v_scopes_519_; lean_object* v_usedQuotCtxts_520_; lean_object* v_nextMacroScope_521_; lean_object* v_maxRecDepth_522_; lean_object* v_ngen_523_; lean_object* v_auxDeclNGen_524_; lean_object* v_traceState_525_; lean_object* v_snapshotTasks_526_; lean_object* v_prevLinterStates_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_548_; 
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
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_548_ == 0)
{
v___x_529_ = v___x_515_;
v_isShared_530_ = v_isSharedCheck_548_;
goto v_resetjp_528_;
}
else
{
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
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_548_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v_enabled_531_; lean_object* v_assignment_532_; lean_object* v_lazyAssignment_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_546_; 
v_enabled_531_ = lean_ctor_get_uint8(v_infoState_516_, sizeof(void*)*3);
v_assignment_532_ = lean_ctor_get(v_infoState_516_, 0);
v_lazyAssignment_533_ = lean_ctor_get(v_infoState_516_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_infoState_516_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v_infoState_516_, 2);
lean_dec(v_unused_547_);
v___x_535_ = v_infoState_516_;
v_isShared_536_ = v_isSharedCheck_546_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_lazyAssignment_533_);
lean_inc(v_assignment_532_);
lean_dec(v_infoState_516_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_546_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___closed__1);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 2, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_assignment_532_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_lazyAssignment_533_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v___x_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_545_, sizeof(void*)*3, v_enabled_531_);
v___x_539_ = v_reuseFailAlloc_545_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 8, v___x_539_);
v___x_541_ = v___x_529_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_env_517_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_messages_518_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_scopes_519_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_usedQuotCtxts_520_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_nextMacroScope_521_);
lean_ctor_set(v_reuseFailAlloc_544_, 5, v_maxRecDepth_522_);
lean_ctor_set(v_reuseFailAlloc_544_, 6, v_ngen_523_);
lean_ctor_set(v_reuseFailAlloc_544_, 7, v_auxDeclNGen_524_);
lean_ctor_set(v_reuseFailAlloc_544_, 8, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_544_, 9, v_traceState_525_);
lean_ctor_set(v_reuseFailAlloc_544_, 10, v_snapshotTasks_526_);
lean_ctor_set(v_reuseFailAlloc_544_, 11, v_prevLinterStates_527_);
v___x_541_ = v_reuseFailAlloc_544_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_st_ref_put(v___y_510_, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_trees_514_);
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg___boxed(lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_549_);
lean_dec(v___y_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___boxed(lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0(v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(lean_object* v_opts_560_, lean_object* v_opt_561_){
_start:
{
lean_object* v_name_562_; lean_object* v_defValue_563_; lean_object* v_map_564_; lean_object* v___x_565_; 
v_name_562_ = lean_ctor_get(v_opt_561_, 0);
v_defValue_563_ = lean_ctor_get(v_opt_561_, 1);
v_map_564_ = lean_ctor_get(v_opts_560_, 0);
v___x_565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_564_, v_name_562_);
if (lean_obj_tag(v___x_565_) == 0)
{
uint8_t v___x_566_; 
v___x_566_ = lean_unbox(v_defValue_563_);
return v___x_566_;
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_565_, 1);
if (lean_obj_tag(v_val_567_) == 1)
{
uint8_t v_v_568_; 
v_v_568_ = lean_ctor_get_uint8(v_val_567_, 0);
lean_dec_ref_known(v_val_567_, 0);
return v_v_568_;
}
else
{
uint8_t v___x_569_; 
lean_dec(v_val_567_);
v___x_569_ = lean_unbox(v_defValue_563_);
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1___boxed(lean_object* v_opts_570_, lean_object* v_opt_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_570_, v_opt_571_);
lean_dec_ref(v_opt_571_);
lean_dec_ref(v_opts_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(lean_object* v_val_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = l_Lean_Language_Snapshot_transform(v_val_576_, v___y_577_);
v___x_579_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed(lean_object* v_val_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0(v_val_581_, v___y_582_);
lean_dec_ref(v___y_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(lean_object* v_inst_584_, lean_object* v_val_585_){
_start:
{
lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_inc_ref(v_val_585_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(v___f_586_, 0, v_val_585_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_inst_584_);
lean_ctor_set(v___x_587_, 1, v_val_585_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___f_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(lean_object* v_stx_589_, lean_object* v_cmds_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__0___redArg(v___y_592_);
lean_dec_ref(v___x_594_);
v___x_595_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_589_, v_cmds_590_, v___y_591_, v___y_592_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed(lean_object* v_stx_596_, lean_object* v_cmds_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0(v_stx_596_, v_cmds_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_602_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__0);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
lean_ctor_set(v___x_607_, 3, v___x_606_);
lean_ctor_set(v___x_607_, 4, v___x_605_);
lean_ctor_set(v___x_607_, 5, v___x_605_);
lean_ctor_set(v___x_607_, 6, v___x_605_);
lean_ctor_set(v___x_607_, 7, v___x_605_);
lean_ctor_set(v___x_607_, 8, v___x_605_);
lean_ctor_set(v___x_607_, 9, v___x_605_);
lean_ctor_set(v___x_607_, 10, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_unsigned_to_nat(32u);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_611_ = ((size_t)5ULL);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_unsigned_to_nat(32u);
v___x_614_ = lean_mk_empty_array_with_capacity(v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__3);
v___x_616_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_612_);
lean_ctor_set(v___x_616_, 3, v___x_612_);
lean_ctor_set_usize(v___x_616_, 4, v___x_611_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(1);
v___x_618_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__4);
v___x_619_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
v___x_620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_617_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(lean_object* v_msgData_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; lean_object* v_env_625_; lean_object* v___x_626_; lean_object* v_scopes_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_opts_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_624_ = lean_st_ref_get(v___y_622_);
v_env_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc_ref(v_env_625_);
lean_dec(v___x_624_);
v___x_626_ = lean_st_ref_get(v___y_622_);
v_scopes_627_ = lean_ctor_get(v___x_626_, 2);
lean_inc(v_scopes_627_);
lean_dec(v___x_626_);
v___x_628_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_629_ = l_List_head_x21___redArg(v___x_628_, v_scopes_627_);
lean_dec(v_scopes_627_);
v_opts_630_ = lean_ctor_get(v___x_629_, 1);
lean_inc_ref(v_opts_630_);
lean_dec(v___x_629_);
v___x_631_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__2);
v___x_632_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__5);
v___x_633_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_633_, 0, v_env_625_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
lean_ctor_set(v___x_633_, 3, v_opts_630_);
v___x_634_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_msgData_621_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___boxed(lean_object* v_msgData_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_636_, v___y_637_);
lean_dec(v___y_637_);
return v_res_639_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(uint8_t v_suppressElabErrors_640_, uint8_t v___y_641_, lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 1)
{
lean_object* v_pre_643_; 
v_pre_643_ = lean_ctor_get(v_x_642_, 0);
if (lean_obj_tag(v_pre_643_) == 0)
{
lean_object* v_str_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_str_644_ = lean_ctor_get(v_x_642_, 1);
v___x_645_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__0));
v___x_646_ = lean_string_dec_eq(v_str_644_, v___x_645_);
if (v___x_646_ == 0)
{
return v___x_646_;
}
else
{
return v_suppressElabErrors_640_;
}
}
else
{
return v___y_641_;
}
}
else
{
return v___y_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_suppressElabErrors_647_, lean_object* v___y_648_, lean_object* v_x_649_){
_start:
{
uint8_t v_suppressElabErrors_boxed_650_; uint8_t v___y_9056__boxed_651_; uint8_t v_res_652_; lean_object* v_r_653_; 
v_suppressElabErrors_boxed_650_ = lean_unbox(v_suppressElabErrors_647_);
v___y_9056__boxed_651_ = lean_unbox(v___y_648_);
v_res_652_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v_suppressElabErrors_boxed_650_, v___y_9056__boxed_651_, v_x_649_);
lean_dec(v_x_649_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_655_, lean_object* v_msgData_656_, uint8_t v_severity_657_, uint8_t v_isSilent_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_727_; uint8_t v___y_728_; uint8_t v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; uint8_t v___y_755_; uint8_t v___y_756_; lean_object* v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; uint8_t v___y_763_; uint8_t v___y_764_; uint8_t v___y_765_; uint8_t v___x_780_; uint8_t v___y_782_; uint8_t v___y_783_; uint8_t v___y_784_; uint8_t v___y_786_; uint8_t v___x_798_; 
v___x_780_ = 2;
v___x_798_ = l_Lean_instBEqMessageSeverity_beq(v_severity_657_, v___x_780_);
if (v___x_798_ == 0)
{
v___y_786_ = v___x_798_;
goto v___jp_785_;
}
else
{
uint8_t v___x_799_; 
lean_inc_ref(v_msgData_656_);
v___x_799_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_656_);
v___y_786_ = v___x_799_;
goto v___jp_785_;
}
v___jp_662_:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Elab_Command_getScope___redArg(v___y_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = l_Lean_Elab_Command_getScope___redArg(v___y_670_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_709_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_709_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_709_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_709_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v_currNamespace_679_; lean_object* v_openDecls_680_; lean_object* v_env_681_; lean_object* v_messages_682_; lean_object* v_scopes_683_; lean_object* v_usedQuotCtxts_684_; lean_object* v_nextMacroScope_685_; lean_object* v_maxRecDepth_686_; lean_object* v_ngen_687_; lean_object* v_auxDeclNGen_688_; lean_object* v_infoState_689_; lean_object* v_traceState_690_; lean_object* v_snapshotTasks_691_; lean_object* v_prevLinterStates_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_708_; 
v___x_678_ = lean_st_ref_take(v___y_670_);
v_currNamespace_679_ = lean_ctor_get(v_a_672_, 2);
lean_inc(v_currNamespace_679_);
lean_dec(v_a_672_);
v_openDecls_680_ = lean_ctor_get(v_a_674_, 3);
lean_inc(v_openDecls_680_);
lean_dec(v_a_674_);
v_env_681_ = lean_ctor_get(v___x_678_, 0);
v_messages_682_ = lean_ctor_get(v___x_678_, 1);
v_scopes_683_ = lean_ctor_get(v___x_678_, 2);
v_usedQuotCtxts_684_ = lean_ctor_get(v___x_678_, 3);
v_nextMacroScope_685_ = lean_ctor_get(v___x_678_, 4);
v_maxRecDepth_686_ = lean_ctor_get(v___x_678_, 5);
v_ngen_687_ = lean_ctor_get(v___x_678_, 6);
v_auxDeclNGen_688_ = lean_ctor_get(v___x_678_, 7);
v_infoState_689_ = lean_ctor_get(v___x_678_, 8);
v_traceState_690_ = lean_ctor_get(v___x_678_, 9);
v_snapshotTasks_691_ = lean_ctor_get(v___x_678_, 10);
v_prevLinterStates_692_ = lean_ctor_get(v___x_678_, 11);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_708_ == 0)
{
v___x_694_ = v___x_678_;
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_prevLinterStates_692_);
lean_inc(v_snapshotTasks_691_);
lean_inc(v_traceState_690_);
lean_inc(v_infoState_689_);
lean_inc(v_auxDeclNGen_688_);
lean_inc(v_ngen_687_);
lean_inc(v_maxRecDepth_686_);
lean_inc(v_nextMacroScope_685_);
lean_inc(v_usedQuotCtxts_684_);
lean_inc(v_scopes_683_);
lean_inc(v_messages_682_);
lean_inc(v_env_681_);
lean_dec(v___x_678_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_currNamespace_679_);
lean_ctor_set(v___x_696_, 1, v_openDecls_680_);
v___x_697_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___y_667_);
lean_inc_ref(v___y_664_);
lean_inc_ref(v___y_668_);
v___x_698_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_698_, 0, v___y_668_);
lean_ctor_set(v___x_698_, 1, v___y_669_);
lean_ctor_set(v___x_698_, 2, v___y_665_);
lean_ctor_set(v___x_698_, 3, v___y_664_);
lean_ctor_set(v___x_698_, 4, v___x_697_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*5, v___y_663_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*5 + 1, v___y_666_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*5 + 2, v_isSilent_658_);
v___x_699_ = l_Lean_MessageLog_add(v___x_698_, v_messages_682_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_699_);
v___x_701_ = v___x_694_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_env_681_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_scopes_683_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_usedQuotCtxts_684_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_nextMacroScope_685_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_maxRecDepth_686_);
lean_ctor_set(v_reuseFailAlloc_707_, 6, v_ngen_687_);
lean_ctor_set(v_reuseFailAlloc_707_, 7, v_auxDeclNGen_688_);
lean_ctor_set(v_reuseFailAlloc_707_, 8, v_infoState_689_);
lean_ctor_set(v_reuseFailAlloc_707_, 9, v_traceState_690_);
lean_ctor_set(v_reuseFailAlloc_707_, 10, v_snapshotTasks_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 11, v_prevLinterStates_692_);
v___x_701_ = v_reuseFailAlloc_707_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_st_ref_put(v___y_670_, v___x_701_);
v___x_703_ = lean_box(0);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_703_);
v___x_705_ = v___x_676_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_a_672_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_665_);
v_a_710_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_673_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_673_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_665_);
v_a_718_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_671_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_671_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
v___jp_726_:
{
lean_object* v_fileName_732_; lean_object* v_fileMap_733_; uint8_t v_suppressElabErrors_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_753_; 
v_fileName_732_ = lean_ctor_get(v___y_659_, 0);
v_fileMap_733_ = lean_ctor_get(v___y_659_, 1);
v_suppressElabErrors_734_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*10);
v___x_735_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_656_);
v___x_736_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v___x_735_, v___y_660_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_753_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_753_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_753_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_inc_ref_n(v_fileMap_733_, 2);
v___x_741_ = l_Lean_FileMap_toPosition(v_fileMap_733_, v___y_730_);
lean_dec(v___y_730_);
v___x_742_ = l_Lean_FileMap_toPosition(v_fileMap_733_, v___y_731_);
lean_dec(v___y_731_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_734_ == 0)
{
lean_del_object(v___x_739_);
v___y_663_ = v___y_728_;
v___y_664_ = v___x_744_;
v___y_665_ = v___x_743_;
v___y_666_ = v___y_729_;
v___y_667_ = v_a_737_;
v___y_668_ = v_fileName_732_;
v___y_669_ = v___x_741_;
v___y_670_ = v___y_660_;
goto v___jp_662_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___f_747_; uint8_t v___x_748_; 
v___x_745_ = lean_box(v_suppressElabErrors_734_);
v___x_746_ = lean_box(v___y_727_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0___boxed), 3, 2);
lean_closure_set(v___f_747_, 0, v___x_745_);
lean_closure_set(v___f_747_, 1, v___x_746_);
lean_inc(v_a_737_);
v___x_748_ = l_Lean_MessageData_hasTag(v___f_747_, v_a_737_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec_ref_known(v___x_743_, 1);
lean_dec_ref(v___x_741_);
lean_dec(v_a_737_);
v___x_749_ = lean_box(0);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_749_);
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_del_object(v___x_739_);
v___y_663_ = v___y_728_;
v___y_664_ = v___x_744_;
v___y_665_ = v___x_743_;
v___y_666_ = v___y_729_;
v___y_667_ = v_a_737_;
v___y_668_ = v_fileName_732_;
v___y_669_ = v___x_741_;
v___y_670_ = v___y_660_;
goto v___jp_662_;
}
}
}
}
v___jp_754_:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Syntax_getTailPos_x3f(v___y_757_, v___y_756_);
lean_dec(v___y_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_inc(v___y_759_);
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_759_;
v___y_731_ = v___y_759_;
goto v___jp_726_;
}
else
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_760_, 1);
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_759_;
v___y_731_ = v_val_761_;
goto v___jp_726_;
}
}
v___jp_762_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Elab_Command_getRef___redArg(v___y_659_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v_ref_768_; lean_object* v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v_ref_768_ = l_Lean_replaceRef(v_ref_655_, v_a_767_);
lean_dec(v_a_767_);
v___x_769_ = l_Lean_Syntax_getPos_x3f(v_ref_768_, v___y_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v___y_755_ = v___y_763_;
v___y_756_ = v___y_764_;
v___y_757_ = v_ref_768_;
v___y_758_ = v___y_765_;
v___y_759_ = v___x_770_;
goto v___jp_754_;
}
else
{
lean_object* v_val_771_; 
v_val_771_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___x_769_, 1);
v___y_755_ = v___y_763_;
v___y_756_ = v___y_764_;
v___y_757_ = v_ref_768_;
v___y_758_ = v___y_765_;
v___y_759_ = v_val_771_;
goto v___jp_754_;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_msgData_656_);
v_a_772_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_766_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_766_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
v___jp_781_:
{
if (v___y_784_ == 0)
{
v___y_763_ = v___y_782_;
v___y_764_ = v___y_783_;
v___y_765_ = v_severity_657_;
goto v___jp_762_;
}
else
{
v___y_763_ = v___y_782_;
v___y_764_ = v___y_783_;
v___y_765_ = v___x_780_;
goto v___jp_762_;
}
}
v___jp_785_:
{
if (v___y_786_ == 0)
{
lean_object* v___x_787_; lean_object* v_scopes_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_opts_791_; uint8_t v___x_792_; uint8_t v___x_793_; 
v___x_787_ = lean_st_ref_get(v___y_660_);
v_scopes_788_ = lean_ctor_get(v___x_787_, 2);
lean_inc(v_scopes_788_);
lean_dec(v___x_787_);
v___x_789_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_790_ = l_List_head_x21___redArg(v___x_789_, v_scopes_788_);
lean_dec(v_scopes_788_);
v_opts_791_ = lean_ctor_get(v___x_790_, 1);
lean_inc_ref(v_opts_791_);
lean_dec(v___x_790_);
v___x_792_ = 1;
v___x_793_ = l_Lean_instBEqMessageSeverity_beq(v_severity_657_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec_ref(v_opts_791_);
v___y_782_ = v___y_786_;
v___y_783_ = v___y_786_;
v___y_784_ = v___x_793_;
goto v___jp_781_;
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = l_Lean_warningAsError;
v___x_795_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_791_, v___x_794_);
lean_dec_ref(v_opts_791_);
v___y_782_ = v___y_786_;
v___y_783_ = v___y_786_;
v___y_784_ = v___x_795_;
goto v___jp_781_;
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v_msgData_656_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___boxed(lean_object* v_ref_800_, lean_object* v_msgData_801_, lean_object* v_severity_802_, lean_object* v_isSilent_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
uint8_t v_severity_boxed_807_; uint8_t v_isSilent_boxed_808_; lean_object* v_res_809_; 
v_severity_boxed_807_ = lean_unbox(v_severity_802_);
v_isSilent_boxed_808_ = lean_unbox(v_isSilent_803_);
v_res_809_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_800_, v_msgData_801_, v_severity_boxed_807_, v_isSilent_boxed_808_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v_ref_800_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(lean_object* v_msgData_810_, uint8_t v_severity_811_, uint8_t v_isSilent_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Elab_Command_getRef___redArg(v___y_813_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_a_817_, v_msgData_810_, v_severity_811_, v_isSilent_812_, v___y_813_, v___y_814_);
lean_dec(v_a_817_);
return v___x_818_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_msgData_810_);
v_a_819_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_816_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12___boxed(lean_object* v_msgData_827_, lean_object* v_severity_828_, lean_object* v_isSilent_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
uint8_t v_severity_boxed_833_; uint8_t v_isSilent_boxed_834_; lean_object* v_res_835_; 
v_severity_boxed_833_ = lean_unbox(v_severity_828_);
v_isSilent_boxed_834_ = lean_unbox(v_isSilent_829_);
v_res_835_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_827_, v_severity_boxed_833_, v_isSilent_boxed_834_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(lean_object* v_msgData_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = 2;
v___x_841_ = 0;
v___x_842_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5_spec__12(v_msgData_836_, v___x_840_, v___x_841_, v___y_837_, v___y_838_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v_msgData_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(lean_object* v_ref_848_, lean_object* v_msgData_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; 
v___x_853_ = 2;
v___x_854_ = 0;
v___x_855_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(v_ref_848_, v_msgData_849_, v___x_853_, v___x_854_, v___y_850_, v___y_851_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_856_, lean_object* v_msgData_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_856_, v_msgData_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v_ref_856_);
return v_res_861_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__0));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(lean_object* v_ex_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
if (lean_obj_tag(v_ex_865_) == 0)
{
lean_object* v_ref_869_; lean_object* v_msg_870_; lean_object* v___x_871_; 
v_ref_869_ = lean_ctor_get(v_ex_865_, 0);
lean_inc(v_ref_869_);
v_msg_870_ = lean_ctor_get(v_ex_865_, 1);
lean_inc_ref(v_msg_870_);
lean_dec_ref_known(v_ex_865_, 2);
v___x_871_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4(v_ref_869_, v_msg_870_, v___y_866_, v___y_867_);
lean_dec(v_ref_869_);
return v___x_871_;
}
else
{
lean_object* v_id_872_; uint8_t v___y_874_; uint8_t v___x_896_; 
v_id_872_ = lean_ctor_get(v_ex_865_, 0);
lean_inc(v_id_872_);
v___x_896_ = l_Lean_Elab_isAbortExceptionId(v_id_872_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_Exception_isInterrupt(v_ex_865_);
lean_dec_ref_known(v_ex_865_, 2);
v___y_874_ = v___x_897_;
goto v___jp_873_;
}
else
{
lean_dec_ref_known(v_ex_865_, 2);
v___y_874_ = v___x_896_;
goto v___jp_873_;
}
v___jp_873_:
{
if (v___y_874_ == 0)
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_InternalExceptionId_getName(v_id_872_);
lean_dec(v_id_872_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___closed__1);
v___x_878_ = l_Lean_MessageData_ofName(v_a_876_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__5(v___x_879_, v___y_866_, v___y_867_);
return v___x_880_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
v_a_881_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_893_ == 0)
{
v___x_883_ = v___x_875_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_875_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_ref_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v_ref_885_ = lean_ctor_get(v___y_866_, 7);
v___x_886_ = lean_io_error_to_string(v_a_881_);
v___x_887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = l_Lean_MessageData_ofFormat(v___x_887_);
lean_inc(v_ref_885_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_ref_885_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_889_);
v___x_891_ = v___x_883_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_id_872_);
v___x_894_ = lean_box(0);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2___boxed(lean_object* v_ex_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_ex_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
v___x_907_ = lean_apply_3(v_x_903_, v___y_904_, v___y_905_, lean_box(0));
if (lean_obj_tag(v___x_907_) == 0)
{
return v___x_907_;
}
else
{
lean_object* v_a_908_; uint8_t v___x_909_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
v___x_909_ = l_Lean_Exception_isInterrupt(v_a_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_910_ = l_Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2(v_a_908_, v___y_904_, v___y_905_);
return v___x_910_;
}
else
{
lean_dec(v_a_908_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2___boxed(lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v_x_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(lean_object* v___f_916_, lean_object* v___x_917_, lean_object* v_val_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_a_922_; lean_object* v___x_924_; 
v___x_924_ = l_Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2(v___f_916_, v___x_917_, v_val_918_);
if (lean_obj_tag(v___x_924_) == 0)
{
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_a_922_ = v_a_925_;
goto v___jp_921_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_924_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec_ref_known(v___x_924_, 1);
v___x_934_ = lean_box(0);
v_a_922_ = v___x_934_;
goto v___jp_921_;
}
v___jp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_a_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed(lean_object* v___f_935_, lean_object* v___x_936_, lean_object* v_val_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1(v___f_935_, v___x_936_, v_val_937_, v___y_938_);
lean_dec_ref(v___y_938_);
lean_dec(v_val_937_);
lean_dec_ref(v___x_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(lean_object* v_h_941_, lean_object* v_x_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_get_set_stderr(v_h_941_);
lean_inc_ref(v___y_943_);
v___x_946_ = lean_apply_2(v_x_942_, v___y_943_, lean_box(0));
v___x_947_ = lean_get_set_stderr(v___x_945_);
lean_dec_ref(v___x_947_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg___boxed(lean_object* v_h_948_, lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_948_, v_x_949_, v___y_950_);
lean_dec_ref(v___y_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(lean_object* v_00_u03b1_953_, lean_object* v_h_954_, lean_object* v_x_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___redArg(v_h_954_, v_x_955_, v___y_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed(lean_object* v_00_u03b1_959_, lean_object* v_h_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7(v_00_u03b1_959_, v_h_960_, v_x_961_, v___y_962_);
lean_dec_ref(v___y_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(lean_object* v_h_965_, lean_object* v_x_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = lean_get_set_stdin(v_h_965_);
lean_inc_ref(v___y_967_);
v___x_970_ = lean_apply_2(v_x_966_, v___y_967_, lean_box(0));
v___x_971_ = lean_get_set_stdin(v___x_969_);
lean_dec_ref(v___x_971_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg___boxed(lean_object* v_h_972_, lean_object* v_x_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_972_, v_x_973_, v___y_974_);
lean_dec_ref(v___y_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(lean_object* v_msg_977_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_979_ = lean_panic_fn_borrowed(v___x_978_, v_msg_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(lean_object* v_h_980_, lean_object* v_x_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_get_set_stdout(v_h_980_);
lean_inc_ref(v___y_982_);
v___x_985_ = lean_apply_2(v_x_981_, v___y_982_, lean_box(0));
v___x_986_ = lean_get_set_stdout(v___x_984_);
lean_dec_ref(v___x_986_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg___boxed(lean_object* v_h_987_, lean_object* v_x_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_987_, v_x_988_, v___y_989_);
lean_dec_ref(v___y_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(lean_object* v_00_u03b1_992_, lean_object* v_h_993_, lean_object* v_x_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___redArg(v_h_993_, v_x_994_, v___y_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed(lean_object* v_00_u03b1_998_, lean_object* v_h_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4(v_00_u03b1_998_, v_h_999_, v_x_1000_, v___y_1001_);
lean_dec_ref(v___y_1001_);
return v_res_1003_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = l_ByteArray_empty;
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1010_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__3));
v___x_1011_ = lean_unsigned_to_nat(46u);
v___x_1012_ = lean_unsigned_to_nat(193u);
v___x_1013_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__2));
v___x_1014_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__1));
v___x_1015_ = l_mkPanicMessageWithDecl(v___x_1014_, v___x_1013_, v___x_1012_, v___x_1011_, v___x_1010_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(lean_object* v_x_1016_, uint8_t v_isolateStderr_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___y_1030_; 
v___x_1024_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__0);
v___x_1025_ = lean_st_mk_ref(v___x_1024_);
v___x_1026_ = lean_st_mk_ref(v___x_1024_);
v___x_1027_ = l_IO_FS_Stream_ofBuffer(v___x_1025_);
lean_inc(v___x_1026_);
v___x_1028_ = l_IO_FS_Stream_ofBuffer(v___x_1026_);
if (v_isolateStderr_1017_ == 0)
{
v___y_1030_ = v_x_1016_;
goto v___jp_1029_;
}
else
{
lean_object* v___x_1039_; 
lean_inc_ref(v___x_1028_);
v___x_1039_ = lean_alloc_closure((void*)(l_IO_withStderr___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__7___boxed), 5, 3);
lean_closure_set(v___x_1039_, 0, lean_box(0));
lean_closure_set(v___x_1039_, 1, v___x_1028_);
lean_closure_set(v___x_1039_, 2, v_x_1016_);
v___y_1030_ = v___x_1039_;
goto v___jp_1029_;
}
v___jp_1020_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_1022_);
lean_ctor_set(v___x_1023_, 1, v___y_1021_);
return v___x_1023_;
}
v___jp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_data_1034_; uint8_t v___x_1035_; 
v___x_1031_ = lean_alloc_closure((void*)(l_IO_withStdout___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__4___boxed), 5, 3);
lean_closure_set(v___x_1031_, 0, lean_box(0));
lean_closure_set(v___x_1031_, 1, v___x_1028_);
lean_closure_set(v___x_1031_, 2, v___y_1030_);
v___x_1032_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v___x_1027_, v___x_1031_, v___y_1018_);
v___x_1033_ = lean_st_ref_get(v___x_1026_);
lean_dec(v___x_1026_);
v_data_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref(v_data_1034_);
lean_dec(v___x_1033_);
v___x_1035_ = lean_string_validate_utf8(v_data_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref(v_data_1034_);
v___x_1036_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4, &l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4_once, _init_l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___closed__4);
v___x_1037_ = l_panic___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__6(v___x_1036_);
v___y_1021_ = v___x_1032_;
v___y_1022_ = v___x_1037_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_string_from_utf8_unchecked(v_data_1034_);
v___y_1021_ = v___x_1032_;
v___y_1022_ = v___x_1038_;
goto v___jp_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg___boxed(lean_object* v_x_1040_, lean_object* v_isolateStderr_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v_isolateStderr_boxed_1044_; lean_object* v_res_1045_; 
v_isolateStderr_boxed_1044_ = lean_unbox(v_isolateStderr_1041_);
v_res_1045_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1040_, v_isolateStderr_boxed_1044_, v___y_1042_);
lean_dec_ref(v___y_1042_);
return v_res_1045_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4(void){
_start:
{
uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = 1;
v___x_1055_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__3));
v___x_1056_ = l_Lean_Name_toString(v___x_1055_, v___x_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(lean_object* v_stx_1057_, lean_object* v_cmds_1058_, lean_object* v_cmdState_1059_, lean_object* v_beginPos_1060_, lean_object* v_snap_1061_, lean_object* v_cancelTk_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_env_1065_; lean_object* v_scopes_1066_; lean_object* v_usedQuotCtxts_1067_; lean_object* v_nextMacroScope_1068_; lean_object* v_maxRecDepth_1069_; lean_object* v_ngen_1070_; lean_object* v_auxDeclNGen_1071_; lean_object* v_infoState_1072_; lean_object* v_prevLinterStates_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1150_; 
v_env_1065_ = lean_ctor_get(v_cmdState_1059_, 0);
v_scopes_1066_ = lean_ctor_get(v_cmdState_1059_, 2);
v_usedQuotCtxts_1067_ = lean_ctor_get(v_cmdState_1059_, 3);
v_nextMacroScope_1068_ = lean_ctor_get(v_cmdState_1059_, 4);
v_maxRecDepth_1069_ = lean_ctor_get(v_cmdState_1059_, 5);
v_ngen_1070_ = lean_ctor_get(v_cmdState_1059_, 6);
v_auxDeclNGen_1071_ = lean_ctor_get(v_cmdState_1059_, 7);
v_infoState_1072_ = lean_ctor_get(v_cmdState_1059_, 8);
v_prevLinterStates_1073_ = lean_ctor_get(v_cmdState_1059_, 11);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_cmdState_1059_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1151_ = lean_ctor_get(v_cmdState_1059_, 10);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_cmdState_1059_, 9);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_cmdState_1059_, 1);
lean_dec(v_unused_1153_);
v___x_1075_ = v_cmdState_1059_;
v_isShared_1076_ = v_isSharedCheck_1150_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_prevLinterStates_1073_);
lean_inc(v_infoState_1072_);
lean_inc(v_auxDeclNGen_1071_);
lean_inc(v_ngen_1070_);
lean_inc(v_maxRecDepth_1069_);
lean_inc(v_nextMacroScope_1068_);
lean_inc(v_usedQuotCtxts_1067_);
lean_inc(v_scopes_1066_);
lean_inc(v_env_1065_);
lean_dec(v_cmdState_1059_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1150_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1077_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1078_ = l_List_head_x21___redArg(v___x_1077_, v_scopes_1066_);
v___x_1079_ = l_Lean_MessageLog_empty;
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_1082_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 10, v___x_1082_);
lean_ctor_set(v___x_1075_, 9, v___x_1081_);
lean_ctor_set(v___x_1075_, 1, v___x_1079_);
v___x_1084_ = v___x_1075_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_env_1065_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_scopes_1066_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_usedQuotCtxts_1067_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_nextMacroScope_1068_);
lean_ctor_set(v_reuseFailAlloc_1149_, 5, v_maxRecDepth_1069_);
lean_ctor_set(v_reuseFailAlloc_1149_, 6, v_ngen_1070_);
lean_ctor_set(v_reuseFailAlloc_1149_, 7, v_auxDeclNGen_1071_);
lean_ctor_set(v_reuseFailAlloc_1149_, 8, v_infoState_1072_);
lean_ctor_set(v_reuseFailAlloc_1149_, 9, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1149_, 10, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1149_, 11, v_prevLinterStates_1073_);
v___x_1084_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v_toProcessingContext_1086_; lean_object* v_fileName_1087_; lean_object* v_fileMap_1088_; lean_object* v_opts_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___y_1099_; uint8_t v___y_1100_; lean_object* v_messages_1101_; lean_object* v___y_1128_; 
v___x_1085_ = lean_st_mk_ref(v___x_1084_);
v_toProcessingContext_1086_ = lean_ctor_get(v_a_1063_, 0);
v_fileName_1087_ = lean_ctor_get(v_toProcessingContext_1086_, 1);
v_fileMap_1088_ = lean_ctor_get(v_toProcessingContext_1086_, 2);
v_opts_1089_ = lean_ctor_get(v___x_1078_, 1);
lean_inc_ref(v_opts_1089_);
lean_dec(v___x_1078_);
v___f_1090_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1090_, 0, v_stx_1057_);
lean_closure_set(v___f_1090_, 1, v_cmds_1058_);
v___x_1091_ = l_Lean_Language_instImpl_00___x40_Lean_Language_Basic_3093936625____hygCtx___hyg_8_;
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_firstFrontendMacroScope;
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Lean_internal_cmdlineSnapshots;
v___x_1097_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1089_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1148_; 
lean_inc_ref(v_snap_1061_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_snap_1061_);
v___y_1128_ = v___x_1148_;
goto v___jp_1127_;
}
else
{
v___y_1128_ = v___x_1093_;
goto v___jp_1127_;
}
v___jp_1098_:
{
lean_object* v_new_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v_env_1108_; lean_object* v_scopes_1109_; lean_object* v_usedQuotCtxts_1110_; lean_object* v_nextMacroScope_1111_; lean_object* v_maxRecDepth_1112_; lean_object* v_ngen_1113_; lean_object* v_auxDeclNGen_1114_; lean_object* v_infoState_1115_; lean_object* v_traceState_1116_; lean_object* v_snapshotTasks_1117_; lean_object* v_prevLinterStates_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_new_1102_ = lean_ctor_get(v_snap_1061_, 1);
lean_inc(v_new_1102_);
lean_dec_ref(v_snap_1061_);
v___x_1103_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__4);
v___x_1104_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_1105_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
lean_ctor_set(v___x_1105_, 2, v___x_1093_);
lean_ctor_set(v___x_1105_, 3, v___x_1081_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*4, v___y_1100_);
v___x_1106_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1091_, v___x_1105_);
v___x_1107_ = lean_io_promise_resolve(v___x_1106_, v_new_1102_);
lean_dec(v_new_1102_);
v_env_1108_ = lean_ctor_get(v___y_1099_, 0);
v_scopes_1109_ = lean_ctor_get(v___y_1099_, 2);
v_usedQuotCtxts_1110_ = lean_ctor_get(v___y_1099_, 3);
v_nextMacroScope_1111_ = lean_ctor_get(v___y_1099_, 4);
v_maxRecDepth_1112_ = lean_ctor_get(v___y_1099_, 5);
v_ngen_1113_ = lean_ctor_get(v___y_1099_, 6);
v_auxDeclNGen_1114_ = lean_ctor_get(v___y_1099_, 7);
v_infoState_1115_ = lean_ctor_get(v___y_1099_, 8);
v_traceState_1116_ = lean_ctor_get(v___y_1099_, 9);
v_snapshotTasks_1117_ = lean_ctor_get(v___y_1099_, 10);
v_prevLinterStates_1118_ = lean_ctor_get(v___y_1099_, 11);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___y_1099_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___y_1099_, 1);
lean_dec(v_unused_1126_);
v___x_1120_ = v___y_1099_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_prevLinterStates_1118_);
lean_inc(v_snapshotTasks_1117_);
lean_inc(v_traceState_1116_);
lean_inc(v_infoState_1115_);
lean_inc(v_auxDeclNGen_1114_);
lean_inc(v_ngen_1113_);
lean_inc(v_maxRecDepth_1112_);
lean_inc(v_nextMacroScope_1111_);
lean_inc(v_usedQuotCtxts_1110_);
lean_inc(v_scopes_1109_);
lean_inc(v_env_1108_);
lean_dec(v___y_1099_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v_messages_1101_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_env_1108_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_messages_1101_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_scopes_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_usedQuotCtxts_1110_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_nextMacroScope_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_maxRecDepth_1112_);
lean_ctor_set(v_reuseFailAlloc_1124_, 6, v_ngen_1113_);
lean_ctor_set(v_reuseFailAlloc_1124_, 7, v_auxDeclNGen_1114_);
lean_ctor_set(v_reuseFailAlloc_1124_, 8, v_infoState_1115_);
lean_ctor_set(v_reuseFailAlloc_1124_, 9, v_traceState_1116_);
lean_ctor_set(v_reuseFailAlloc_1124_, 10, v_snapshotTasks_1117_);
lean_ctor_set(v_reuseFailAlloc_1124_, 11, v_prevLinterStates_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
v___jp_1127_:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v_fst_1136_; lean_object* v___x_1137_; lean_object* v_messages_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_cancelTk_1062_);
v___x_1130_ = 0;
lean_inc(v_beginPos_1060_);
lean_inc_ref(v_fileMap_1088_);
lean_inc_ref(v_fileName_1087_);
v___x_1131_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1131_, 0, v_fileName_1087_);
lean_ctor_set(v___x_1131_, 1, v_fileMap_1088_);
lean_ctor_set(v___x_1131_, 2, v___x_1080_);
lean_ctor_set(v___x_1131_, 3, v_beginPos_1060_);
lean_ctor_set(v___x_1131_, 4, v___x_1092_);
lean_ctor_set(v___x_1131_, 5, v___x_1093_);
lean_ctor_set(v___x_1131_, 6, v___x_1094_);
lean_ctor_set(v___x_1131_, 7, v___x_1095_);
lean_ctor_set(v___x_1131_, 8, v___y_1128_);
lean_ctor_set(v___x_1131_, 9, v___x_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*10, v___x_1130_);
lean_inc(v___x_1085_);
v___f_1132_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1132_, 0, v___f_1090_);
lean_closure_set(v___f_1132_, 1, v___x_1131_);
lean_closure_set(v___f_1132_, 2, v___x_1085_);
v___x_1133_ = l_Lean_Core_stderrAsMessages;
v___x_1134_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1089_, v___x_1133_);
lean_dec_ref(v_opts_1089_);
v___x_1135_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v___f_1132_, v___x_1134_, v_a_1063_);
v_fst_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_fst_1136_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = lean_st_ref_get(v___x_1085_);
lean_dec(v___x_1085_);
v_messages_1138_ = lean_ctor_get(v___x_1137_, 1);
lean_inc_ref(v_messages_1138_);
v___x_1139_ = lean_string_utf8_byte_size(v_fst_1136_);
v___x_1140_ = lean_nat_dec_eq(v___x_1139_, v___x_1080_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_inc_ref(v_fileMap_1088_);
v___x_1141_ = l_Lean_FileMap_toPosition(v_fileMap_1088_, v_beginPos_1060_);
lean_dec(v_beginPos_1060_);
v___x_1142_ = 0;
v___x_1143_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_fst_1136_);
v___x_1145_ = l_Lean_MessageData_ofFormat(v___x_1144_);
lean_inc_ref(v_fileName_1087_);
v___x_1146_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1146_, 0, v_fileName_1087_);
lean_ctor_set(v___x_1146_, 1, v___x_1141_);
lean_ctor_set(v___x_1146_, 2, v___x_1093_);
lean_ctor_set(v___x_1146_, 3, v___x_1143_);
lean_ctor_set(v___x_1146_, 4, v___x_1145_);
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*5, v___x_1130_);
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*5 + 1, v___x_1142_);
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*5 + 2, v___x_1130_);
v___x_1147_ = l_Lean_MessageLog_add(v___x_1146_, v_messages_1138_);
v___y_1099_ = v___x_1137_;
v___y_1100_ = v___x_1130_;
v_messages_1101_ = v___x_1147_;
goto v___jp_1098_;
}
else
{
lean_dec(v_fst_1136_);
lean_dec(v_beginPos_1060_);
v___y_1099_ = v___x_1137_;
v___y_1100_ = v___x_1130_;
v_messages_1101_ = v_messages_1138_;
goto v___jp_1098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1154_, lean_object* v_cmds_1155_, lean_object* v_cmdState_1156_, lean_object* v_beginPos_1157_, lean_object* v_snap_1158_, lean_object* v_cancelTk_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1154_, v_cmds_1155_, v_cmdState_1156_, v_beginPos_1157_, v_snap_1158_, v_cancelTk_1159_, v_a_1160_);
lean_dec_ref(v_a_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1163_, lean_object* v_h_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1164_, v_x_1165_, v___y_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_h_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1169_, v_h_1170_, v_x_1171_, v___y_1172_);
lean_dec_ref(v___y_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1175_, lean_object* v_x_1176_, uint8_t v_isolateStderr_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1176_, v_isolateStderr_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_x_1182_, lean_object* v_isolateStderr_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v_isolateStderr_boxed_1186_; lean_object* v_res_1187_; 
v_isolateStderr_boxed_1186_ = lean_unbox(v_isolateStderr_1183_);
v_res_1187_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1181_, v_x_1182_, v_isolateStderr_boxed_1186_, v___y_1184_);
lean_dec_ref(v___y_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1188_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1198_){
_start:
{
lean_object* v_toSnapshotTreeM_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_toSnapshotTreeM_1199_ = lean_ctor_get(v_a_1198_, 1);
lean_inc_ref(v_toSnapshotTreeM_1199_);
lean_dec_ref(v_a_1198_);
v___x_1200_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1201_ = lean_apply_1(v_toSnapshotTreeM_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1202_){
_start:
{
lean_object* v_toSnapshot_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_toSnapshot_1203_ = lean_ctor_get(v_a_1202_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1202_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_a_1202_, 1);
lean_dec(v_unused_1214_);
v___x_1205_ = v_a_1202_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_toSnapshot_1203_);
lean_dec(v_a_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1207_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1208_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1203_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1209_);
lean_ctor_set(v___x_1205_, 0, v___x_1208_);
v___x_1211_ = v___x_1205_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1217_ = l_Lean_Language_Snapshot_transform(v_a_1215_, v___x_1216_);
v___x_1218_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1220_, lean_object* v_opt_1221_){
_start:
{
lean_object* v_name_1222_; lean_object* v_defValue_1223_; lean_object* v_map_1224_; lean_object* v___x_1225_; 
v_name_1222_ = lean_ctor_get(v_opt_1221_, 0);
v_defValue_1223_ = lean_ctor_get(v_opt_1221_, 1);
v_map_1224_ = lean_ctor_get(v_opts_1220_, 0);
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1224_, v_name_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_inc(v_defValue_1223_);
return v_defValue_1223_;
}
else
{
lean_object* v_val_1226_; 
v_val_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v___x_1225_, 1);
if (lean_obj_tag(v_val_1226_) == 3)
{
lean_object* v_v_1227_; 
v_v_1227_ = lean_ctor_get(v_val_1226_, 0);
lean_inc(v_v_1227_);
lean_dec_ref_known(v_val_1226_, 1);
return v_v_1227_;
}
else
{
lean_dec(v_val_1226_);
lean_inc(v_defValue_1223_);
return v_defValue_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1228_, lean_object* v_opt_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1228_, v_opt_1229_);
lean_dec_ref(v_opt_1229_);
lean_dec_ref(v_opts_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1233_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1231_, v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1240_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1241_ = l_Lean_Name_append(v___x_1240_, v___x_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1242_, lean_object* v___x_1243_, uint8_t v_val_1244_, lean_object* v_val_1245_, lean_object* v_val_1246_, lean_object* v___x_1247_, lean_object* v___x_1248_, uint8_t v___x_1249_, lean_object* v_a_1250_, lean_object* v_pos_1251_, lean_object* v___x_1252_, lean_object* v_infoSt_1253_){
_start:
{
lean_object* v___y_1256_; lean_object* v_msgLog_1257_; lean_object* v___y_1263_; lean_object* v_trees_1295_; lean_object* v_size_1296_; uint8_t v___x_1297_; 
v_trees_1295_ = lean_ctor_get(v_infoSt_1253_, 2);
v_size_1296_ = lean_ctor_get(v_trees_1295_, 2);
v___x_1297_ = lean_nat_dec_lt(v___x_1248_, v_size_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = l_outOfBounds___redArg(v___x_1252_);
v___y_1263_ = v___x_1298_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1252_, v_trees_1295_, v___x_1248_);
v___y_1263_ = v___x_1299_;
goto v___jp_1262_;
}
v___jp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1257_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___y_1256_);
v___x_1260_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1242_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
lean_ctor_set(v___x_1260_, 2, v___x_1259_);
lean_ctor_set(v___x_1260_, 3, v___x_1243_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*4, v_val_1244_);
v___x_1261_ = lean_io_promise_resolve(v___x_1260_, v_val_1245_);
return v___x_1261_;
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_scopes_1266_; lean_object* v___x_1267_; lean_object* v_opts_1268_; uint8_t v_hasTrace_1269_; lean_object* v___x_1270_; 
v___x_1264_ = l_Lean_inheritedTraceOptions;
v___x_1265_ = lean_st_ref_get(v___x_1264_);
v_scopes_1266_ = lean_ctor_get(v_val_1246_, 2);
v___x_1267_ = l_List_head_x21___redArg(v___x_1247_, v_scopes_1266_);
v_opts_1268_ = lean_ctor_get(v___x_1267_, 1);
lean_inc_ref(v_opts_1268_);
lean_dec(v___x_1267_);
v_hasTrace_1269_ = lean_ctor_get_uint8(v_opts_1268_, sizeof(void*)*1);
v___x_1270_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1269_ == 0)
{
lean_dec_ref(v_opts_1268_);
lean_dec(v___x_1265_);
lean_dec(v___x_1248_);
v___y_1256_ = v___y_1263_;
v_msgLog_1257_ = v___x_1270_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1272_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1273_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1265_, v_opts_1268_, v___x_1273_);
lean_dec_ref(v_opts_1268_);
lean_dec(v___x_1265_);
if (v___x_1274_ == 0)
{
lean_dec(v___x_1248_);
v___y_1256_ = v___y_1263_;
v_msgLog_1257_ = v___x_1270_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_box(0);
lean_inc_ref(v___y_1263_);
v___x_1276_ = l_Lean_Elab_InfoTree_format(v___y_1263_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; double v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_toProcessingContext_1281_; lean_object* v_fileName_1282_; lean_object* v_fileMap_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = lean_float_of_nat(v___x_1248_);
v___x_1279_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1280_, 0, v___x_1271_);
lean_ctor_set(v___x_1280_, 1, v___x_1275_);
lean_ctor_set(v___x_1280_, 2, v___x_1279_);
lean_ctor_set_float(v___x_1280_, sizeof(void*)*3, v___x_1278_);
lean_ctor_set_float(v___x_1280_, sizeof(void*)*3 + 8, v___x_1278_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 16, v___x_1249_);
v_toProcessingContext_1281_ = lean_ctor_get(v_a_1250_, 0);
v_fileName_1282_ = lean_ctor_get(v_toProcessingContext_1281_, 1);
v_fileMap_1283_ = lean_ctor_get(v_toProcessingContext_1281_, 2);
v___x_1284_ = l_Lean_MessageData_nil;
v___x_1285_ = l_Lean_MessageData_ofFormat(v_a_1277_);
v___x_1286_ = lean_unsigned_to_nat(1u);
v___x_1287_ = lean_mk_empty_array_with_capacity(v___x_1286_);
v___x_1288_ = lean_array_push(v___x_1287_, v___x_1285_);
v___x_1289_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1280_);
lean_ctor_set(v___x_1289_, 1, v___x_1284_);
lean_ctor_set(v___x_1289_, 2, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1272_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_inc_ref(v_fileMap_1283_);
v___x_1291_ = l_Lean_FileMap_toPosition(v_fileMap_1283_, v_pos_1251_);
v___x_1292_ = 0;
lean_inc_ref(v_fileName_1282_);
v___x_1293_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1293_, 0, v_fileName_1282_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1275_);
lean_ctor_set(v___x_1293_, 3, v___x_1279_);
lean_ctor_set(v___x_1293_, 4, v___x_1290_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*5, v_val_1244_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*5 + 1, v___x_1292_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*5 + 2, v_val_1244_);
v___x_1294_ = l_Lean_MessageLog_add(v___x_1293_, v___x_1270_);
v___y_1256_ = v___y_1263_;
v_msgLog_1257_ = v___x_1294_;
goto v___jp_1255_;
}
else
{
lean_dec_ref_known(v___x_1276_, 1);
lean_dec(v___x_1248_);
v___y_1256_ = v___y_1263_;
v_msgLog_1257_ = v___x_1270_;
goto v___jp_1255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v_val_1302_, lean_object* v_val_1303_, lean_object* v_val_1304_, lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, lean_object* v_a_1308_, lean_object* v_pos_1309_, lean_object* v___x_1310_, lean_object* v_infoSt_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_val_35006__boxed_1313_; uint8_t v___x_35011__boxed_1314_; lean_object* v_res_1315_; 
v_val_35006__boxed_1313_ = lean_unbox(v_val_1302_);
v___x_35011__boxed_1314_ = lean_unbox(v___x_1307_);
v_res_1315_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1300_, v___x_1301_, v_val_35006__boxed_1313_, v_val_1303_, v_val_1304_, v___x_1305_, v___x_1306_, v___x_35011__boxed_1314_, v_a_1308_, v_pos_1309_, v___x_1310_, v_infoSt_1311_);
lean_dec_ref(v_infoSt_1311_);
lean_dec_ref(v___x_1310_);
lean_dec(v_pos_1309_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v_val_1304_);
lean_dec(v_val_1303_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, uint8_t v_val_1319_, lean_object* v_as_1320_, size_t v_sz_1321_, size_t v_i_1322_, lean_object* v_b_1323_){
_start:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_usize_dec_lt(v_i_1322_, v_sz_1321_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v___x_1318_);
lean_dec_ref(v___x_1316_);
return v_b_1323_;
}
else
{
lean_object* v_snd_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1344_; 
v_snd_1326_ = lean_ctor_get(v_b_1323_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_b_1323_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_b_1323_, 0);
lean_dec(v_unused_1345_);
v___x_1328_ = v_b_1323_;
v_isShared_1329_ = v_isSharedCheck_1344_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snd_1326_);
lean_dec(v_b_1323_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1344_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_a_1330_; lean_object* v_msg_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v_a_1330_ = lean_array_uget_borrowed(v_as_1320_, v_i_1322_);
v_msg_1331_ = lean_ctor_get(v_a_1330_, 1);
v___x_1332_ = lean_box(0);
lean_inc_ref(v___x_1316_);
v___x_1333_ = l_Lean_FileMap_toPosition(v___x_1316_, v___x_1317_);
v___x_1334_ = 0;
v___x_1335_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1331_);
lean_inc_ref(v___x_1318_);
v___x_1336_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1336_, 0, v___x_1318_);
lean_ctor_set(v___x_1336_, 1, v___x_1333_);
lean_ctor_set(v___x_1336_, 2, v___x_1332_);
lean_ctor_set(v___x_1336_, 3, v___x_1335_);
lean_ctor_set(v___x_1336_, 4, v_msg_1331_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5, v_val_1319_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5 + 1, v___x_1334_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5 + 2, v_val_1319_);
v___x_1337_ = l_Lean_MessageLog_add(v___x_1336_, v_snd_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1337_);
lean_ctor_set(v___x_1328_, 0, v___x_1332_);
v___x_1339_ = v___x_1328_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
size_t v___x_1340_; size_t v___x_1341_; 
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1322_, v___x_1340_);
v_i_1322_ = v___x_1341_;
v_b_1323_ = v___x_1339_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1346_, lean_object* v___x_1347_, lean_object* v___x_1348_, lean_object* v_val_1349_, lean_object* v_as_1350_, lean_object* v_sz_1351_, lean_object* v_i_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_val_35119__boxed_1355_; size_t v_sz_boxed_1356_; size_t v_i_boxed_1357_; lean_object* v_res_1358_; 
v_val_35119__boxed_1355_ = lean_unbox(v_val_1349_);
v_sz_boxed_1356_ = lean_unbox_usize(v_sz_1351_);
lean_dec(v_sz_1351_);
v_i_boxed_1357_ = lean_unbox_usize(v_i_1352_);
lean_dec(v_i_1352_);
v_res_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1346_, v___x_1347_, v___x_1348_, v_val_35119__boxed_1355_, v_as_1350_, v_sz_boxed_1356_, v_i_boxed_1357_, v_b_1353_);
lean_dec_ref(v_as_1350_);
lean_dec(v___x_1347_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, uint8_t v_val_1362_, lean_object* v_as_1363_, size_t v_sz_1364_, size_t v_i_1365_, lean_object* v_b_1366_){
_start:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_usize_dec_lt(v_i_1365_, v_sz_1364_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v___x_1361_);
lean_dec_ref(v___x_1359_);
return v_b_1366_;
}
else
{
lean_object* v_snd_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1387_; 
v_snd_1369_ = lean_ctor_get(v_b_1366_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_b_1366_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v_b_1366_, 0);
lean_dec(v_unused_1388_);
v___x_1371_ = v_b_1366_;
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_snd_1369_);
lean_dec(v_b_1366_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_a_1373_; lean_object* v_msg_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v_a_1373_ = lean_array_uget_borrowed(v_as_1363_, v_i_1365_);
v_msg_1374_ = lean_ctor_get(v_a_1373_, 1);
v___x_1375_ = lean_box(0);
lean_inc_ref(v___x_1359_);
v___x_1376_ = l_Lean_FileMap_toPosition(v___x_1359_, v___x_1360_);
v___x_1377_ = 0;
v___x_1378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1374_);
lean_inc_ref(v___x_1361_);
v___x_1379_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1379_, 0, v___x_1361_);
lean_ctor_set(v___x_1379_, 1, v___x_1376_);
lean_ctor_set(v___x_1379_, 2, v___x_1375_);
lean_ctor_set(v___x_1379_, 3, v___x_1378_);
lean_ctor_set(v___x_1379_, 4, v_msg_1374_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*5, v_val_1362_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*5 + 1, v___x_1377_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*5 + 2, v_val_1362_);
v___x_1380_ = l_Lean_MessageLog_add(v___x_1379_, v_snd_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1380_);
lean_ctor_set(v___x_1371_, 0, v___x_1375_);
v___x_1382_ = v___x_1371_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((size_t)1ULL);
v___x_1384_ = lean_usize_add(v_i_1365_, v___x_1383_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1359_, v___x_1360_, v___x_1361_, v_val_1362_, v_as_1363_, v_sz_1364_, v___x_1384_, v___x_1382_);
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v_val_1392_, lean_object* v_as_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_val_35171__boxed_1398_; size_t v_sz_boxed_1399_; size_t v_i_boxed_1400_; lean_object* v_res_1401_; 
v_val_35171__boxed_1398_ = lean_unbox(v_val_1392_);
v_sz_boxed_1399_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1400_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1389_, v___x_1390_, v___x_1391_, v_val_35171__boxed_1398_, v_as_1393_, v_sz_boxed_1399_, v_i_boxed_1400_, v_b_1396_);
lean_dec_ref(v_as_1393_);
lean_dec(v___x_1390_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, uint8_t v_val_1406_, lean_object* v_n_1407_, lean_object* v_b_1408_){
_start:
{
if (lean_obj_tag(v_n_1407_) == 0)
{
lean_object* v_cs_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; lean_object* v_fst_1416_; 
v_cs_1410_ = lean_ctor_get(v_n_1407_, 0);
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_b_1408_);
v_sz_1413_ = lean_array_size(v_cs_1410_);
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1402_, v___x_1403_, v___x_1404_, v___x_1405_, v_val_1406_, v_cs_1410_, v_sz_1413_, v___x_1414_, v___x_1412_);
v_fst_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_fst_1416_);
if (lean_obj_tag(v_fst_1416_) == 0)
{
lean_object* v_snd_1417_; lean_object* v___x_1418_; 
v_snd_1417_ = lean_ctor_get(v___x_1415_, 1);
lean_inc(v_snd_1417_);
lean_dec_ref(v___x_1415_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_snd_1417_);
return v___x_1418_;
}
else
{
lean_object* v_val_1419_; 
lean_dec_ref(v___x_1415_);
v_val_1419_ = lean_ctor_get(v_fst_1416_, 0);
lean_inc(v_val_1419_);
lean_dec_ref_known(v_fst_1416_, 1);
return v_val_1419_;
}
}
else
{
lean_object* v_vs_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v_fst_1426_; 
v_vs_1420_ = lean_ctor_get(v_n_1407_, 0);
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v_b_1408_);
v_sz_1423_ = lean_array_size(v_vs_1420_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1403_, v___x_1404_, v___x_1405_, v_val_1406_, v_vs_1420_, v_sz_1423_, v___x_1424_, v___x_1422_);
v_fst_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_fst_1426_);
if (lean_obj_tag(v_fst_1426_) == 0)
{
lean_object* v_snd_1427_; lean_object* v___x_1428_; 
v_snd_1427_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_snd_1427_);
lean_dec_ref(v___x_1425_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_snd_1427_);
return v___x_1428_;
}
else
{
lean_object* v_val_1429_; 
lean_dec_ref(v___x_1425_);
v_val_1429_ = lean_ctor_get(v_fst_1426_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v_fst_1426_, 1);
return v_val_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1430_, lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v___x_1433_, uint8_t v_val_1434_, lean_object* v_as_1435_, size_t v_sz_1436_, size_t v_i_1437_, lean_object* v_b_1438_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_lt(v_i_1437_, v_sz_1436_);
if (v___x_1440_ == 0)
{
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1431_);
return v_b_1438_;
}
else
{
lean_object* v_snd_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1459_; 
v_snd_1441_ = lean_ctor_get(v_b_1438_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_b_1438_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_b_1438_, 0);
lean_dec(v_unused_1460_);
v___x_1443_ = v_b_1438_;
v_isShared_1444_ = v_isSharedCheck_1459_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_snd_1441_);
lean_dec(v_b_1438_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1459_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_array_uget_borrowed(v_as_1435_, v_i_1437_);
lean_inc(v_snd_1441_);
lean_inc_ref(v___x_1433_);
lean_inc_ref(v___x_1431_);
v___x_1446_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1430_, v___x_1431_, v___x_1432_, v___x_1433_, v_val_1434_, v_a_1445_, v_snd_1441_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1431_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1447_);
v___x_1449_ = v___x_1443_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_snd_1441_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
lean_dec(v_snd_1441_);
v_a_1451_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1452_ = lean_box(0);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_a_1451_);
lean_ctor_set(v___x_1443_, 0, v___x_1452_);
v___x_1454_ = v___x_1443_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_a_1451_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
size_t v___x_1455_; size_t v___x_1456_; 
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_add(v_i_1437_, v___x_1455_);
v_i_1437_ = v___x_1456_;
v_b_1438_ = v___x_1454_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1461_, lean_object* v___x_1462_, lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v_val_1465_, lean_object* v_as_1466_, lean_object* v_sz_1467_, lean_object* v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_val_35222__boxed_1471_; size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_val_35222__boxed_1471_ = lean_unbox(v_val_1465_);
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1467_);
lean_dec(v_sz_1467_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1461_, v___x_1462_, v___x_1463_, v___x_1464_, v_val_35222__boxed_1471_, v_as_1466_, v_sz_boxed_1472_, v_i_boxed_1473_, v_b_1469_);
lean_dec_ref(v_as_1466_);
lean_dec(v___x_1463_);
lean_dec_ref(v_init_1461_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v_val_1479_, lean_object* v_n_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_val_35238__boxed_1483_; lean_object* v_res_1484_; 
v_val_35238__boxed_1483_ = lean_unbox(v_val_1479_);
v_res_1484_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1475_, v___x_1476_, v___x_1477_, v___x_1478_, v_val_35238__boxed_1483_, v_n_1480_, v_b_1481_);
lean_dec_ref(v_n_1480_);
lean_dec(v___x_1477_);
lean_dec_ref(v_init_1475_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1485_, lean_object* v___x_1486_, lean_object* v___x_1487_, uint8_t v_val_1488_, lean_object* v_as_1489_, size_t v_sz_1490_, size_t v_i_1491_, lean_object* v_b_1492_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_lt(v_i_1491_, v_sz_1490_);
if (v___x_1494_ == 0)
{
lean_dec_ref(v___x_1487_);
lean_dec_ref(v___x_1485_);
return v_b_1492_;
}
else
{
lean_object* v_snd_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1513_; 
v_snd_1495_ = lean_ctor_get(v_b_1492_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_b_1492_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_b_1492_, 0);
lean_dec(v_unused_1514_);
v___x_1497_ = v_b_1492_;
v_isShared_1498_ = v_isSharedCheck_1513_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snd_1495_);
lean_dec(v_b_1492_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1513_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_a_1499_; lean_object* v_msg_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v_a_1499_ = lean_array_uget_borrowed(v_as_1489_, v_i_1491_);
v_msg_1500_ = lean_ctor_get(v_a_1499_, 1);
v___x_1501_ = lean_box(0);
lean_inc_ref(v___x_1485_);
v___x_1502_ = l_Lean_FileMap_toPosition(v___x_1485_, v___x_1486_);
v___x_1503_ = 0;
v___x_1504_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1500_);
lean_inc_ref(v___x_1487_);
v___x_1505_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1505_, 0, v___x_1487_);
lean_ctor_set(v___x_1505_, 1, v___x_1502_);
lean_ctor_set(v___x_1505_, 2, v___x_1501_);
lean_ctor_set(v___x_1505_, 3, v___x_1504_);
lean_ctor_set(v___x_1505_, 4, v_msg_1500_);
lean_ctor_set_uint8(v___x_1505_, sizeof(void*)*5, v_val_1488_);
lean_ctor_set_uint8(v___x_1505_, sizeof(void*)*5 + 1, v___x_1503_);
lean_ctor_set_uint8(v___x_1505_, sizeof(void*)*5 + 2, v_val_1488_);
v___x_1506_ = l_Lean_MessageLog_add(v___x_1505_, v_snd_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v___x_1506_);
lean_ctor_set(v___x_1497_, 0, v___x_1501_);
v___x_1508_ = v___x_1497_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
size_t v___x_1509_; size_t v___x_1510_; 
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_add(v_i_1491_, v___x_1509_);
v_i_1491_ = v___x_1510_;
v_b_1492_ = v___x_1508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v_val_1518_, lean_object* v_as_1519_, lean_object* v_sz_1520_, lean_object* v_i_1521_, lean_object* v_b_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_val_35320__boxed_1524_; size_t v_sz_boxed_1525_; size_t v_i_boxed_1526_; lean_object* v_res_1527_; 
v_val_35320__boxed_1524_ = lean_unbox(v_val_1518_);
v_sz_boxed_1525_ = lean_unbox_usize(v_sz_1520_);
lean_dec(v_sz_1520_);
v_i_boxed_1526_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_res_1527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1515_, v___x_1516_, v___x_1517_, v_val_35320__boxed_1524_, v_as_1519_, v_sz_boxed_1525_, v_i_boxed_1526_, v_b_1522_);
lean_dec_ref(v_as_1519_);
lean_dec(v___x_1516_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v___x_1530_, uint8_t v_val_1531_, lean_object* v_as_1532_, size_t v_sz_1533_, size_t v_i_1534_, lean_object* v_b_1535_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_usize_dec_lt(v_i_1534_, v_sz_1533_);
if (v___x_1537_ == 0)
{
lean_dec_ref(v___x_1530_);
lean_dec_ref(v___x_1528_);
return v_b_1535_;
}
else
{
lean_object* v_snd_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1556_; 
v_snd_1538_ = lean_ctor_get(v_b_1535_, 1);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_b_1535_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_b_1535_, 0);
lean_dec(v_unused_1557_);
v___x_1540_ = v_b_1535_;
v_isShared_1541_ = v_isSharedCheck_1556_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_snd_1538_);
lean_dec(v_b_1535_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1556_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_a_1542_; lean_object* v_msg_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v_a_1542_ = lean_array_uget_borrowed(v_as_1532_, v_i_1534_);
v_msg_1543_ = lean_ctor_get(v_a_1542_, 1);
v___x_1544_ = lean_box(0);
lean_inc_ref(v___x_1528_);
v___x_1545_ = l_Lean_FileMap_toPosition(v___x_1528_, v___x_1529_);
v___x_1546_ = 0;
v___x_1547_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1543_);
lean_inc_ref(v___x_1530_);
v___x_1548_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1548_, 0, v___x_1530_);
lean_ctor_set(v___x_1548_, 1, v___x_1545_);
lean_ctor_set(v___x_1548_, 2, v___x_1544_);
lean_ctor_set(v___x_1548_, 3, v___x_1547_);
lean_ctor_set(v___x_1548_, 4, v_msg_1543_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*5, v_val_1531_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*5 + 1, v___x_1546_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*5 + 2, v_val_1531_);
v___x_1549_ = l_Lean_MessageLog_add(v___x_1548_, v_snd_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___x_1549_);
lean_ctor_set(v___x_1540_, 0, v___x_1544_);
v___x_1551_ = v___x_1540_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_add(v_i_1534_, v___x_1552_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1528_, v___x_1529_, v___x_1530_, v_val_1531_, v_as_1532_, v_sz_1533_, v___x_1553_, v___x_1551_);
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1558_, lean_object* v___x_1559_, lean_object* v___x_1560_, lean_object* v_val_1561_, lean_object* v_as_1562_, lean_object* v_sz_1563_, lean_object* v_i_1564_, lean_object* v_b_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v_val_35372__boxed_1567_; size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_val_35372__boxed_1567_ = lean_unbox(v_val_1561_);
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1563_);
lean_dec(v_sz_1563_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1564_);
lean_dec(v_i_1564_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1558_, v___x_1559_, v___x_1560_, v_val_35372__boxed_1567_, v_as_1562_, v_sz_boxed_1568_, v_i_boxed_1569_, v_b_1565_);
lean_dec_ref(v_as_1562_);
lean_dec(v___x_1559_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, uint8_t v_val_1574_, lean_object* v_t_1575_, lean_object* v_init_1576_){
_start:
{
lean_object* v_root_1578_; lean_object* v_tail_1579_; lean_object* v___x_1580_; 
v_root_1578_ = lean_ctor_get(v_t_1575_, 0);
v_tail_1579_ = lean_ctor_get(v_t_1575_, 1);
lean_inc_ref(v___x_1573_);
lean_inc_ref(v___x_1571_);
lean_inc_ref(v_init_1576_);
v___x_1580_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1576_, v___x_1571_, v___x_1572_, v___x_1573_, v_val_1574_, v_root_1578_, v_init_1576_);
lean_dec_ref(v_init_1576_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
lean_dec_ref(v___x_1573_);
lean_dec_ref(v___x_1571_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
return v_a_1581_;
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; lean_object* v_fst_1588_; 
v_a_1582_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_a_1582_);
v_sz_1585_ = lean_array_size(v_tail_1579_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1571_, v___x_1572_, v___x_1573_, v_val_1574_, v_tail_1579_, v_sz_1585_, v___x_1586_, v___x_1584_);
v_fst_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_fst_1588_);
if (lean_obj_tag(v_fst_1588_) == 0)
{
lean_object* v_snd_1589_; 
v_snd_1589_ = lean_ctor_get(v___x_1587_, 1);
lean_inc(v_snd_1589_);
lean_dec_ref(v___x_1587_);
return v_snd_1589_;
}
else
{
lean_object* v_val_1590_; 
lean_dec_ref(v___x_1587_);
v_val_1590_ = lean_ctor_get(v_fst_1588_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v_fst_1588_, 1);
return v_val_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v_val_1594_, lean_object* v_t_1595_, lean_object* v_init_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v_val_35423__boxed_1598_; lean_object* v_res_1599_; 
v_val_35423__boxed_1598_ = lean_unbox(v_val_1594_);
v_res_1599_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1591_, v___x_1592_, v___x_1593_, v_val_35423__boxed_1598_, v_t_1595_, v_init_1596_);
lean_dec_ref(v_t_1595_);
lean_dec(v___x_1592_);
return v_res_1599_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = l_Lean_firstFrontendMacroScope;
v___x_1602_ = lean_nat_add(v___x_1601_, v___x_1600_);
return v___x_1602_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1609_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v___x_1614_, lean_object* v___x_1615_, lean_object* v___x_1616_, size_t v___x_1617_, uint8_t v___x_1618_, lean_object* v_env_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, lean_object* v_a_1622_, lean_object* v_opts_1623_, lean_object* v___x_1624_, lean_object* v_pos_1625_, uint8_t v_val_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v___x_1630_, uint8_t v___x_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_toProcessingContext_1653_; lean_object* v_fileName_1654_; lean_object* v_fileMap_1655_; lean_object* v_env_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; lean_object* v_fileName_1662_; lean_object* v_fileMap_1663_; lean_object* v_currRecDepth_1664_; lean_object* v_ref_1665_; lean_object* v_currNamespace_1666_; lean_object* v_openDecls_1667_; lean_object* v_initHeartbeats_1668_; lean_object* v_maxHeartbeats_1669_; lean_object* v_quotContext_1670_; lean_object* v_currMacroScope_1671_; lean_object* v_cancelTk_x3f_1672_; uint8_t v_suppressElabErrors_1673_; lean_object* v_inheritedTraceOptions_1674_; lean_object* v___y_1675_; uint8_t v___y_1692_; uint8_t v___x_1712_; 
v___x_1634_ = l_Lean_firstFrontendMacroScope;
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1637_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_1638_ = lean_box(0);
lean_inc(v___x_1614_);
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1614_);
lean_ctor_set(v___x_1639_, 1, v___x_1635_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1641_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6);
v___x_1642_ = lean_mk_empty_array_with_capacity(v___x_1615_);
lean_inc_ref(v___x_1642_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_inc_n(v___x_1616_, 2);
v___x_1644_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1642_);
lean_ctor_set(v___x_1644_, 2, v___x_1616_);
lean_ctor_set(v___x_1644_, 3, v___x_1616_);
lean_ctor_set_usize(v___x_1644_, 4, v___x_1617_);
v___x_1645_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1644_, 2);
v___x_1646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1644_);
lean_ctor_set(v___x_1646_, 2, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1647_, 0, v___x_1640_);
lean_ctor_set(v___x_1647_, 1, v___x_1640_);
lean_ctor_set(v___x_1647_, 2, v___x_1644_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*3, v___x_1618_);
v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1616_);
lean_inc_ref(v___x_1648_);
lean_inc_ref(v___x_1620_);
v___x_1649_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1649_, 0, v_env_1619_);
lean_ctor_set(v___x_1649_, 1, v___x_1636_);
lean_ctor_set(v___x_1649_, 2, v___x_1637_);
lean_ctor_set(v___x_1649_, 3, v___x_1639_);
lean_ctor_set(v___x_1649_, 4, v___x_1620_);
lean_ctor_set(v___x_1649_, 5, v___x_1641_);
lean_ctor_set(v___x_1649_, 6, v___x_1646_);
lean_ctor_set(v___x_1649_, 7, v___x_1647_);
lean_ctor_set(v___x_1649_, 8, v___x_1648_);
v___x_1650_ = lean_st_mk_ref(v___x_1649_);
v___x_1651_ = lean_st_ref_get(v___x_1621_);
v___x_1652_ = lean_st_ref_get(v___x_1650_);
v_toProcessingContext_1653_ = lean_ctor_get(v_a_1622_, 0);
v_fileName_1654_ = lean_ctor_get(v_toProcessingContext_1653_, 1);
v_fileMap_1655_ = lean_ctor_get(v_toProcessingContext_1653_, 2);
v_env_1656_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_ref(v_env_1656_);
lean_dec(v___x_1652_);
v___x_1657_ = lean_box(0);
v___x_1658_ = l_Lean_Core_getMaxHeartbeats(v_opts_1623_);
v___x_1659_ = l_Lean_diagnostics;
v___x_1660_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1623_, v___x_1659_);
v___x_1712_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1656_);
lean_dec_ref(v_env_1656_);
if (v___x_1660_ == 0)
{
if (v___x_1712_ == 0)
{
v___y_1692_ = v___x_1631_;
goto v___jp_1691_;
}
else
{
v___y_1692_ = v___x_1660_;
goto v___jp_1691_;
}
}
else
{
v___y_1692_ = v___x_1712_;
goto v___jp_1691_;
}
v___jp_1661_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1676_ = l_Lean_maxRecDepth;
v___x_1677_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1623_, v___x_1676_);
lean_inc(v_currMacroScope_1671_);
lean_inc(v_openDecls_1667_);
lean_inc(v_ref_1665_);
v___x_1678_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1678_, 0, v_fileName_1662_);
lean_ctor_set(v___x_1678_, 1, v_fileMap_1663_);
lean_ctor_set(v___x_1678_, 2, v_opts_1623_);
lean_ctor_set(v___x_1678_, 3, v_currRecDepth_1664_);
lean_ctor_set(v___x_1678_, 4, v___x_1677_);
lean_ctor_set(v___x_1678_, 5, v_ref_1665_);
lean_ctor_set(v___x_1678_, 6, v_currNamespace_1666_);
lean_ctor_set(v___x_1678_, 7, v_openDecls_1667_);
lean_ctor_set(v___x_1678_, 8, v_initHeartbeats_1668_);
lean_ctor_set(v___x_1678_, 9, v_maxHeartbeats_1669_);
lean_ctor_set(v___x_1678_, 10, v_quotContext_1670_);
lean_ctor_set(v___x_1678_, 11, v_currMacroScope_1671_);
lean_ctor_set(v___x_1678_, 12, v_cancelTk_x3f_1672_);
lean_ctor_set(v___x_1678_, 13, v_inheritedTraceOptions_1674_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*14, v___x_1660_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*14 + 1, v_suppressElabErrors_1673_);
v___x_1679_ = l_Lean_Language_SnapshotTree_trace(v___x_1624_, v___x_1678_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref_known(v___x_1678_, 14);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; lean_object* v_traceState_1681_; lean_object* v_traces_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec_ref_known(v___x_1679_, 1);
lean_dec_ref(v___x_1629_);
v___x_1680_ = lean_st_ref_get(v___x_1650_);
lean_dec(v___x_1650_);
v_traceState_1681_ = lean_ctor_get(v___x_1680_, 4);
lean_inc_ref(v_traceState_1681_);
lean_dec(v___x_1680_);
v_traces_1682_ = lean_ctor_get(v_traceState_1681_, 0);
lean_inc_ref(v_traces_1682_);
lean_dec_ref(v_traceState_1681_);
v___x_1683_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1654_);
lean_inc_ref(v_fileMap_1655_);
v___x_1684_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1655_, v_pos_1625_, v_fileName_1654_, v_val_1626_, v_traces_1682_, v___x_1683_);
lean_dec_ref(v_traces_1682_);
v___x_1685_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1686_, 0, v___x_1627_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
lean_ctor_set(v___x_1686_, 2, v___x_1628_);
lean_ctor_set(v___x_1686_, 3, v___x_1620_);
lean_ctor_set_uint8(v___x_1686_, sizeof(void*)*4, v_val_1626_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1648_);
v___x_1688_ = lean_task_pure(v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref_known(v___x_1679_, 1);
lean_dec(v___x_1650_);
lean_dec(v___x_1628_);
lean_dec_ref(v___x_1627_);
lean_dec_ref(v___x_1620_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1629_);
lean_ctor_set(v___x_1689_, 1, v___x_1648_);
v___x_1690_ = lean_task_pure(v___x_1689_);
return v___x_1690_;
}
}
v___jp_1691_:
{
if (v___y_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v_env_1694_; lean_object* v_nextMacroScope_1695_; lean_object* v_ngen_1696_; lean_object* v_auxDeclNGen_1697_; lean_object* v_traceState_1698_; lean_object* v_messages_1699_; lean_object* v_infoState_1700_; lean_object* v_snapshotTasks_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1710_; 
v___x_1693_ = lean_st_ref_take(v___x_1650_);
v_env_1694_ = lean_ctor_get(v___x_1693_, 0);
v_nextMacroScope_1695_ = lean_ctor_get(v___x_1693_, 1);
v_ngen_1696_ = lean_ctor_get(v___x_1693_, 2);
v_auxDeclNGen_1697_ = lean_ctor_get(v___x_1693_, 3);
v_traceState_1698_ = lean_ctor_get(v___x_1693_, 4);
v_messages_1699_ = lean_ctor_get(v___x_1693_, 6);
v_infoState_1700_ = lean_ctor_get(v___x_1693_, 7);
v_snapshotTasks_1701_ = lean_ctor_get(v___x_1693_, 8);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1693_, 5);
lean_dec(v_unused_1711_);
v___x_1703_ = v___x_1693_;
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snapshotTasks_1701_);
lean_inc(v_infoState_1700_);
lean_inc(v_messages_1699_);
lean_inc(v_traceState_1698_);
lean_inc(v_auxDeclNGen_1697_);
lean_inc(v_ngen_1696_);
lean_inc(v_nextMacroScope_1695_);
lean_inc(v_env_1694_);
lean_dec(v___x_1693_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = l_Lean_Kernel_enableDiag(v_env_1694_, v___x_1660_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 5, v___x_1641_);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_nextMacroScope_1695_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_ngen_1696_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_auxDeclNGen_1697_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_traceState_1698_);
lean_ctor_set(v_reuseFailAlloc_1709_, 5, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1709_, 6, v_messages_1699_);
lean_ctor_set(v_reuseFailAlloc_1709_, 7, v_infoState_1700_);
lean_ctor_set(v_reuseFailAlloc_1709_, 8, v_snapshotTasks_1701_);
v___x_1707_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_st_ref_put(v___x_1650_, v___x_1707_);
lean_inc(v___x_1650_);
lean_inc(v___x_1614_);
lean_inc(v___x_1616_);
lean_inc_ref(v_fileMap_1655_);
lean_inc_ref(v_fileName_1654_);
v_fileName_1662_ = v_fileName_1654_;
v_fileMap_1663_ = v_fileMap_1655_;
v_currRecDepth_1664_ = v___x_1616_;
v_ref_1665_ = v___x_1657_;
v_currNamespace_1666_ = v___x_1614_;
v_openDecls_1667_ = v___x_1638_;
v_initHeartbeats_1668_ = v___x_1616_;
v_maxHeartbeats_1669_ = v___x_1658_;
v_quotContext_1670_ = v___x_1614_;
v_currMacroScope_1671_ = v___x_1634_;
v_cancelTk_x3f_1672_ = v___x_1630_;
v_suppressElabErrors_1673_ = v_val_1626_;
v_inheritedTraceOptions_1674_ = v___x_1651_;
v___y_1675_ = v___x_1650_;
goto v___jp_1661_;
}
}
}
else
{
lean_inc(v___x_1650_);
lean_inc(v___x_1614_);
lean_inc(v___x_1616_);
lean_inc_ref(v_fileMap_1655_);
lean_inc_ref(v_fileName_1654_);
v_fileName_1662_ = v_fileName_1654_;
v_fileMap_1663_ = v_fileMap_1655_;
v_currRecDepth_1664_ = v___x_1616_;
v_ref_1665_ = v___x_1657_;
v_currNamespace_1666_ = v___x_1614_;
v_openDecls_1667_ = v___x_1638_;
v_initHeartbeats_1668_ = v___x_1616_;
v_maxHeartbeats_1669_ = v___x_1658_;
v_quotContext_1670_ = v___x_1614_;
v_currMacroScope_1671_ = v___x_1634_;
v_cancelTk_x3f_1672_ = v___x_1630_;
v_suppressElabErrors_1673_ = v_val_1626_;
v_inheritedTraceOptions_1674_ = v___x_1651_;
v___y_1675_ = v___x_1650_;
goto v___jp_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v___x_1713_ = _args[0];
lean_object* v___x_1714_ = _args[1];
lean_object* v___x_1715_ = _args[2];
lean_object* v___x_1716_ = _args[3];
lean_object* v___x_1717_ = _args[4];
lean_object* v_env_1718_ = _args[5];
lean_object* v___x_1719_ = _args[6];
lean_object* v___x_1720_ = _args[7];
lean_object* v_a_1721_ = _args[8];
lean_object* v_opts_1722_ = _args[9];
lean_object* v___x_1723_ = _args[10];
lean_object* v_pos_1724_ = _args[11];
lean_object* v_val_1725_ = _args[12];
lean_object* v___x_1726_ = _args[13];
lean_object* v___x_1727_ = _args[14];
lean_object* v___x_1728_ = _args[15];
lean_object* v___x_1729_ = _args[16];
lean_object* v___x_1730_ = _args[17];
lean_object* v_x_1731_ = _args[18];
lean_object* v___y_1732_ = _args[19];
_start:
{
size_t v___x_35484__boxed_1733_; uint8_t v___x_35485__boxed_1734_; uint8_t v_val_35489__boxed_1735_; uint8_t v___x_35494__boxed_1736_; lean_object* v_res_1737_; 
v___x_35484__boxed_1733_ = lean_unbox_usize(v___x_1716_);
lean_dec(v___x_1716_);
v___x_35485__boxed_1734_ = lean_unbox(v___x_1717_);
v_val_35489__boxed_1735_ = lean_unbox(v_val_1725_);
v___x_35494__boxed_1736_ = lean_unbox(v___x_1730_);
v_res_1737_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v___x_1713_, v___x_1714_, v___x_1715_, v___x_35484__boxed_1733_, v___x_35485__boxed_1734_, v_env_1718_, v___x_1719_, v___x_1720_, v_a_1721_, v_opts_1722_, v___x_1723_, v_pos_1724_, v_val_35489__boxed_1735_, v___x_1726_, v___x_1727_, v___x_1728_, v___x_1729_, v___x_35494__boxed_1736_, v_x_1731_);
lean_dec(v_pos_1724_);
lean_dec_ref(v_a_1721_);
lean_dec(v___x_1720_);
lean_dec(v___x_1714_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1738_, lean_object* v___x_1739_, lean_object* v_parserState_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_toProcessingContext_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_toProcessingContext_1742_ = lean_ctor_get(v_a_1738_, 0);
v___x_1743_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1742_);
v___x_1744_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1742_, v___x_1739_, v_parserState_1740_, v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1745_, lean_object* v___x_1746_, lean_object* v_parserState_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1745_, v___x_1746_, v_parserState_1747_, v_x_1748_);
lean_dec_ref(v_a_1745_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1751_, size_t v_i_1752_, size_t v_stop_1753_, lean_object* v_b_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_eq(v_i_1752_, v_stop_1753_);
if (v___x_1756_ == 0)
{
lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; 
v___f_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
v___x_1758_ = lean_array_uget_borrowed(v_as_1751_, v_i_1752_);
lean_inc(v___x_1758_);
v___x_1759_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1757_, v___x_1758_);
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1752_, v___x_1760_);
v_i_1752_ = v___x_1761_;
v_b_1754_ = v___x_1759_;
goto _start;
}
else
{
return v_b_1754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1763_, lean_object* v_i_1764_, lean_object* v_stop_1765_, lean_object* v_b_1766_, lean_object* v___y_1767_){
_start:
{
size_t v_i_boxed_1768_; size_t v_stop_boxed_1769_; lean_object* v_res_1770_; 
v_i_boxed_1768_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_stop_boxed_1769_ = lean_unbox_usize(v_stop_1765_);
lean_dec(v_stop_1765_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1763_, v_i_boxed_1768_, v_stop_boxed_1769_, v_b_1766_);
lean_dec_ref(v_as_1763_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1771_, lean_object* v_cmds_1772_, lean_object* v_stx_1773_, lean_object* v_newParserState_1774_, lean_object* v_val_1775_, lean_object* v_sync_1776_, lean_object* v_val_1777_, lean_object* v_a_1778_, lean_object* v_oldNext_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v_sync_boxed_1781_; lean_object* v_res_1782_; 
v_sync_boxed_1781_ = lean_unbox(v_sync_1776_);
v_res_1782_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1771_, v_cmds_1772_, v_stx_1773_, v_newParserState_1774_, v_val_1775_, v_sync_boxed_1781_, v_val_1777_, v_a_1778_, v_oldNext_1779_);
lean_dec_ref(v_a_1778_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1783_, lean_object* v_cmds_1784_, lean_object* v_stx_1785_, lean_object* v_newParserState_1786_, lean_object* v_val_1787_, uint8_t v_sync_1788_, lean_object* v_val_1789_, lean_object* v_a_1790_, lean_object* v_oldResult_1791_){
_start:
{
lean_object* v_task_1793_; lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; 
v_task_1793_ = lean_ctor_get(v_val_1783_, 3);
lean_inc_ref(v_task_1793_);
lean_dec_ref(v_val_1783_);
v___x_1794_ = lean_box(v_sync_1788_);
lean_inc_ref(v_a_1790_);
v___f_1795_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1795_, 0, v_oldResult_1791_);
lean_closure_set(v___f_1795_, 1, v_cmds_1784_);
lean_closure_set(v___f_1795_, 2, v_stx_1785_);
lean_closure_set(v___f_1795_, 3, v_newParserState_1786_);
lean_closure_set(v___f_1795_, 4, v_val_1787_);
lean_closure_set(v___f_1795_, 5, v___x_1794_);
lean_closure_set(v___f_1795_, 6, v_val_1789_);
lean_closure_set(v___f_1795_, 7, v_a_1790_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = 1;
v___x_1798_ = l_BaseIO_chainTask___redArg(v_task_1793_, v___f_1795_, v___x_1796_, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1799_, lean_object* v_cmds_1800_, lean_object* v_stx_1801_, lean_object* v_newParserState_1802_, lean_object* v_val_1803_, lean_object* v_sync_1804_, lean_object* v_val_1805_, lean_object* v_a_1806_, lean_object* v_oldResult_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v_sync_boxed_1809_; lean_object* v_res_1810_; 
v_sync_boxed_1809_ = lean_unbox(v_sync_1804_);
v_res_1810_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1799_, v_cmds_1800_, v_stx_1801_, v_newParserState_1802_, v_val_1803_, v_sync_boxed_1809_, v_val_1805_, v_a_1806_, v_oldResult_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1810_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__1));
v___x_1819_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1820_ = l_Lean_Name_append(v___x_1819_, v___x_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__3);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1825_, lean_object* v_val_1826_, lean_object* v_cmds_1827_, lean_object* v_fst_1828_, lean_object* v_fst_1829_, uint8_t v_val_1830_, lean_object* v_a_1831_, lean_object* v_snd_1832_, lean_object* v___x_1833_, uint8_t v___x_1834_, lean_object* v_fst_1835_, lean_object* v_val_1836_, lean_object* v_val_1837_, lean_object* v_val_1838_, lean_object* v_snd_1839_, lean_object* v_prom_1840_, lean_object* v___x_1841_, lean_object* v___f_1842_, lean_object* v___f_1843_, lean_object* v___f_1844_, lean_object* v_pos_1845_, lean_object* v_cmdState_1846_, lean_object* v___x_1847_, lean_object* v_opts_1848_, lean_object* v___x_1849_, lean_object* v_old_x3f_1850_, lean_object* v_parseCancelTk_1851_, lean_object* v_next_x3f_1852_){
_start:
{
lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v_snapshotTasks_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v_traceTask_1861_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; size_t v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v_env_1903_; lean_object* v_messages_1904_; lean_object* v_scopes_1905_; lean_object* v_infoState_1906_; lean_object* v_traceState_1907_; lean_object* v_snapshotTasks_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_reportedCmdState_1911_; size_t v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_reportedCmdState_1968_; size_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; size_t v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2032_; 
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
v_toProcessingContext_2086_ = lean_ctor_get(v_a_1831_, 0);
v_val_2087_ = lean_ctor_get(v_next_x3f_1852_, 0);
v_pos_2088_ = lean_ctor_get(v_fst_1829_, 0);
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
lean_ctor_set(v___x_1862_, 0, v___y_1855_);
lean_ctor_set(v___x_1862_, 1, v___x_1825_);
lean_ctor_set(v___x_1862_, 2, v___y_1860_);
lean_ctor_set(v___x_1862_, 3, v_traceTask_1861_);
v___x_1863_ = lean_array_push(v_snapshotTasks_1858_, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___y_1859_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_io_promise_resolve(v___x_1864_, v_val_1826_);
if (lean_obj_tag(v_next_x3f_1852_) == 1)
{
lean_object* v_val_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_val_1866_ = lean_ctor_get(v_next_x3f_1852_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_next_x3f_1852_, 1);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_array_push(v_cmds_1827_, v_fst_1828_);
v___x_1869_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1867_, v_fst_1829_, v___y_1857_, v_val_1866_, v_val_1830_, v___y_1856_, v___x_1868_, v_a_1831_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
lean_dec_ref(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v_next_x3f_1852_);
lean_dec_ref(v_fst_1829_);
lean_dec(v_fst_1828_);
lean_dec_ref(v_cmds_1827_);
v___x_1870_ = lean_box(0);
return v___x_1870_;
}
}
v___jp_1871_:
{
lean_object* v_snapshotTasks_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_snapshotTasks_1878_ = lean_ctor_get(v___y_1875_, 10);
lean_inc_ref(v_snapshotTasks_1878_);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___y_1873_);
lean_dec(v___y_1873_);
lean_inc_ref(v___y_1876_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___y_1876_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_task_pure(v___x_1880_);
v___y_1855_ = v___y_1872_;
v___y_1856_ = v___y_1874_;
v___y_1857_ = v___y_1875_;
v_snapshotTasks_1858_ = v_snapshotTasks_1878_;
v___y_1859_ = v___y_1876_;
v___y_1860_ = v___y_1877_;
v_traceTask_1861_ = v___x_1881_;
goto v___jp_1854_;
}
v___jp_1882_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_opts_1921_; uint8_t v_hasTrace_1922_; 
v___x_1912_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1904_);
v___x_1913_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1913_, 0, v___y_1910_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
lean_ctor_set(v___x_1913_, 2, v___y_1901_);
lean_ctor_set(v___x_1913_, 3, v_traceState_1907_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*4, v_val_1830_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v_reportedCmdState_1911_);
v___x_1915_ = lean_io_promise_resolve(v___x_1914_, v_val_1837_);
v___x_1916_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1906_);
lean_inc(v___y_1892_);
v___x_1917_ = l_BaseIO_chainTask___redArg(v___x_1916_, v___y_1893_, v___y_1892_, v___x_1834_);
v___x_1918_ = l_Lean_inheritedTraceOptions;
v___x_1919_ = lean_st_ref_get(v___x_1918_);
v___x_1920_ = l_List_head_x21___redArg(v___x_1841_, v_scopes_1905_);
lean_dec(v_scopes_1905_);
lean_dec_ref(v___x_1841_);
v_opts_1921_ = lean_ctor_get(v___x_1920_, 1);
lean_inc_ref(v_opts_1921_);
lean_dec(v___x_1920_);
v_hasTrace_1922_ = lean_ctor_get_uint8(v_opts_1921_, sizeof(void*)*1);
if (v_hasTrace_1922_ == 0)
{
lean_dec_ref(v_opts_1921_);
lean_dec(v___x_1919_);
lean_dec(v___y_1909_);
lean_dec_ref(v_snapshotTasks_1908_);
lean_dec_ref(v_env_1903_);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v_pos_1845_);
lean_dec_ref(v___f_1844_);
lean_dec_ref(v___f_1843_);
lean_dec_ref(v___f_1842_);
lean_dec(v___x_1833_);
v___y_1872_ = v___y_1898_;
v___y_1873_ = v___y_1892_;
v___y_1874_ = v___y_1899_;
v___y_1875_ = v___y_1902_;
v___y_1876_ = v___y_1895_;
v___y_1877_ = v___y_1897_;
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
lean_dec(v___y_1909_);
lean_dec_ref(v_snapshotTasks_1908_);
lean_dec_ref(v_env_1903_);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v_pos_1845_);
lean_dec_ref(v___f_1844_);
lean_dec_ref(v___f_1843_);
lean_dec_ref(v___f_1842_);
lean_dec(v___x_1833_);
v___y_1872_ = v___y_1898_;
v___y_1873_ = v___y_1892_;
v___y_1874_ = v___y_1899_;
v___y_1875_ = v___y_1902_;
v___y_1876_ = v___y_1895_;
v___y_1877_ = v___y_1897_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; 
lean_inc_n(v___y_1892_, 3);
v___x_1925_ = lean_task_map(v___f_1842_, v___y_1896_, v___y_1892_, v___x_1834_);
lean_inc_n(v___y_1897_, 3);
lean_inc_n(v___y_1894_, 2);
lean_inc_n(v___y_1909_, 2);
v___x_1926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1909_);
lean_ctor_set(v___x_1926_, 1, v___y_1894_);
lean_ctor_set(v___x_1926_, 2, v___y_1897_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = lean_task_map(v___f_1843_, v___y_1900_, v___y_1892_, v___x_1834_);
v___x_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1909_);
lean_ctor_set(v___x_1928_, 1, v___y_1894_);
lean_ctor_set(v___x_1928_, 2, v___y_1897_);
lean_ctor_set(v___x_1928_, 3, v___x_1927_);
v___x_1929_ = lean_task_map(v___f_1844_, v___y_1891_, v___y_1892_, v___x_1834_);
v___x_1930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1930_, 0, v___y_1909_);
lean_ctor_set(v___x_1930_, 1, v___y_1894_);
lean_ctor_set(v___x_1930_, 2, v___y_1897_);
lean_ctor_set(v___x_1930_, 3, v___x_1929_);
v___x_1931_ = lean_unsigned_to_nat(3u);
v___x_1932_ = lean_mk_empty_array_with_capacity(v___x_1931_);
v___x_1933_ = lean_array_push(v___x_1932_, v___x_1926_);
v___x_1934_ = lean_array_push(v___x_1933_, v___x_1928_);
v___x_1935_ = lean_array_push(v___x_1934_, v___x_1930_);
v___x_1936_ = l_Array_append___redArg(v___x_1935_, v_snapshotTasks_1908_);
lean_inc_ref(v___y_1895_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1895_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
lean_inc_ref(v___x_1937_);
v___x_1938_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1937_);
v___x_1939_ = lean_box_usize(v___y_1883_);
v___x_1940_ = lean_box(v___x_1834_);
v___x_1941_ = lean_box(v_val_1830_);
v___x_1942_ = lean_box(v___x_1924_);
lean_inc_ref(v_a_1831_);
lean_inc_ref(v___y_1889_);
v___f_1943_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1943_, 0, v___x_1833_);
lean_closure_set(v___f_1943_, 1, v___y_1890_);
lean_closure_set(v___f_1943_, 2, v___y_1885_);
lean_closure_set(v___f_1943_, 3, v___x_1939_);
lean_closure_set(v___f_1943_, 4, v___x_1940_);
lean_closure_set(v___f_1943_, 5, v_env_1903_);
lean_closure_set(v___f_1943_, 6, v___y_1889_);
lean_closure_set(v___f_1943_, 7, v___x_1918_);
lean_closure_set(v___f_1943_, 8, v_a_1831_);
lean_closure_set(v___f_1943_, 9, v_opts_1921_);
lean_closure_set(v___f_1943_, 10, v___x_1937_);
lean_closure_set(v___f_1943_, 11, v_pos_1845_);
lean_closure_set(v___f_1943_, 12, v___x_1941_);
lean_closure_set(v___f_1943_, 13, v___y_1884_);
lean_closure_set(v___f_1943_, 14, v___y_1888_);
lean_closure_set(v___f_1943_, 15, v___y_1887_);
lean_closure_set(v___f_1943_, 16, v___y_1886_);
lean_closure_set(v___f_1943_, 17, v___x_1942_);
v___x_1944_ = lean_io_bind_task(v___x_1938_, v___f_1943_, v___y_1892_, v_val_1830_);
v___y_1855_ = v___y_1898_;
v___y_1856_ = v___y_1899_;
v___y_1857_ = v___y_1902_;
v_snapshotTasks_1858_ = v_snapshotTasks_1908_;
v___y_1859_ = v___y_1895_;
v___y_1860_ = v___y_1897_;
v_traceTask_1861_ = v___x_1944_;
goto v___jp_1854_;
}
}
}
v___jp_1945_:
{
lean_object* v_env_1969_; lean_object* v_messages_1970_; lean_object* v_scopes_1971_; lean_object* v_infoState_1972_; lean_object* v_traceState_1973_; lean_object* v_snapshotTasks_1974_; 
v_env_1969_ = lean_ctor_get(v___y_1965_, 0);
lean_inc_ref(v_env_1969_);
v_messages_1970_ = lean_ctor_get(v___y_1965_, 1);
lean_inc_ref(v_messages_1970_);
v_scopes_1971_ = lean_ctor_get(v___y_1965_, 2);
lean_inc(v_scopes_1971_);
v_infoState_1972_ = lean_ctor_get(v___y_1965_, 8);
lean_inc_ref(v_infoState_1972_);
v_traceState_1973_ = lean_ctor_get(v___y_1965_, 9);
lean_inc_ref(v_traceState_1973_);
v_snapshotTasks_1974_ = lean_ctor_get(v___y_1965_, 10);
lean_inc_ref(v_snapshotTasks_1974_);
v___y_1883_ = v___y_1946_;
v___y_1884_ = v___y_1948_;
v___y_1885_ = v___y_1947_;
v___y_1886_ = v___y_1950_;
v___y_1887_ = v___y_1949_;
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
v___y_1899_ = v___y_1962_;
v___y_1900_ = v___y_1963_;
v___y_1901_ = v___y_1964_;
v___y_1902_ = v___y_1965_;
v_env_1903_ = v_env_1969_;
v_messages_1904_ = v_messages_1970_;
v_scopes_1905_ = v_scopes_1971_;
v_infoState_1906_ = v_infoState_1972_;
v_traceState_1907_ = v_traceState_1973_;
v_snapshotTasks_1908_ = v_snapshotTasks_1974_;
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
lean_ctor_set(v___x_2000_, 1, v_val_1836_);
lean_inc_ref(v___y_1993_);
lean_inc_n(v_pos_1845_, 2);
lean_inc_ref(v_cmds_1827_);
lean_inc(v_fst_1828_);
v___x_2001_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1828_, v_cmds_1827_, v_cmdState_1846_, v_pos_1845_, v___x_2000_, v___y_1993_, v_a_1831_);
v___x_2002_ = lean_box(v_val_1830_);
v___x_2003_ = lean_box(v___x_1834_);
lean_inc_ref(v_a_1831_);
lean_inc(v___y_1977_);
lean_inc_ref(v___x_1841_);
lean_inc_ref(v___x_2001_);
lean_inc_ref(v___y_1982_);
lean_inc_ref(v___y_1978_);
v___f_2004_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2004_, 0, v___y_1978_);
lean_closure_set(v___f_2004_, 1, v___y_1982_);
lean_closure_set(v___f_2004_, 2, v___x_2002_);
lean_closure_set(v___f_2004_, 3, v_val_1838_);
lean_closure_set(v___f_2004_, 4, v___x_2001_);
lean_closure_set(v___f_2004_, 5, v___x_1841_);
lean_closure_set(v___f_2004_, 6, v___y_1977_);
lean_closure_set(v___f_2004_, 7, v___x_2003_);
lean_closure_set(v___f_2004_, 8, v_a_1831_);
lean_closure_set(v___f_2004_, 9, v_pos_1845_);
lean_closure_set(v___f_2004_, 10, v___x_1847_);
v___x_2005_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1848_, v___x_1849_);
if (v___x_2005_ == 0)
{
lean_dec(v___y_1996_);
lean_inc_ref(v___x_2001_);
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1979_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1985_;
v___y_1956_ = v___f_2004_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___x_2001_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1998_;
v_reportedCmdState_1968_ = v___x_2001_;
goto v___jp_1945_;
}
else
{
uint8_t v___x_2006_; 
lean_inc(v_fst_1828_);
v___x_2006_ = l_Lean_Parser_isTerminalCommand(v_fst_1828_);
if (v___x_2006_ == 0)
{
if (v___x_2005_ == 0)
{
lean_dec(v___y_1996_);
lean_inc_ref(v___x_2001_);
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1979_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1985_;
v___y_1956_ = v___f_2004_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___x_2001_;
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
v___x_2013_ = lean_mk_empty_array_with_capacity(v___y_1996_);
lean_dec(v___y_1996_);
lean_inc_ref(v___x_2013_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_inc_n(v___y_1985_, 3);
v___x_2015_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
lean_ctor_set(v___x_2015_, 2, v___y_1985_);
lean_ctor_set(v___x_2015_, 3, v___y_1985_);
lean_ctor_set_usize(v___x_2015_, 4, v___y_1990_);
v___x_2016_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2015_, 2);
v___x_2017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2015_);
lean_ctor_set(v___x_2017_, 2, v___x_2016_);
v___x_2018_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2019_ = l_Lean_Options_empty;
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_mk_empty_array_with_capacity(v___y_1985_);
lean_inc_ref_n(v___x_2021_, 2);
lean_inc_n(v___x_1833_, 2);
v___x_2022_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___x_2019_);
lean_ctor_set(v___x_2022_, 2, v___x_1833_);
lean_ctor_set(v___x_2022_, 3, v___x_2020_);
lean_ctor_set(v___x_2022_, 4, v___x_2020_);
lean_ctor_set(v___x_2022_, 5, v___x_2021_);
lean_ctor_set(v___x_2022_, 6, v___x_2021_);
lean_ctor_set(v___x_2022_, 7, v___x_2020_);
lean_ctor_set(v___x_2022_, 8, v___x_2020_);
lean_ctor_set(v___x_2022_, 9, v___x_2020_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*10, v_val_1830_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*10 + 1, v_val_1830_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*10 + 2, v_val_1830_);
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_2020_);
v___x_2024_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2025_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2026_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1833_);
v___x_2027_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2028_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
lean_ctor_set(v___x_2028_, 2, v___x_2015_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*3, v___x_1834_);
v___x_2029_ = lean_box(0);
lean_inc_ref(v___y_1987_);
v___x_2030_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2030_, 0, v_env_2007_);
lean_ctor_set(v___x_2030_, 1, v___x_2017_);
lean_ctor_set(v___x_2030_, 2, v___x_2023_);
lean_ctor_set(v___x_2030_, 3, v___x_2016_);
lean_ctor_set(v___x_2030_, 4, v___x_2024_);
lean_ctor_set(v___x_2030_, 5, v___y_1985_);
lean_ctor_set(v___x_2030_, 6, v___x_2025_);
lean_ctor_set(v___x_2030_, 7, v___x_2026_);
lean_ctor_set(v___x_2030_, 8, v___x_2028_);
lean_ctor_set(v___x_2030_, 9, v___y_1987_);
lean_ctor_set(v___x_2030_, 10, v___x_2021_);
lean_ctor_set(v___x_2030_, 11, v___x_2029_);
v___y_1883_ = v___y_1976_;
v___y_1884_ = v___y_1978_;
v___y_1885_ = v___y_1977_;
v___y_1886_ = v___y_1979_;
v___y_1887_ = v___y_1980_;
v___y_1888_ = v___y_1981_;
v___y_1889_ = v___y_1982_;
v___y_1890_ = v___y_1983_;
v___y_1891_ = v___y_1984_;
v___y_1892_ = v___y_1985_;
v___y_1893_ = v___f_2004_;
v___y_1894_ = v___y_1986_;
v___y_1895_ = v___y_1988_;
v___y_1896_ = v___y_1989_;
v___y_1897_ = v___y_1991_;
v___y_1898_ = v___y_1992_;
v___y_1899_ = v___y_1993_;
v___y_1900_ = v___y_1994_;
v___y_1901_ = v___y_1995_;
v___y_1902_ = v___x_2001_;
v_env_1903_ = v_env_2007_;
v_messages_1904_ = v_messages_2008_;
v_scopes_1905_ = v_scopes_2009_;
v_infoState_1906_ = v_infoState_2010_;
v_traceState_1907_ = v_traceState_2011_;
v_snapshotTasks_1908_ = v_snapshotTasks_2012_;
v___y_1909_ = v___y_1997_;
v___y_1910_ = v___y_1998_;
v_reportedCmdState_1911_ = v___x_2030_;
goto v___jp_1882_;
}
}
else
{
lean_dec(v___y_1996_);
lean_inc_ref(v___x_2001_);
v___y_1946_ = v___y_1976_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1980_;
v___y_1950_ = v___y_1979_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1985_;
v___y_1956_ = v___f_2004_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1989_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___x_2001_;
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
v___x_2033_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1832_);
v___x_2034_ = l_IO_CancelToken_new();
v___x_2035_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1833_);
v___x_2036_ = l_Lean_Name_str___override(v___x_1833_, v___x_2035_);
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
v___x_2051_ = l_Lean_Name_toString(v___x_2050_, v___x_1834_);
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
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*4, v_val_1830_);
v___x_2057_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2058_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2058_, 0, v___x_2051_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
lean_ctor_set(v___x_2058_, 2, v___x_2052_);
lean_ctor_set(v___x_2058_, 3, v___x_2055_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*4, v_val_1830_);
lean_inc(v_fst_1835_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_fst_1835_);
v___x_2060_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2059_);
lean_inc_ref(v___x_2034_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2034_);
v___x_2062_ = l_IO_Promise_result_x21___redArg(v_val_1836_);
lean_inc_ref(v___x_2062_);
lean_inc(v___x_2060_);
lean_inc_ref_n(v___x_2059_, 3);
v___x_2063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2059_);
lean_ctor_set(v___x_2063_, 1, v___x_2060_);
lean_ctor_set(v___x_2063_, 2, v___x_2061_);
lean_ctor_set(v___x_2063_, 3, v___x_2062_);
v___x_2064_ = l_IO_Promise_result_x21___redArg(v_val_1837_);
lean_inc_ref(v___x_2064_);
lean_inc_n(v___x_1825_, 3);
v___x_2065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2059_);
lean_ctor_set(v___x_2065_, 1, v___x_1825_);
lean_ctor_set(v___x_2065_, 2, v___x_2052_);
lean_ctor_set(v___x_2065_, 3, v___x_2064_);
v___x_2066_ = l_IO_Promise_result_x21___redArg(v_val_1838_);
lean_inc_ref(v___x_2066_);
v___x_2067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2059_);
lean_ctor_set(v___x_2067_, 1, v___x_1825_);
lean_ctor_set(v___x_2067_, 2, v___x_2052_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
v___x_2068_ = l_IO_Promise_result_x21___redArg(v_val_1826_);
v___x_2069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2052_);
lean_ctor_set(v___x_2069_, 1, v___x_1825_);
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
lean_ctor_set(v___x_2071_, 1, v_fst_1835_);
lean_ctor_set(v___x_2071_, 2, v_snd_1839_);
lean_ctor_set(v___x_2071_, 3, v___x_2070_);
lean_ctor_set(v___x_2071_, 4, v___y_2032_);
v___x_2072_ = lean_io_promise_resolve(v___x_2071_, v_prom_1840_);
if (lean_obj_tag(v_old_x3f_1850_) == 0)
{
lean_inc_ref(v___x_2058_);
lean_inc_ref(v___x_2051_);
v___y_1976_ = v___x_2054_;
v___y_1977_ = v___x_2042_;
v___y_1978_ = v___x_2051_;
v___y_1979_ = v___x_2052_;
v___y_1980_ = v___x_2058_;
v___y_1981_ = v___x_2052_;
v___y_1982_ = v___x_2055_;
v___y_1983_ = v___x_2053_;
v___y_1984_ = v___x_2066_;
v___y_1985_ = v___x_2042_;
v___y_1986_ = v___x_2060_;
v___y_1987_ = v___x_2055_;
v___y_1988_ = v___x_2058_;
v___y_1989_ = v___x_2062_;
v___y_1990_ = v___x_2054_;
v___y_1991_ = v___x_2052_;
v___y_1992_ = v___x_2052_;
v___y_1993_ = v___x_2034_;
v___y_1994_ = v___x_2064_;
v___y_1995_ = v___x_2052_;
v___y_1996_ = v___x_2053_;
v___y_1997_ = v___x_2059_;
v___y_1998_ = v___x_2051_;
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
lean_inc_ref(v___x_2058_);
lean_inc_ref(v___x_2051_);
v___y_1976_ = v___x_2054_;
v___y_1977_ = v___x_2042_;
v___y_1978_ = v___x_2051_;
v___y_1979_ = v___x_2052_;
v___y_1980_ = v___x_2058_;
v___y_1981_ = v___x_2052_;
v___y_1982_ = v___x_2055_;
v___y_1983_ = v___x_2053_;
v___y_1984_ = v___x_2066_;
v___y_1985_ = v___x_2042_;
v___y_1986_ = v___x_2060_;
v___y_1987_ = v___x_2055_;
v___y_1988_ = v___x_2058_;
v___y_1989_ = v___x_2062_;
v___y_1990_ = v___x_2054_;
v___y_1991_ = v___x_2052_;
v___y_1992_ = v___x_2052_;
v___y_1993_ = v___x_2034_;
v___y_1994_ = v___x_2064_;
v___y_1995_ = v___x_2052_;
v___y_1996_ = v___x_2053_;
v___y_1997_ = v___x_2059_;
v___y_1998_ = v___x_2051_;
v___y_1999_ = v___x_2082_;
goto v___jp_1975_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_2098_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_2100_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_cmds_2101_, lean_object* v_fst_2102_, lean_object* v_fst_2103_, uint8_t v_val_2104_, lean_object* v_a_2105_, lean_object* v_snd_2106_, lean_object* v___x_2107_, uint8_t v___x_2108_, lean_object* v_prom_2109_, lean_object* v___x_2110_, lean_object* v___f_2111_, lean_object* v___f_2112_, lean_object* v___f_2113_, lean_object* v_pos_2114_, lean_object* v_cmdState_2115_, lean_object* v___x_2116_, lean_object* v_opts_2117_, lean_object* v_old_x3f_2118_, lean_object* v_parseCancelTk_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v_snapshotTasks_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v_traceTask_2134_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; size_t v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v_env_2180_; lean_object* v_messages_2181_; lean_object* v_scopes_2182_; lean_object* v_infoState_2183_; lean_object* v_traceState_2184_; lean_object* v_snapshotTasks_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v_reportedCmdState_2188_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; size_t v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v_reportedCmdState_2247_; lean_object* v___x_2254_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; size_t v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; size_t v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v_fst_2392_; lean_object* v_snd_2393_; uint8_t v___x_2405_; 
v___x_2121_ = lean_io_promise_new();
v___x_2122_ = lean_io_promise_new();
v___x_2123_ = lean_io_promise_new();
v___x_2124_ = lean_io_promise_new();
v___x_2254_ = l_Lean_internal_cmdlineSnapshots;
v___x_2405_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2117_, v___x_2254_);
if (v___x_2405_ == 0)
{
lean_inc_ref(v_fst_2103_);
lean_inc(v_fst_2102_);
v_fst_2392_ = v_fst_2102_;
v_snd_2393_ = v_fst_2103_;
goto v___jp_2391_;
}
else
{
uint8_t v___x_2406_; 
lean_inc(v_fst_2102_);
v___x_2406_ = l_Lean_Parser_isTerminalCommand(v_fst_2102_);
if (v___x_2406_ == 0)
{
if (v___x_2405_ == 0)
{
lean_inc_ref(v_fst_2103_);
lean_inc(v_fst_2102_);
v_fst_2392_ = v_fst_2102_;
v_snd_2393_ = v_fst_2103_;
goto v___jp_2391_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_box(0);
v___x_2408_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2392_ = v___x_2407_;
v_snd_2393_ = v___x_2408_;
goto v___jp_2391_;
}
}
else
{
lean_inc_ref(v_fst_2103_);
lean_inc(v_fst_2102_);
v_fst_2392_ = v_fst_2102_;
v_snd_2393_ = v_fst_2103_;
goto v___jp_2391_;
}
}
v___jp_2125_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2135_, 0, v___y_2126_);
lean_ctor_set(v___x_2135_, 1, v___y_2127_);
lean_ctor_set(v___x_2135_, 2, v___y_2131_);
lean_ctor_set(v___x_2135_, 3, v_traceTask_2134_);
v___x_2136_ = lean_array_push(v_snapshotTasks_2129_, v___x_2135_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___y_2133_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_io_promise_resolve(v___x_2137_, v___x_2124_);
lean_dec(v___x_2124_);
if (lean_obj_tag(v___y_2132_) == 1)
{
lean_object* v_val_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_val_2139_ = lean_ctor_get(v___y_2132_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v___y_2132_, 1);
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_array_push(v_cmds_2101_, v_fst_2102_);
v___x_2142_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2140_, v_fst_2103_, v___y_2128_, v_val_2139_, v_val_2104_, v___y_2130_, v___x_2141_, v_a_2105_);
return v___x_2142_;
}
else
{
lean_object* v___x_2143_; 
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v___y_2128_);
lean_dec_ref(v_fst_2103_);
lean_dec(v_fst_2102_);
lean_dec_ref(v_cmds_2101_);
v___x_2143_ = lean_box(0);
return v___x_2143_;
}
}
v___jp_2144_:
{
lean_object* v_snapshotTasks_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_snapshotTasks_2153_ = lean_ctor_get(v___y_2148_, 10);
lean_inc_ref(v_snapshotTasks_2153_);
v___x_2154_ = lean_mk_empty_array_with_capacity(v___y_2146_);
lean_dec(v___y_2146_);
lean_inc_ref(v___y_2152_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___y_2152_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_task_pure(v___x_2155_);
v___y_2126_ = v___y_2145_;
v___y_2127_ = v___y_2147_;
v___y_2128_ = v___y_2148_;
v_snapshotTasks_2129_ = v_snapshotTasks_2153_;
v___y_2130_ = v___y_2150_;
v___y_2131_ = v___y_2149_;
v___y_2132_ = v___y_2151_;
v___y_2133_ = v___y_2152_;
v_traceTask_2134_ = v___x_2156_;
goto v___jp_2125_;
}
v___jp_2157_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_opts_2198_; uint8_t v_hasTrace_2199_; 
v___x_2189_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2181_);
v___x_2190_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2190_, 0, v___y_2176_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
lean_ctor_set(v___x_2190_, 2, v___y_2170_);
lean_ctor_set(v___x_2190_, 3, v_traceState_2184_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*4, v_val_2104_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_reportedCmdState_2188_);
v___x_2192_ = lean_io_promise_resolve(v___x_2191_, v___x_2122_);
lean_dec(v___x_2122_);
v___x_2193_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2183_);
lean_inc(v___y_2178_);
v___x_2194_ = l_BaseIO_chainTask___redArg(v___x_2193_, v___y_2186_, v___y_2178_, v___x_2108_);
v___x_2195_ = l_Lean_inheritedTraceOptions;
v___x_2196_ = lean_st_ref_get(v___x_2195_);
v___x_2197_ = l_List_head_x21___redArg(v___x_2110_, v_scopes_2182_);
lean_dec(v_scopes_2182_);
lean_dec_ref(v___x_2110_);
v_opts_2198_ = lean_ctor_get(v___x_2197_, 1);
lean_inc_ref(v_opts_2198_);
lean_dec(v___x_2197_);
v_hasTrace_2199_ = lean_ctor_get_uint8(v_opts_2198_, sizeof(void*)*1);
if (v_hasTrace_2199_ == 0)
{
lean_dec_ref(v_opts_2198_);
lean_dec(v___x_2196_);
lean_dec_ref(v_snapshotTasks_2185_);
lean_dec_ref(v_env_2180_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec(v_pos_2114_);
lean_dec_ref(v___f_2113_);
lean_dec_ref(v___f_2112_);
lean_dec_ref(v___f_2111_);
lean_dec(v___x_2107_);
v___y_2145_ = v___y_2177_;
v___y_2146_ = v___y_2178_;
v___y_2147_ = v___y_2166_;
v___y_2148_ = v___y_2179_;
v___y_2149_ = v___y_2171_;
v___y_2150_ = v___y_2172_;
v___y_2151_ = v___y_2173_;
v___y_2152_ = v___y_2187_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2196_, v_opts_2198_, v___x_2200_);
lean_dec(v___x_2196_);
if (v___x_2201_ == 0)
{
lean_dec_ref(v_opts_2198_);
lean_dec_ref(v_snapshotTasks_2185_);
lean_dec_ref(v_env_2180_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec(v_pos_2114_);
lean_dec_ref(v___f_2113_);
lean_dec_ref(v___f_2112_);
lean_dec_ref(v___f_2111_);
lean_dec(v___x_2107_);
v___y_2145_ = v___y_2177_;
v___y_2146_ = v___y_2178_;
v___y_2147_ = v___y_2166_;
v___y_2148_ = v___y_2179_;
v___y_2149_ = v___y_2171_;
v___y_2150_ = v___y_2172_;
v___y_2151_ = v___y_2173_;
v___y_2152_ = v___y_2187_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___f_2220_; lean_object* v___x_2221_; 
lean_inc_n(v___y_2178_, 3);
v___x_2202_ = lean_task_map(v___f_2111_, v___y_2169_, v___y_2178_, v___x_2108_);
lean_inc_n(v___y_2171_, 3);
lean_inc_n(v___y_2168_, 2);
lean_inc_n(v___y_2174_, 2);
v___x_2203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2203_, 0, v___y_2174_);
lean_ctor_set(v___x_2203_, 1, v___y_2168_);
lean_ctor_set(v___x_2203_, 2, v___y_2171_);
lean_ctor_set(v___x_2203_, 3, v___x_2202_);
v___x_2204_ = lean_task_map(v___f_2112_, v___y_2167_, v___y_2178_, v___x_2108_);
v___x_2205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2205_, 0, v___y_2174_);
lean_ctor_set(v___x_2205_, 1, v___y_2168_);
lean_ctor_set(v___x_2205_, 2, v___y_2171_);
lean_ctor_set(v___x_2205_, 3, v___x_2204_);
v___x_2206_ = lean_task_map(v___f_2113_, v___y_2175_, v___y_2178_, v___x_2108_);
v___x_2207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2174_);
lean_ctor_set(v___x_2207_, 1, v___y_2168_);
lean_ctor_set(v___x_2207_, 2, v___y_2171_);
lean_ctor_set(v___x_2207_, 3, v___x_2206_);
v___x_2208_ = lean_unsigned_to_nat(3u);
v___x_2209_ = lean_mk_empty_array_with_capacity(v___x_2208_);
v___x_2210_ = lean_array_push(v___x_2209_, v___x_2203_);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2205_);
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2207_);
v___x_2213_ = l_Array_append___redArg(v___x_2212_, v_snapshotTasks_2185_);
lean_inc_ref(v___y_2187_);
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2187_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
lean_inc_ref(v___x_2214_);
v___x_2215_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2214_);
v___x_2216_ = lean_box_usize(v___y_2161_);
v___x_2217_ = lean_box(v___x_2108_);
v___x_2218_ = lean_box(v_val_2104_);
v___x_2219_ = lean_box(v___x_2201_);
lean_inc_ref(v_a_2105_);
lean_inc_ref(v___y_2163_);
v___f_2220_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2220_, 0, v___x_2107_);
lean_closure_set(v___f_2220_, 1, v___y_2165_);
lean_closure_set(v___f_2220_, 2, v___y_2158_);
lean_closure_set(v___f_2220_, 3, v___x_2216_);
lean_closure_set(v___f_2220_, 4, v___x_2217_);
lean_closure_set(v___f_2220_, 5, v_env_2180_);
lean_closure_set(v___f_2220_, 6, v___y_2163_);
lean_closure_set(v___f_2220_, 7, v___x_2195_);
lean_closure_set(v___f_2220_, 8, v_a_2105_);
lean_closure_set(v___f_2220_, 9, v_opts_2198_);
lean_closure_set(v___f_2220_, 10, v___x_2214_);
lean_closure_set(v___f_2220_, 11, v_pos_2114_);
lean_closure_set(v___f_2220_, 12, v___x_2218_);
lean_closure_set(v___f_2220_, 13, v___y_2162_);
lean_closure_set(v___f_2220_, 14, v___y_2160_);
lean_closure_set(v___f_2220_, 15, v___y_2159_);
lean_closure_set(v___f_2220_, 16, v___y_2164_);
lean_closure_set(v___f_2220_, 17, v___x_2219_);
v___x_2221_ = lean_io_bind_task(v___x_2215_, v___f_2220_, v___y_2178_, v_val_2104_);
v___y_2126_ = v___y_2177_;
v___y_2127_ = v___y_2166_;
v___y_2128_ = v___y_2179_;
v_snapshotTasks_2129_ = v_snapshotTasks_2185_;
v___y_2130_ = v___y_2172_;
v___y_2131_ = v___y_2171_;
v___y_2132_ = v___y_2173_;
v___y_2133_ = v___y_2187_;
v_traceTask_2134_ = v___x_2221_;
goto v___jp_2125_;
}
}
}
v___jp_2222_:
{
lean_object* v_env_2248_; lean_object* v_messages_2249_; lean_object* v_scopes_2250_; lean_object* v_infoState_2251_; lean_object* v_traceState_2252_; lean_object* v_snapshotTasks_2253_; 
v_env_2248_ = lean_ctor_get(v___y_2244_, 0);
lean_inc_ref(v_env_2248_);
v_messages_2249_ = lean_ctor_get(v___y_2244_, 1);
lean_inc_ref(v_messages_2249_);
v_scopes_2250_ = lean_ctor_get(v___y_2244_, 2);
lean_inc(v_scopes_2250_);
v_infoState_2251_ = lean_ctor_get(v___y_2244_, 8);
lean_inc_ref(v_infoState_2251_);
v_traceState_2252_ = lean_ctor_get(v___y_2244_, 9);
lean_inc_ref(v_traceState_2252_);
v_snapshotTasks_2253_ = lean_ctor_get(v___y_2244_, 10);
lean_inc_ref(v_snapshotTasks_2253_);
v___y_2158_ = v___y_2223_;
v___y_2159_ = v___y_2224_;
v___y_2160_ = v___y_2225_;
v___y_2161_ = v___y_2226_;
v___y_2162_ = v___y_2228_;
v___y_2163_ = v___y_2227_;
v___y_2164_ = v___y_2230_;
v___y_2165_ = v___y_2229_;
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
v_env_2180_ = v_env_2248_;
v_messages_2181_ = v_messages_2249_;
v_scopes_2182_ = v_scopes_2250_;
v_infoState_2183_ = v_infoState_2251_;
v_traceState_2184_ = v_traceState_2252_;
v_snapshotTasks_2185_ = v_snapshotTasks_2253_;
v___y_2186_ = v___y_2245_;
v___y_2187_ = v___y_2246_;
v_reportedCmdState_2188_ = v_reportedCmdState_2247_;
goto v___jp_2157_;
}
v___jp_2255_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; uint8_t v___x_2287_; 
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___y_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2121_);
lean_inc_ref(v___y_2268_);
lean_inc_n(v_pos_2114_, 2);
lean_inc_ref(v_cmds_2101_);
lean_inc(v_fst_2102_);
v___x_2283_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2102_, v_cmds_2101_, v_cmdState_2115_, v_pos_2114_, v___x_2282_, v___y_2268_, v_a_2105_);
v___x_2284_ = lean_box(v_val_2104_);
v___x_2285_ = lean_box(v___x_2108_);
lean_inc_ref(v_a_2105_);
lean_inc(v___y_2256_);
lean_inc_ref(v___x_2110_);
lean_inc_ref(v___x_2283_);
lean_inc_ref(v___y_2260_);
lean_inc_ref(v___y_2261_);
v___f_2286_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 13, 11);
lean_closure_set(v___f_2286_, 0, v___y_2261_);
lean_closure_set(v___f_2286_, 1, v___y_2260_);
lean_closure_set(v___f_2286_, 2, v___x_2284_);
lean_closure_set(v___f_2286_, 3, v___x_2123_);
lean_closure_set(v___f_2286_, 4, v___x_2283_);
lean_closure_set(v___f_2286_, 5, v___x_2110_);
lean_closure_set(v___f_2286_, 6, v___y_2256_);
lean_closure_set(v___f_2286_, 7, v___x_2285_);
lean_closure_set(v___f_2286_, 8, v_a_2105_);
lean_closure_set(v___f_2286_, 9, v_pos_2114_);
lean_closure_set(v___f_2286_, 10, v___x_2116_);
v___x_2287_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2117_, v___x_2254_);
if (v___x_2287_ == 0)
{
lean_dec(v___y_2279_);
lean_inc_ref(v___x_2283_);
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2262_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2270_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2268_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2273_;
v___y_2240_ = v___y_2275_;
v___y_2241_ = v___y_2274_;
v___y_2242_ = v___y_2276_;
v___y_2243_ = v___y_2278_;
v___y_2244_ = v___x_2283_;
v___y_2245_ = v___f_2286_;
v___y_2246_ = v___y_2280_;
v_reportedCmdState_2247_ = v___x_2283_;
goto v___jp_2222_;
}
else
{
uint8_t v___x_2288_; 
lean_inc(v_fst_2102_);
v___x_2288_ = l_Lean_Parser_isTerminalCommand(v_fst_2102_);
if (v___x_2288_ == 0)
{
if (v___x_2287_ == 0)
{
lean_dec(v___y_2279_);
lean_inc_ref(v___x_2283_);
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2262_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2270_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2268_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2273_;
v___y_2240_ = v___y_2275_;
v___y_2241_ = v___y_2274_;
v___y_2242_ = v___y_2276_;
v___y_2243_ = v___y_2278_;
v___y_2244_ = v___x_2283_;
v___y_2245_ = v___f_2286_;
v___y_2246_ = v___y_2280_;
v_reportedCmdState_2247_ = v___x_2283_;
goto v___jp_2222_;
}
else
{
lean_object* v_env_2289_; lean_object* v_messages_2290_; lean_object* v_scopes_2291_; lean_object* v_infoState_2292_; lean_object* v_traceState_2293_; lean_object* v_snapshotTasks_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_env_2289_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref_n(v_env_2289_, 2);
v_messages_2290_ = lean_ctor_get(v___x_2283_, 1);
lean_inc_ref(v_messages_2290_);
v_scopes_2291_ = lean_ctor_get(v___x_2283_, 2);
lean_inc(v_scopes_2291_);
v_infoState_2292_ = lean_ctor_get(v___x_2283_, 8);
lean_inc_ref(v_infoState_2292_);
v_traceState_2293_ = lean_ctor_get(v___x_2283_, 9);
lean_inc_ref(v_traceState_2293_);
v_snapshotTasks_2294_ = lean_ctor_get(v___x_2283_, 10);
lean_inc_ref(v_snapshotTasks_2294_);
v___x_2295_ = lean_mk_empty_array_with_capacity(v___y_2279_);
lean_dec(v___y_2279_);
lean_inc_ref(v___x_2295_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_inc_n(v___y_2278_, 3);
v___x_2297_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v___x_2295_);
lean_ctor_set(v___x_2297_, 2, v___y_2278_);
lean_ctor_set(v___x_2297_, 3, v___y_2278_);
lean_ctor_set_usize(v___x_2297_, 4, v___y_2272_);
v___x_2298_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2297_, 2);
v___x_2299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
lean_ctor_set(v___x_2299_, 2, v___x_2298_);
v___x_2300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2301_ = l_Lean_Options_empty;
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_mk_empty_array_with_capacity(v___y_2278_);
lean_inc_ref_n(v___x_2303_, 2);
lean_inc_n(v___x_2107_, 2);
v___x_2304_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2304_, 0, v___x_2300_);
lean_ctor_set(v___x_2304_, 1, v___x_2301_);
lean_ctor_set(v___x_2304_, 2, v___x_2107_);
lean_ctor_set(v___x_2304_, 3, v___x_2302_);
lean_ctor_set(v___x_2304_, 4, v___x_2302_);
lean_ctor_set(v___x_2304_, 5, v___x_2303_);
lean_ctor_set(v___x_2304_, 6, v___x_2303_);
lean_ctor_set(v___x_2304_, 7, v___x_2302_);
lean_ctor_set(v___x_2304_, 8, v___x_2302_);
lean_ctor_set(v___x_2304_, 9, v___x_2302_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*10, v_val_2104_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*10 + 1, v_val_2104_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*10 + 2, v_val_2104_);
v___x_2305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v___x_2302_);
v___x_2306_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2307_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2308_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2107_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2310_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
lean_ctor_set(v___x_2310_, 2, v___x_2297_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3, v___x_2108_);
v___x_2311_ = lean_box(0);
lean_inc_ref(v___y_2277_);
v___x_2312_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2312_, 0, v_env_2289_);
lean_ctor_set(v___x_2312_, 1, v___x_2299_);
lean_ctor_set(v___x_2312_, 2, v___x_2305_);
lean_ctor_set(v___x_2312_, 3, v___x_2298_);
lean_ctor_set(v___x_2312_, 4, v___x_2306_);
lean_ctor_set(v___x_2312_, 5, v___y_2278_);
lean_ctor_set(v___x_2312_, 6, v___x_2307_);
lean_ctor_set(v___x_2312_, 7, v___x_2308_);
lean_ctor_set(v___x_2312_, 8, v___x_2310_);
lean_ctor_set(v___x_2312_, 9, v___y_2277_);
lean_ctor_set(v___x_2312_, 10, v___x_2303_);
lean_ctor_set(v___x_2312_, 11, v___x_2311_);
v___y_2158_ = v___y_2256_;
v___y_2159_ = v___y_2257_;
v___y_2160_ = v___y_2258_;
v___y_2161_ = v___y_2259_;
v___y_2162_ = v___y_2261_;
v___y_2163_ = v___y_2260_;
v___y_2164_ = v___y_2262_;
v___y_2165_ = v___y_2263_;
v___y_2166_ = v___y_2264_;
v___y_2167_ = v___y_2265_;
v___y_2168_ = v___y_2266_;
v___y_2169_ = v___y_2267_;
v___y_2170_ = v___y_2270_;
v___y_2171_ = v___y_2269_;
v___y_2172_ = v___y_2268_;
v___y_2173_ = v___y_2271_;
v___y_2174_ = v___y_2273_;
v___y_2175_ = v___y_2275_;
v___y_2176_ = v___y_2274_;
v___y_2177_ = v___y_2276_;
v___y_2178_ = v___y_2278_;
v___y_2179_ = v___x_2283_;
v_env_2180_ = v_env_2289_;
v_messages_2181_ = v_messages_2290_;
v_scopes_2182_ = v_scopes_2291_;
v_infoState_2183_ = v_infoState_2292_;
v_traceState_2184_ = v_traceState_2293_;
v_snapshotTasks_2185_ = v_snapshotTasks_2294_;
v___y_2186_ = v___f_2286_;
v___y_2187_ = v___y_2280_;
v_reportedCmdState_2188_ = v___x_2312_;
goto v___jp_2157_;
}
}
else
{
lean_dec(v___y_2279_);
lean_inc_ref(v___x_2283_);
v___y_2223_ = v___y_2256_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2262_;
v___y_2231_ = v___y_2264_;
v___y_2232_ = v___y_2265_;
v___y_2233_ = v___y_2266_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2270_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2268_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2273_;
v___y_2240_ = v___y_2275_;
v___y_2241_ = v___y_2274_;
v___y_2242_ = v___y_2276_;
v___y_2243_ = v___y_2278_;
v___y_2244_ = v___x_2283_;
v___y_2245_ = v___f_2286_;
v___y_2246_ = v___y_2280_;
v_reportedCmdState_2247_ = v___x_2283_;
goto v___jp_2222_;
}
}
}
v___jp_2313_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2319_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2106_);
v___x_2320_ = l_IO_CancelToken_new();
v___x_2321_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2107_);
v___x_2322_ = l_Lean_Name_str___override(v___x_2107_, v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2324_ = l_Lean_Name_str___override(v___x_2322_, v___x_2323_);
v___x_2325_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2326_ = l_Lean_Name_str___override(v___x_2324_, v___x_2325_);
v___x_2327_ = l_Lean_Name_str___override(v___x_2326_, v___x_2323_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = l_Lean_Name_num___override(v___x_2327_, v___x_2328_);
v___x_2330_ = l_Lean_Name_str___override(v___x_2329_, v___x_2323_);
v___x_2331_ = l_Lean_Name_str___override(v___x_2330_, v___x_2325_);
v___x_2332_ = l_Lean_Name_str___override(v___x_2331_, v___x_2323_);
v___x_2333_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2334_ = l_Lean_Name_str___override(v___x_2332_, v___x_2333_);
v___x_2335_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2336_ = l_Lean_Name_str___override(v___x_2334_, v___x_2335_);
v___x_2337_ = l_Lean_Name_toString(v___x_2336_, v___x_2108_);
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_unsigned_to_nat(32u);
v___x_2340_ = lean_mk_empty_array_with_capacity(v___x_2339_);
lean_dec_ref(v___x_2340_);
v___x_2341_ = ((size_t)5ULL);
v___x_2342_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2337_, 2);
v___x_2343_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2343_, 0, v___x_2337_);
lean_ctor_set(v___x_2343_, 1, v___x_2319_);
lean_ctor_set(v___x_2343_, 2, v___x_2338_);
lean_ctor_set(v___x_2343_, 3, v___x_2342_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*4, v_val_2104_);
v___x_2344_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2345_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2337_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_ctor_set(v___x_2345_, 2, v___x_2338_);
lean_ctor_set(v___x_2345_, 3, v___x_2342_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*4, v_val_2104_);
lean_inc(v___y_2316_);
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___y_2316_);
v___x_2347_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2346_);
lean_inc_ref(v___x_2320_);
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2320_);
v___x_2349_ = l_IO_Promise_result_x21___redArg(v___x_2121_);
lean_inc_ref(v___x_2349_);
lean_inc(v___x_2347_);
lean_inc_ref_n(v___x_2346_, 3);
v___x_2350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2346_);
lean_ctor_set(v___x_2350_, 1, v___x_2347_);
lean_ctor_set(v___x_2350_, 2, v___x_2348_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
v___x_2351_ = l_IO_Promise_result_x21___redArg(v___x_2122_);
lean_inc_ref(v___x_2351_);
lean_inc_n(v___y_2315_, 3);
v___x_2352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2346_);
lean_ctor_set(v___x_2352_, 1, v___y_2315_);
lean_ctor_set(v___x_2352_, 2, v___x_2338_);
lean_ctor_set(v___x_2352_, 3, v___x_2351_);
v___x_2353_ = l_IO_Promise_result_x21___redArg(v___x_2123_);
lean_inc_ref(v___x_2353_);
v___x_2354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2346_);
lean_ctor_set(v___x_2354_, 1, v___y_2315_);
lean_ctor_set(v___x_2354_, 2, v___x_2338_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
v___x_2355_ = l_IO_Promise_result_x21___redArg(v___x_2124_);
v___x_2356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2338_);
lean_ctor_set(v___x_2356_, 1, v___y_2315_);
lean_ctor_set(v___x_2356_, 2, v___x_2338_);
lean_ctor_set(v___x_2356_, 3, v___x_2355_);
lean_inc_ref(v___x_2345_);
v___x_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2345_);
lean_ctor_set(v___x_2357_, 1, v___x_2350_);
lean_ctor_set(v___x_2357_, 2, v___x_2352_);
lean_ctor_set(v___x_2357_, 3, v___x_2354_);
lean_ctor_set(v___x_2357_, 4, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2343_);
lean_ctor_set(v___x_2358_, 1, v___y_2316_);
lean_ctor_set(v___x_2358_, 2, v___y_2314_);
lean_ctor_set(v___x_2358_, 3, v___x_2357_);
lean_ctor_set(v___x_2358_, 4, v___y_2318_);
v___x_2359_ = lean_io_promise_resolve(v___x_2358_, v_prom_2109_);
if (lean_obj_tag(v_old_x3f_2118_) == 0)
{
lean_inc_ref(v___x_2337_);
lean_inc_ref(v___x_2345_);
v___y_2256_ = v___x_2328_;
v___y_2257_ = v___x_2345_;
v___y_2258_ = v___x_2338_;
v___y_2259_ = v___x_2341_;
v___y_2260_ = v___x_2342_;
v___y_2261_ = v___x_2337_;
v___y_2262_ = v___x_2338_;
v___y_2263_ = v___x_2339_;
v___y_2264_ = v___y_2315_;
v___y_2265_ = v___x_2351_;
v___y_2266_ = v___x_2347_;
v___y_2267_ = v___x_2349_;
v___y_2268_ = v___x_2320_;
v___y_2269_ = v___x_2338_;
v___y_2270_ = v___x_2338_;
v___y_2271_ = v___y_2317_;
v___y_2272_ = v___x_2341_;
v___y_2273_ = v___x_2346_;
v___y_2274_ = v___x_2337_;
v___y_2275_ = v___x_2353_;
v___y_2276_ = v___x_2338_;
v___y_2277_ = v___x_2342_;
v___y_2278_ = v___x_2328_;
v___y_2279_ = v___x_2339_;
v___y_2280_ = v___x_2345_;
v___y_2281_ = v___x_2338_;
goto v___jp_2255_;
}
else
{
lean_object* v_val_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2371_; 
v_val_2360_ = lean_ctor_get(v_old_x3f_2118_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_old_x3f_2118_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2362_ = v_old_x3f_2118_;
v_isShared_2363_ = v_isSharedCheck_2371_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_val_2360_);
lean_dec(v_old_x3f_2118_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2371_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_elabSnap_2364_; lean_object* v_stx_2365_; lean_object* v_elabSnap_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v_elabSnap_2364_ = lean_ctor_get(v_val_2360_, 3);
lean_inc_ref(v_elabSnap_2364_);
v_stx_2365_ = lean_ctor_get(v_val_2360_, 1);
lean_inc(v_stx_2365_);
lean_dec(v_val_2360_);
v_elabSnap_2366_ = lean_ctor_get(v_elabSnap_2364_, 1);
lean_inc_ref(v_elabSnap_2366_);
lean_dec_ref(v_elabSnap_2364_);
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v_stx_2365_);
lean_ctor_set(v___x_2367_, 1, v_elabSnap_2366_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2367_);
v___x_2369_ = v___x_2362_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_inc_ref(v___x_2337_);
lean_inc_ref(v___x_2345_);
v___y_2256_ = v___x_2328_;
v___y_2257_ = v___x_2345_;
v___y_2258_ = v___x_2338_;
v___y_2259_ = v___x_2341_;
v___y_2260_ = v___x_2342_;
v___y_2261_ = v___x_2337_;
v___y_2262_ = v___x_2338_;
v___y_2263_ = v___x_2339_;
v___y_2264_ = v___y_2315_;
v___y_2265_ = v___x_2351_;
v___y_2266_ = v___x_2347_;
v___y_2267_ = v___x_2349_;
v___y_2268_ = v___x_2320_;
v___y_2269_ = v___x_2338_;
v___y_2270_ = v___x_2338_;
v___y_2271_ = v___y_2317_;
v___y_2272_ = v___x_2341_;
v___y_2273_ = v___x_2346_;
v___y_2274_ = v___x_2337_;
v___y_2275_ = v___x_2353_;
v___y_2276_ = v___x_2338_;
v___y_2277_ = v___x_2342_;
v___y_2278_ = v___x_2328_;
v___y_2279_ = v___x_2339_;
v___y_2280_ = v___x_2345_;
v___y_2281_ = v___x_2369_;
goto v___jp_2255_;
}
}
}
}
v___jp_2372_:
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2375_);
lean_inc(v_fst_2102_);
v___x_2377_ = l_Lean_Parser_isTerminalCommand(v_fst_2102_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v_toProcessingContext_2379_; lean_object* v_pos_2380_; lean_object* v_endPos_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2378_ = lean_io_promise_new();
v_toProcessingContext_2379_ = lean_ctor_get(v_a_2105_, 0);
v_pos_2380_ = lean_ctor_get(v_fst_2103_, 0);
v_endPos_2381_ = lean_ctor_get(v_toProcessingContext_2379_, 3);
lean_inc(v___x_2378_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2378_);
v___x_2383_ = lean_box(0);
lean_inc(v_endPos_2381_);
lean_inc(v_pos_2380_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v_pos_2380_);
lean_ctor_set(v___x_2384_, 1, v_endPos_2381_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_parseCancelTk_2119_);
v___x_2387_ = l_IO_Promise_result_x21___redArg(v___x_2378_);
lean_dec(v___x_2378_);
v___x_2388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2383_);
lean_ctor_set(v___x_2388_, 1, v___x_2385_);
lean_ctor_set(v___x_2388_, 2, v___x_2386_);
lean_ctor_set(v___x_2388_, 3, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
v___y_2314_ = v___y_2373_;
v___y_2315_ = v___x_2376_;
v___y_2316_ = v___y_2374_;
v___y_2317_ = v___x_2382_;
v___y_2318_ = v___x_2389_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2390_; 
lean_dec_ref(v_parseCancelTk_2119_);
v___x_2390_ = lean_box(0);
v___y_2314_ = v___y_2373_;
v___y_2315_ = v___x_2376_;
v___y_2316_ = v___y_2374_;
v___y_2317_ = v___x_2390_;
v___y_2318_ = v___x_2390_;
goto v___jp_2313_;
}
}
v___jp_2391_:
{
lean_object* v___x_2394_; 
lean_inc(v_fst_2102_);
v___x_2394_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2102_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_box(0);
v___y_2373_ = v_snd_2393_;
v___y_2374_ = v_fst_2392_;
v___y_2375_ = v___x_2395_;
goto v___jp_2372_;
}
else
{
lean_object* v_val_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2404_; 
v_val_2396_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2398_ = v___x_2394_;
v_isShared_2399_ = v_isSharedCheck_2404_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_val_2396_);
lean_dec(v___x_2394_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2404_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2402_; 
lean_inc(v_val_2396_);
v___x_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2400_, 0, v_val_2396_);
lean_ctor_set(v___x_2400_, 1, v_val_2396_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2400_);
v___x_2402_ = v___x_2398_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
v___y_2373_ = v_snd_2393_;
v___y_2374_ = v_fst_2392_;
v___y_2375_ = v___x_2402_;
goto v___jp_2372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_cmds_2409_ = _args[0];
lean_object* v_fst_2410_ = _args[1];
lean_object* v_fst_2411_ = _args[2];
lean_object* v_val_2412_ = _args[3];
lean_object* v_a_2413_ = _args[4];
lean_object* v_snd_2414_ = _args[5];
lean_object* v___x_2415_ = _args[6];
lean_object* v___x_2416_ = _args[7];
lean_object* v_prom_2417_ = _args[8];
lean_object* v___x_2418_ = _args[9];
lean_object* v___f_2419_ = _args[10];
lean_object* v___f_2420_ = _args[11];
lean_object* v___f_2421_ = _args[12];
lean_object* v_pos_2422_ = _args[13];
lean_object* v_cmdState_2423_ = _args[14];
lean_object* v___x_2424_ = _args[15];
lean_object* v_opts_2425_ = _args[16];
lean_object* v_old_x3f_2426_ = _args[17];
lean_object* v_parseCancelTk_2427_ = _args[18];
lean_object* v___y_2428_ = _args[19];
_start:
{
uint8_t v_val_36124__boxed_2429_; uint8_t v___x_36127__boxed_2430_; lean_object* v_res_2431_; 
v_val_36124__boxed_2429_ = lean_unbox(v_val_2412_);
v___x_36127__boxed_2430_ = lean_unbox(v___x_2416_);
v_res_2431_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_cmds_2409_, v_fst_2410_, v_fst_2411_, v_val_36124__boxed_2429_, v_a_2413_, v_snd_2414_, v___x_2415_, v___x_36127__boxed_2430_, v_prom_2417_, v___x_2418_, v___f_2419_, v___f_2420_, v___f_2421_, v_pos_2422_, v_cmdState_2423_, v___x_2424_, v_opts_2425_, v_old_x3f_2426_, v_parseCancelTk_2427_);
lean_dec_ref(v_opts_2425_);
lean_dec(v_prom_2417_);
lean_dec_ref(v_a_2413_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2434_, lean_object* v_parserState_2435_, lean_object* v_cmdState_2436_, lean_object* v_prom_2437_, uint8_t v_sync_2438_, lean_object* v_parseCancelTk_2439_, lean_object* v_cmds_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v___y_2446_; lean_object* v_toSnapshot_2448_; lean_object* v_stx_2449_; lean_object* v_parserState_2450_; lean_object* v_elabSnap_2451_; lean_object* v_val_2452_; lean_object* v_newParserState_2453_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; uint8_t v___y_2494_; uint8_t v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; uint8_t v___y_2519_; uint8_t v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v_fst_2529_; lean_object* v_snd_2530_; lean_object* v___y_2543_; lean_object* v___y_2544_; uint8_t v___y_2545_; lean_object* v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___x_2624_; 
v___f_2484_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0));
v___f_2485_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1));
v___f_2486_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___x_2487_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2488_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2624_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
if (lean_obj_tag(v_old_x3f_2434_) == 1)
{
lean_object* v_val_2657_; lean_object* v_nextCmdSnap_x3f_2658_; 
v_val_2657_ = lean_ctor_get(v_old_x3f_2434_, 0);
v_nextCmdSnap_x3f_2658_ = lean_ctor_get(v_val_2657_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_2658_) == 0)
{
goto v___jp_2625_;
}
else
{
lean_object* v_toSnapshot_2659_; lean_object* v_stx_2660_; lean_object* v_parserState_2661_; lean_object* v_elabSnap_2662_; lean_object* v_val_2663_; lean_object* v___x_2664_; 
v_toSnapshot_2659_ = lean_ctor_get(v_val_2657_, 0);
v_stx_2660_ = lean_ctor_get(v_val_2657_, 1);
v_parserState_2661_ = lean_ctor_get(v_val_2657_, 2);
v_elabSnap_2662_ = lean_ctor_get(v_val_2657_, 3);
v_val_2663_ = lean_ctor_get(v_nextCmdSnap_x3f_2658_, 0);
lean_inc(v_val_2663_);
v___x_2664_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2663_);
if (lean_obj_tag(v___x_2664_) == 1)
{
lean_object* v_val_2665_; lean_object* v_nextCmdSnap_x3f_2666_; 
v_val_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_val_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v_nextCmdSnap_x3f_2666_ = lean_ctor_get(v_val_2665_, 4);
lean_inc(v_nextCmdSnap_x3f_2666_);
lean_dec(v_val_2665_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2666_) == 0)
{
goto v___jp_2625_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_val_2667_ = lean_ctor_get(v_nextCmdSnap_x3f_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2666_, 1);
v___x_2668_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_2667_);
if (lean_obj_tag(v___x_2668_) == 1)
{
lean_object* v_val_2669_; lean_object* v_parserState_2670_; lean_object* v_pos_2671_; uint8_t v___x_2672_; 
v_val_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v_parserState_2670_ = lean_ctor_get(v_val_2669_, 2);
lean_inc_ref(v_parserState_2670_);
lean_dec(v_val_2669_);
v_pos_2671_ = lean_ctor_get(v_parserState_2670_, 0);
lean_inc(v_pos_2671_);
lean_dec_ref(v_parserState_2670_);
v___x_2672_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2671_, v_a_2441_);
lean_dec(v_pos_2671_);
if (v___x_2672_ == 0)
{
goto v___jp_2625_;
}
else
{
lean_inc(v_val_2663_);
lean_inc_ref(v_elabSnap_2662_);
lean_inc_ref_n(v_parserState_2661_, 2);
lean_inc(v_stx_2660_);
lean_inc_ref(v_toSnapshot_2659_);
lean_dec_ref_known(v_old_x3f_2434_, 1);
lean_dec_ref(v_parseCancelTk_2439_);
lean_dec_ref(v_cmdState_2436_);
lean_dec_ref(v_parserState_2435_);
v_toSnapshot_2448_ = v_toSnapshot_2659_;
v_stx_2449_ = v_stx_2660_;
v_parserState_2450_ = v_parserState_2661_;
v_elabSnap_2451_ = v_elabSnap_2662_;
v_val_2452_ = v_val_2663_;
v_newParserState_2453_ = v_parserState_2661_;
goto v___jp_2447_;
}
}
else
{
lean_dec(v___x_2668_);
goto v___jp_2625_;
}
}
}
else
{
lean_dec(v___x_2664_);
goto v___jp_2625_;
}
}
}
else
{
goto v___jp_2625_;
}
v___jp_2443_:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_box(0);
return v___x_2444_;
}
v___jp_2445_:
{
goto v___jp_2443_;
}
v___jp_2447_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_resultSnap_2456_; lean_object* v_task_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2480_; 
v___x_2454_ = lean_io_promise_new();
v___x_2455_ = l_IO_CancelToken_new();
v_resultSnap_2456_ = lean_ctor_get(v_elabSnap_2451_, 2);
lean_inc_ref(v_resultSnap_2456_);
v_task_2457_ = lean_ctor_get(v_resultSnap_2456_, 3);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_resultSnap_2456_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; 
v_unused_2481_ = lean_ctor_get(v_resultSnap_2456_, 2);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_resultSnap_2456_, 1);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_resultSnap_2456_, 0);
lean_dec(v_unused_2483_);
v___x_2459_ = v_resultSnap_2456_;
v_isShared_2460_ = v_isSharedCheck_2480_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_task_2457_);
lean_dec(v_resultSnap_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2480_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; lean_object* v___x_2465_; lean_object* v_toProcessingContext_2466_; lean_object* v_pos_2467_; lean_object* v_endPos_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2461_ = lean_box(v_sync_2438_);
lean_inc_ref(v_a_2441_);
lean_inc_ref(v___x_2455_);
lean_inc(v___x_2454_);
lean_inc_ref(v_newParserState_2453_);
lean_inc(v_stx_2449_);
v___f_2462_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2462_, 0, v_val_2452_);
lean_closure_set(v___f_2462_, 1, v_cmds_2440_);
lean_closure_set(v___f_2462_, 2, v_stx_2449_);
lean_closure_set(v___f_2462_, 3, v_newParserState_2453_);
lean_closure_set(v___f_2462_, 4, v___x_2454_);
lean_closure_set(v___f_2462_, 5, v___x_2461_);
lean_closure_set(v___f_2462_, 6, v___x_2455_);
lean_closure_set(v___f_2462_, 7, v_a_2441_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = 1;
v___x_2465_ = l_BaseIO_chainTask___redArg(v_task_2457_, v___f_2462_, v___x_2463_, v___x_2464_);
v_toProcessingContext_2466_ = lean_ctor_get(v_a_2441_, 0);
v_pos_2467_ = lean_ctor_get(v_newParserState_2453_, 0);
lean_inc(v_pos_2467_);
lean_dec_ref(v_newParserState_2453_);
v_endPos_2468_ = lean_ctor_get(v_toProcessingContext_2466_, 3);
v___x_2469_ = lean_box(0);
lean_inc(v_endPos_2468_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_pos_2467_);
lean_ctor_set(v___x_2470_, 1, v_endPos_2468_);
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2455_);
v___x_2473_ = l_IO_Promise_result_x21___redArg(v___x_2454_);
lean_dec(v___x_2454_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 3, v___x_2473_);
lean_ctor_set(v___x_2459_, 2, v___x_2472_);
lean_ctor_set(v___x_2459_, 1, v___x_2471_);
lean_ctor_set(v___x_2459_, 0, v___x_2469_);
v___x_2475_ = v___x_2459_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2477_, 0, v_toSnapshot_2448_);
lean_ctor_set(v___x_2477_, 1, v_stx_2449_);
lean_ctor_set(v___x_2477_, 2, v_parserState_2450_);
lean_ctor_set(v___x_2477_, 3, v_elabSnap_2451_);
lean_ctor_set(v___x_2477_, 4, v___x_2476_);
v___x_2478_ = lean_io_promise_resolve(v___x_2477_, v_prom_2437_);
lean_dec(v_prom_2437_);
return v___x_2478_;
}
}
}
v___jp_2489_:
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2506_);
v___x_2508_ = l_Lean_Parser_isTerminalCommand(v___y_2500_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_io_promise_new();
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
v___x_2511_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2507_, v___y_2493_, v_cmds_2440_, v___y_2502_, v___y_2492_, v___y_2494_, v_a_2441_, v___y_2490_, v___y_2503_, v___y_2495_, v___y_2504_, v___y_2497_, v___y_2491_, v___y_2499_, v___y_2498_, v_prom_2437_, v___x_2487_, v___f_2486_, v___f_2485_, v___f_2484_, v___y_2496_, v_cmdState_2436_, v___x_2488_, v___y_2505_, v___y_2501_, v_old_x3f_2434_, v_parseCancelTk_2439_, v___x_2510_);
lean_dec_ref(v___y_2505_);
lean_dec(v_prom_2437_);
lean_dec(v___y_2491_);
lean_dec(v___y_2493_);
v___y_2446_ = v___x_2511_;
goto v___jp_2445_;
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_box(0);
v___x_2513_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2507_, v___y_2493_, v_cmds_2440_, v___y_2502_, v___y_2492_, v___y_2494_, v_a_2441_, v___y_2490_, v___y_2503_, v___y_2495_, v___y_2504_, v___y_2497_, v___y_2491_, v___y_2499_, v___y_2498_, v_prom_2437_, v___x_2487_, v___f_2486_, v___f_2485_, v___f_2484_, v___y_2496_, v_cmdState_2436_, v___x_2488_, v___y_2505_, v___y_2501_, v_old_x3f_2434_, v_parseCancelTk_2439_, v___x_2512_);
lean_dec_ref(v___y_2505_);
lean_dec(v_prom_2437_);
lean_dec(v___y_2491_);
lean_dec(v___y_2493_);
v___y_2446_ = v___x_2513_;
goto v___jp_2445_;
}
}
v___jp_2514_:
{
lean_object* v___x_2531_; 
lean_inc(v___y_2528_);
v___x_2531_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2528_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_box(0);
v___y_2490_ = v___y_2515_;
v___y_2491_ = v___y_2516_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2518_;
v___y_2494_ = v___y_2519_;
v___y_2495_ = v___y_2520_;
v___y_2496_ = v___y_2521_;
v___y_2497_ = v___y_2522_;
v___y_2498_ = v_snd_2530_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2528_;
v___y_2501_ = v___y_2524_;
v___y_2502_ = v___y_2525_;
v___y_2503_ = v___y_2526_;
v___y_2504_ = v_fst_2529_;
v___y_2505_ = v___y_2527_;
v___y_2506_ = v___x_2532_;
goto v___jp_2489_;
}
else
{
lean_object* v_val_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2541_; 
v_val_2533_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2535_ = v___x_2531_;
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_val_2533_);
lean_dec(v___x_2531_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2541_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
lean_inc(v_val_2533_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_val_2533_);
lean_ctor_set(v___x_2537_, 1, v_val_2533_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2537_);
v___x_2539_ = v___x_2535_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
v___y_2490_ = v___y_2515_;
v___y_2491_ = v___y_2516_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2518_;
v___y_2494_ = v___y_2519_;
v___y_2495_ = v___y_2520_;
v___y_2496_ = v___y_2521_;
v___y_2497_ = v___y_2522_;
v___y_2498_ = v_snd_2530_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2528_;
v___y_2501_ = v___y_2524_;
v___y_2502_ = v___y_2525_;
v___y_2503_ = v___y_2526_;
v___y_2504_ = v_fst_2529_;
v___y_2505_ = v___y_2527_;
v___y_2506_ = v___x_2539_;
goto v___jp_2489_;
}
}
}
}
v___jp_2542_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2546_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2547_ = l_Lean_Name_str___override(v___y_2544_, v___x_2546_);
v___x_2548_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2549_ = l_Lean_Name_str___override(v___x_2547_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2551_ = l_Lean_Name_str___override(v___x_2549_, v___x_2550_);
v___x_2552_ = l_Lean_Name_str___override(v___x_2551_, v___x_2548_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = l_Lean_Name_num___override(v___x_2552_, v___x_2553_);
v___x_2555_ = l_Lean_Name_str___override(v___x_2554_, v___x_2548_);
v___x_2556_ = l_Lean_Name_str___override(v___x_2555_, v___x_2550_);
v___x_2557_ = l_Lean_Name_str___override(v___x_2556_, v___x_2548_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2559_ = l_Lean_Name_str___override(v___x_2557_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2561_ = l_Lean_Name_str___override(v___x_2559_, v___x_2560_);
v___x_2562_ = l_Lean_Name_toString(v___x_2561_, v___y_2545_);
v___x_2563_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2566_ = 0;
v___x_2567_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2562_);
lean_ctor_set(v___x_2567_, 1, v___x_2563_);
lean_ctor_set(v___x_2567_, 2, v___x_2564_);
lean_ctor_set(v___x_2567_, 3, v___x_2565_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*4, v___x_2566_);
v___x_2568_ = lean_box(0);
v___x_2569_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
lean_inc_ref_n(v___x_2567_, 3);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2567_);
lean_ctor_set(v___x_2570_, 1, v_cmdState_2436_);
v___x_2571_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2564_, v___x_2570_);
v___x_2572_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2564_, v___x_2567_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4);
v___x_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2567_);
lean_ctor_set(v___x_2574_, 1, v___x_2569_);
lean_ctor_set(v___x_2574_, 2, v___x_2571_);
lean_ctor_set(v___x_2574_, 3, v___x_2572_);
lean_ctor_set(v___x_2574_, 4, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2567_);
lean_ctor_set(v___x_2575_, 1, v___x_2568_);
lean_ctor_set(v___x_2575_, 2, v___y_2543_);
lean_ctor_set(v___x_2575_, 3, v___x_2574_);
lean_ctor_set(v___x_2575_, 4, v___x_2564_);
v___x_2576_ = lean_io_promise_resolve(v___x_2575_, v_prom_2437_);
lean_dec(v_prom_2437_);
v___x_2577_ = lean_box(0);
return v___x_2577_;
}
v___jp_2578_:
{
v___y_2543_ = v___y_2579_;
v___y_2544_ = v___y_2580_;
v___y_2545_ = v___y_2581_;
goto v___jp_2542_;
}
v___jp_2583_:
{
uint8_t v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = l_IO_CancelToken_isSet(v_parseCancelTk_2439_);
v___x_2595_ = 1;
if (v___x_2594_ == 0)
{
lean_dec(v___y_2592_);
if (v_sync_2438_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2596_ = lean_io_promise_new();
v___x_2597_ = lean_io_promise_new();
v___x_2598_ = lean_io_promise_new();
v___x_2599_ = lean_io_promise_new();
v___x_2600_ = l_Lean_internal_cmdlineSnapshots;
v___x_2601_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2593_, v___x_2600_);
lean_dec_ref(v___y_2593_);
if (v___x_2601_ == 0)
{
lean_inc(v___y_2591_);
v___y_2515_ = v___y_2585_;
v___y_2516_ = v___x_2597_;
v___y_2517_ = v___y_2586_;
v___y_2518_ = v___x_2599_;
v___y_2519_ = v___x_2594_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___y_2584_;
v___y_2522_ = v___x_2596_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___x_2600_;
v___y_2525_ = v___y_2587_;
v___y_2526_ = v___y_2588_;
v___y_2527_ = v___y_2589_;
v___y_2528_ = v___y_2591_;
v_fst_2529_ = v___y_2591_;
v_snd_2530_ = v___y_2590_;
goto v___jp_2514_;
}
else
{
uint8_t v___x_2602_; 
lean_inc(v___y_2591_);
v___x_2602_ = l_Lean_Parser_isTerminalCommand(v___y_2591_);
if (v___x_2602_ == 0)
{
if (v___x_2601_ == 0)
{
lean_inc(v___y_2591_);
v___y_2515_ = v___y_2585_;
v___y_2516_ = v___x_2597_;
v___y_2517_ = v___y_2586_;
v___y_2518_ = v___x_2599_;
v___y_2519_ = v___x_2594_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___y_2584_;
v___y_2522_ = v___x_2596_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___x_2600_;
v___y_2525_ = v___y_2587_;
v___y_2526_ = v___y_2588_;
v___y_2527_ = v___y_2589_;
v___y_2528_ = v___y_2591_;
v_fst_2529_ = v___y_2591_;
v_snd_2530_ = v___y_2590_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec_ref(v___y_2590_);
v___x_2603_ = lean_box(0);
v___x_2604_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2515_ = v___y_2585_;
v___y_2516_ = v___x_2597_;
v___y_2517_ = v___y_2586_;
v___y_2518_ = v___x_2599_;
v___y_2519_ = v___x_2594_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___y_2584_;
v___y_2522_ = v___x_2596_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___x_2600_;
v___y_2525_ = v___y_2587_;
v___y_2526_ = v___y_2588_;
v___y_2527_ = v___y_2589_;
v___y_2528_ = v___y_2591_;
v_fst_2529_ = v___x_2603_;
v_snd_2530_ = v___x_2604_;
goto v___jp_2514_;
}
}
else
{
lean_inc(v___y_2591_);
v___y_2515_ = v___y_2585_;
v___y_2516_ = v___x_2597_;
v___y_2517_ = v___y_2586_;
v___y_2518_ = v___x_2599_;
v___y_2519_ = v___x_2594_;
v___y_2520_ = v___x_2595_;
v___y_2521_ = v___y_2584_;
v___y_2522_ = v___x_2596_;
v___y_2523_ = v___x_2598_;
v___y_2524_ = v___x_2600_;
v___y_2525_ = v___y_2587_;
v___y_2526_ = v___y_2588_;
v___y_2527_ = v___y_2589_;
v___y_2528_ = v___y_2591_;
v_fst_2529_ = v___y_2591_;
v_snd_2530_ = v___y_2590_;
goto v___jp_2514_;
}
}
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
v___x_2605_ = lean_box(v___x_2594_);
v___x_2606_ = lean_box(v___x_2595_);
lean_inc_ref(v_a_2441_);
v___f_2607_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 20, 19);
lean_closure_set(v___f_2607_, 0, v_cmds_2440_);
lean_closure_set(v___f_2607_, 1, v___y_2587_);
lean_closure_set(v___f_2607_, 2, v___y_2586_);
lean_closure_set(v___f_2607_, 3, v___x_2605_);
lean_closure_set(v___f_2607_, 4, v_a_2441_);
lean_closure_set(v___f_2607_, 5, v___y_2585_);
lean_closure_set(v___f_2607_, 6, v___y_2588_);
lean_closure_set(v___f_2607_, 7, v___x_2606_);
lean_closure_set(v___f_2607_, 8, v_prom_2437_);
lean_closure_set(v___f_2607_, 9, v___x_2487_);
lean_closure_set(v___f_2607_, 10, v___f_2486_);
lean_closure_set(v___f_2607_, 11, v___f_2485_);
lean_closure_set(v___f_2607_, 12, v___f_2484_);
lean_closure_set(v___f_2607_, 13, v___y_2584_);
lean_closure_set(v___f_2607_, 14, v_cmdState_2436_);
lean_closure_set(v___f_2607_, 15, v___x_2488_);
lean_closure_set(v___f_2607_, 16, v___y_2589_);
lean_closure_set(v___f_2607_, 17, v_old_x3f_2434_);
lean_closure_set(v___f_2607_, 18, v_parseCancelTk_2439_);
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = lean_io_as_task(v___f_2607_, v___x_2608_);
lean_dec_ref(v___x_2609_);
goto v___jp_2443_;
}
}
else
{
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v_cmds_2440_);
lean_dec_ref(v_parseCancelTk_2439_);
if (lean_obj_tag(v_old_x3f_2434_) == 1)
{
lean_object* v_val_2610_; lean_object* v___x_2611_; lean_object* v_children_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v_val_2610_ = lean_ctor_get(v_old_x3f_2434_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v_old_x3f_2434_, 1);
v___x_2611_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(v_val_2610_);
v_children_2612_ = lean_ctor_get(v___x_2611_, 1);
lean_inc_ref(v_children_2612_);
lean_dec_ref(v___x_2611_);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_array_get_size(v_children_2612_);
v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_dec_ref(v_children_2612_);
v___y_2543_ = v___y_2590_;
v___y_2544_ = v___y_2592_;
v___y_2545_ = v___x_2595_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_nat_dec_le(v___x_2614_, v___x_2614_);
if (v___x_2617_ == 0)
{
if (v___x_2615_ == 0)
{
lean_dec_ref(v_children_2612_);
v___y_2543_ = v___y_2590_;
v___y_2544_ = v___y_2592_;
v___y_2545_ = v___x_2595_;
goto v___jp_2542_;
}
else
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2614_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2612_, v___x_2618_, v___x_2619_, v___x_2616_);
lean_dec_ref(v_children_2612_);
v___y_2579_ = v___y_2590_;
v___y_2580_ = v___y_2592_;
v___y_2581_ = v___x_2595_;
v___y_2582_ = v___x_2620_;
goto v___jp_2578_;
}
}
else
{
size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = lean_usize_of_nat(v___x_2614_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2612_, v___x_2621_, v___x_2622_, v___x_2616_);
lean_dec_ref(v_children_2612_);
v___y_2579_ = v___y_2590_;
v___y_2580_ = v___y_2592_;
v___y_2581_ = v___x_2595_;
v___y_2582_ = v___x_2623_;
goto v___jp_2578_;
}
}
}
else
{
lean_dec(v_old_x3f_2434_);
v___y_2543_ = v___y_2590_;
v___y_2544_ = v___y_2592_;
v___y_2545_ = v___x_2595_;
goto v___jp_2542_;
}
}
}
v___jp_2625_:
{
lean_object* v_env_2626_; lean_object* v_scopes_2627_; lean_object* v___x_2628_; lean_object* v_opts_2629_; lean_object* v_currNamespace_2630_; lean_object* v_openDecls_2631_; lean_object* v___x_2632_; lean_object* v___f_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_snd_2637_; 
v_env_2626_ = lean_ctor_get(v_cmdState_2436_, 0);
v_scopes_2627_ = lean_ctor_get(v_cmdState_2436_, 2);
v___x_2628_ = l_List_head_x21___redArg(v___x_2487_, v_scopes_2627_);
v_opts_2629_ = lean_ctor_get(v___x_2628_, 1);
lean_inc_ref_n(v_opts_2629_, 2);
v_currNamespace_2630_ = lean_ctor_get(v___x_2628_, 2);
lean_inc(v_currNamespace_2630_);
v_openDecls_2631_ = lean_ctor_get(v___x_2628_, 3);
lean_inc(v_openDecls_2631_);
lean_dec(v___x_2628_);
lean_inc_ref(v_env_2626_);
v___x_2632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2632_, 0, v_env_2626_);
lean_ctor_set(v___x_2632_, 1, v_opts_2629_);
lean_ctor_set(v___x_2632_, 2, v_currNamespace_2630_);
lean_ctor_set(v___x_2632_, 3, v_openDecls_2631_);
lean_inc_ref(v_parserState_2435_);
lean_inc_ref(v_a_2441_);
v___f_2633_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2633_, 0, v_a_2441_);
lean_closure_set(v___f_2633_, 1, v___x_2632_);
lean_closure_set(v___f_2633_, 2, v_parserState_2435_);
v___x_2634_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_profileit(v___x_2634_, v_opts_2629_, v___f_2633_, v___x_2635_);
v_snd_2637_ = lean_ctor_get(v___x_2636_, 1);
lean_inc(v_snd_2637_);
if (lean_obj_tag(v_old_x3f_2434_) == 1)
{
lean_object* v_val_2638_; lean_object* v_fst_2639_; lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v_pos_2642_; lean_object* v_toSnapshot_2643_; lean_object* v_stx_2644_; lean_object* v_parserState_2645_; lean_object* v_elabSnap_2646_; lean_object* v_nextCmdSnap_x3f_2647_; uint8_t v___x_2648_; 
v_val_2638_ = lean_ctor_get(v_old_x3f_2434_, 0);
v_fst_2639_ = lean_ctor_get(v___x_2636_, 0);
lean_inc_n(v_fst_2639_, 2);
lean_dec(v___x_2636_);
v_fst_2640_ = lean_ctor_get(v_snd_2637_, 0);
lean_inc(v_fst_2640_);
v_snd_2641_ = lean_ctor_get(v_snd_2637_, 1);
lean_inc(v_snd_2641_);
lean_dec(v_snd_2637_);
v_pos_2642_ = lean_ctor_get(v_parserState_2435_, 0);
lean_inc(v_pos_2642_);
lean_dec_ref(v_parserState_2435_);
v_toSnapshot_2643_ = lean_ctor_get(v_val_2638_, 0);
v_stx_2644_ = lean_ctor_get(v_val_2638_, 1);
v_parserState_2645_ = lean_ctor_get(v_val_2638_, 2);
v_elabSnap_2646_ = lean_ctor_get(v_val_2638_, 3);
v_nextCmdSnap_x3f_2647_ = lean_ctor_get(v_val_2638_, 4);
lean_inc(v_stx_2644_);
v___x_2648_ = l_Lean_Syntax_eqWithInfo(v_fst_2639_, v_stx_2644_);
if (v___x_2648_ == 0)
{
if (lean_obj_tag(v_nextCmdSnap_x3f_2647_) == 0)
{
lean_inc_ref(v_opts_2629_);
lean_inc(v_fst_2639_);
lean_inc(v_fst_2640_);
v___y_2584_ = v_pos_2642_;
v___y_2585_ = v_snd_2641_;
v___y_2586_ = v_fst_2640_;
v___y_2587_ = v_fst_2639_;
v___y_2588_ = v___x_2635_;
v___y_2589_ = v_opts_2629_;
v___y_2590_ = v_fst_2640_;
v___y_2591_ = v_fst_2639_;
v___y_2592_ = v___x_2635_;
v___y_2593_ = v_opts_2629_;
goto v___jp_2583_;
}
else
{
lean_object* v_val_2649_; lean_object* v___x_2650_; 
v_val_2649_ = lean_ctor_get(v_nextCmdSnap_x3f_2647_, 0);
lean_inc(v_val_2649_);
v___x_2650_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2624_, v_val_2649_);
lean_inc_ref(v_opts_2629_);
lean_inc(v_fst_2639_);
lean_inc(v_fst_2640_);
v___y_2584_ = v_pos_2642_;
v___y_2585_ = v_snd_2641_;
v___y_2586_ = v_fst_2640_;
v___y_2587_ = v_fst_2639_;
v___y_2588_ = v___x_2635_;
v___y_2589_ = v_opts_2629_;
v___y_2590_ = v_fst_2640_;
v___y_2591_ = v_fst_2639_;
v___y_2592_ = v___x_2635_;
v___y_2593_ = v_opts_2629_;
goto v___jp_2583_;
}
}
else
{
lean_inc(v_val_2638_);
lean_dec(v_pos_2642_);
lean_dec(v_snd_2641_);
lean_dec(v_fst_2639_);
lean_dec_ref_known(v_old_x3f_2434_, 1);
lean_dec_ref(v_opts_2629_);
lean_dec_ref(v_parseCancelTk_2439_);
lean_dec_ref(v_cmdState_2436_);
if (lean_obj_tag(v_nextCmdSnap_x3f_2647_) == 1)
{
lean_object* v_val_2651_; 
lean_inc_ref(v_nextCmdSnap_x3f_2647_);
lean_inc_ref(v_elabSnap_2646_);
lean_inc_ref(v_parserState_2645_);
lean_inc(v_stx_2644_);
lean_inc_ref(v_toSnapshot_2643_);
lean_dec(v_val_2638_);
v_val_2651_ = lean_ctor_get(v_nextCmdSnap_x3f_2647_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v_nextCmdSnap_x3f_2647_, 1);
v_toSnapshot_2448_ = v_toSnapshot_2643_;
v_stx_2449_ = v_stx_2644_;
v_parserState_2450_ = v_parserState_2645_;
v_elabSnap_2451_ = v_elabSnap_2646_;
v_val_2452_ = v_val_2651_;
v_newParserState_2453_ = v_fst_2640_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2652_; 
lean_dec(v_fst_2640_);
lean_dec_ref(v_cmds_2440_);
v___x_2652_ = lean_io_promise_resolve(v_val_2638_, v_prom_2437_);
lean_dec(v_prom_2437_);
return v___x_2652_;
}
}
}
else
{
lean_object* v_fst_2653_; lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v_pos_2656_; 
v_fst_2653_ = lean_ctor_get(v___x_2636_, 0);
lean_inc_n(v_fst_2653_, 2);
lean_dec(v___x_2636_);
v_fst_2654_ = lean_ctor_get(v_snd_2637_, 0);
lean_inc_n(v_fst_2654_, 2);
v_snd_2655_ = lean_ctor_get(v_snd_2637_, 1);
lean_inc(v_snd_2655_);
lean_dec(v_snd_2637_);
v_pos_2656_ = lean_ctor_get(v_parserState_2435_, 0);
lean_inc(v_pos_2656_);
lean_dec_ref(v_parserState_2435_);
lean_inc_ref(v_opts_2629_);
v___y_2584_ = v_pos_2656_;
v___y_2585_ = v_snd_2655_;
v___y_2586_ = v_fst_2654_;
v___y_2587_ = v_fst_2653_;
v___y_2588_ = v___x_2635_;
v___y_2589_ = v_opts_2629_;
v___y_2590_ = v_fst_2654_;
v___y_2591_ = v_fst_2653_;
v___y_2592_ = v___x_2635_;
v___y_2593_ = v_opts_2629_;
goto v___jp_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(lean_object* v_oldResult_2673_, lean_object* v_cmds_2674_, lean_object* v_stx_2675_, lean_object* v_newParserState_2676_, lean_object* v_val_2677_, uint8_t v_sync_2678_, lean_object* v_val_2679_, lean_object* v_a_2680_, lean_object* v_oldNext_2681_){
_start:
{
lean_object* v_cmdState_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_cmdState_2683_ = lean_ctor_get(v_oldResult_2673_, 1);
lean_inc_ref(v_cmdState_2683_);
lean_dec_ref(v_oldResult_2673_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_oldNext_2681_);
v___x_2685_ = lean_array_push(v_cmds_2674_, v_stx_2675_);
v___x_2686_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2684_, v_newParserState_2676_, v_cmdState_2683_, v_val_2677_, v_sync_2678_, v_val_2679_, v___x_2685_, v_a_2680_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___boxed(lean_object** _args){
lean_object* v___x_2687_ = _args[0];
lean_object* v_val_2688_ = _args[1];
lean_object* v_cmds_2689_ = _args[2];
lean_object* v_fst_2690_ = _args[3];
lean_object* v_fst_2691_ = _args[4];
lean_object* v_val_2692_ = _args[5];
lean_object* v_a_2693_ = _args[6];
lean_object* v_snd_2694_ = _args[7];
lean_object* v___x_2695_ = _args[8];
lean_object* v___x_2696_ = _args[9];
lean_object* v_fst_2697_ = _args[10];
lean_object* v_val_2698_ = _args[11];
lean_object* v_val_2699_ = _args[12];
lean_object* v_val_2700_ = _args[13];
lean_object* v_snd_2701_ = _args[14];
lean_object* v_prom_2702_ = _args[15];
lean_object* v___x_2703_ = _args[16];
lean_object* v___f_2704_ = _args[17];
lean_object* v___f_2705_ = _args[18];
lean_object* v___f_2706_ = _args[19];
lean_object* v_pos_2707_ = _args[20];
lean_object* v_cmdState_2708_ = _args[21];
lean_object* v___x_2709_ = _args[22];
lean_object* v_opts_2710_ = _args[23];
lean_object* v___x_2711_ = _args[24];
lean_object* v_old_x3f_2712_ = _args[25];
lean_object* v_parseCancelTk_2713_ = _args[26];
lean_object* v_next_x3f_2714_ = _args[27];
lean_object* v___y_2715_ = _args[28];
_start:
{
uint8_t v_val_35906__boxed_2716_; uint8_t v___x_35909__boxed_2717_; lean_object* v_res_2718_; 
v_val_35906__boxed_2716_ = lean_unbox(v_val_2692_);
v___x_35909__boxed_2717_ = lean_unbox(v___x_2696_);
v_res_2718_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2687_, v_val_2688_, v_cmds_2689_, v_fst_2690_, v_fst_2691_, v_val_35906__boxed_2716_, v_a_2693_, v_snd_2694_, v___x_2695_, v___x_35909__boxed_2717_, v_fst_2697_, v_val_2698_, v_val_2699_, v_val_2700_, v_snd_2701_, v_prom_2702_, v___x_2703_, v___f_2704_, v___f_2705_, v___f_2706_, v_pos_2707_, v_cmdState_2708_, v___x_2709_, v_opts_2710_, v___x_2711_, v_old_x3f_2712_, v_parseCancelTk_2713_, v_next_x3f_2714_);
lean_dec_ref(v___x_2711_);
lean_dec_ref(v_opts_2710_);
lean_dec(v_prom_2702_);
lean_dec(v_val_2699_);
lean_dec_ref(v_a_2693_);
lean_dec(v_val_2688_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed(lean_object* v_old_x3f_2719_, lean_object* v_parserState_2720_, lean_object* v_cmdState_2721_, lean_object* v_prom_2722_, lean_object* v_sync_2723_, lean_object* v_parseCancelTk_2724_, lean_object* v_cmds_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
uint8_t v_sync_boxed_2728_; lean_object* v_res_2729_; 
v_sync_boxed_2728_ = lean_unbox(v_sync_2723_);
v_res_2729_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v_old_x3f_2719_, v_parserState_2720_, v_cmdState_2721_, v_prom_2722_, v_sync_boxed_2728_, v_parseCancelTk_2724_, v_cmds_2725_, v_a_2726_);
lean_dec_ref(v_a_2726_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(lean_object* v_as_2730_, size_t v_i_2731_, size_t v_stop_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_2730_, v_i_2731_, v_stop_2732_, v_b_2733_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___boxed(lean_object* v_as_2737_, lean_object* v_i_2738_, lean_object* v_stop_2739_, lean_object* v_b_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
size_t v_i_boxed_2743_; size_t v_stop_boxed_2744_; lean_object* v_res_2745_; 
v_i_boxed_2743_ = lean_unbox_usize(v_i_2738_);
lean_dec(v_i_2738_);
v_stop_boxed_2744_ = lean_unbox_usize(v_stop_2739_);
lean_dec(v_stop_2739_);
v_res_2745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6(v_as_2737_, v_i_boxed_2743_, v_stop_boxed_2744_, v_b_2740_, v___y_2741_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v_as_2737_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(lean_object* v_opts_2746_, lean_object* v_opt_2747_){
_start:
{
lean_object* v_name_2748_; lean_object* v_map_2749_; lean_object* v___x_2750_; 
v_name_2748_ = lean_ctor_get(v_opt_2747_, 0);
v_map_2749_ = lean_ctor_get(v_opts_2746_, 0);
v___x_2750_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2749_, v_name_2748_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_box(0);
return v___x_2751_;
}
else
{
lean_object* v_val_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2761_; 
v_val_2752_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2754_ = v___x_2750_;
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_val_2752_);
lean_dec(v___x_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
if (lean_obj_tag(v_val_2752_) == 0)
{
lean_object* v_v_2756_; lean_object* v___x_2758_; 
v_v_2756_ = lean_ctor_get(v_val_2752_, 0);
lean_inc_ref(v_v_2756_);
lean_dec_ref_known(v_val_2752_, 1);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v_v_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_v_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
else
{
lean_object* v___x_2760_; 
lean_del_object(v___x_2754_);
lean_dec(v_val_2752_);
v___x_2760_ = lean_box(0);
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1___boxed(lean_object* v_opts_2762_, lean_object* v_opt_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2762_, v_opt_2763_);
lean_dec_ref(v_opt_2763_);
lean_dec_ref(v_opts_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0(lean_object* v___x_2765_, lean_object* v_x_2766_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2765_);
v___x_2768_ = lean_box(0);
v___x_2769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2769_, 0, v_x_2766_);
lean_ctor_set(v___x_2769_, 1, v___x_2767_);
lean_ctor_set(v___x_2769_, 2, v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__2));
v___x_2776_ = l_Lean_Array_toPArray_x27___redArg(v___x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
if (lean_obj_tag(v_a_2777_) == 0)
{
lean_object* v___x_2779_; 
v___x_2779_ = l_List_reverse___redArg(v_a_2778_);
return v___x_2779_;
}
else
{
lean_object* v_head_2780_; lean_object* v_tail_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2794_; 
v_head_2780_ = lean_ctor_get(v_a_2777_, 0);
v_tail_2781_ = lean_ctor_get(v_a_2777_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_a_2777_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2783_ = v_a_2777_;
v_isShared_2784_ = v_isSharedCheck_2794_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_tail_2781_);
lean_inc(v_head_2780_);
lean_dec(v_a_2777_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2794_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2785_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__1));
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_head_2780_);
v___x_2787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
v___x_2788_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0___closed__3);
v___x_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v_a_2778_);
lean_ctor_set(v___x_2783_, 0, v___x_2789_);
v___x_2791_ = v___x_2783_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2778_);
v___x_2791_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v_a_2777_ = v_tail_2781_;
v_a_2778_ = v___x_2791_;
goto _start;
}
}
}
}
}
static double _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2805_; double v___x_2806_; 
v___x_2805_ = lean_unsigned_to_nat(1000000000u);
v___x_2806_ = lean_float_of_nat(v___x_2805_);
return v___x_2806_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__10));
v___x_2814_ = l_Lean_MessageData_ofFormat(v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(lean_object* v_setupImports_2815_, lean_object* v_stx_2816_, lean_object* v_origStx_2817_, lean_object* v_toProcessingContext_2818_, lean_object* v___x_2819_, lean_object* v_fileMap_2820_, lean_object* v_parserState_2821_, lean_object* v_a_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_toProcessingContext_2828_; lean_object* v___x_2829_; 
v_toProcessingContext_2828_ = lean_ctor_get(v___y_2826_, 0);
lean_inc_ref(v_toProcessingContext_2828_);
lean_inc(v_stx_2816_);
v___x_2829_ = lean_apply_3(v_setupImports_2815_, v_stx_2816_, v_toProcessingContext_2828_, lean_box(0));
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_3042_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_3042_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_3042_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
if (lean_obj_tag(v_a_2830_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; 
lean_dec_ref(v___x_2825_);
lean_dec(v___x_2823_);
lean_dec_ref(v_parserState_2821_);
lean_dec_ref(v_fileMap_2820_);
lean_dec(v___x_2819_);
lean_dec_ref(v_toProcessingContext_2818_);
lean_dec(v_origStx_2817_);
lean_dec(v_stx_2816_);
v_a_2834_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v_a_2830_, 1);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v_a_2834_);
v___x_2836_ = v___x_2832_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_3041_; 
v_a_2838_ = lean_ctor_get(v_a_2830_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_2840_ = v_a_2830_;
v_isShared_2841_ = v_isSharedCheck_3041_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v_a_2830_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_3041_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v_mainModuleName_2843_; lean_object* v_package_x3f_2844_; uint8_t v_isModule_2845_; lean_object* v_imports_2846_; lean_object* v_opts_2847_; uint32_t v_trustLevel_2848_; lean_object* v_importArts_2849_; lean_object* v_plugins_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2855_; 
v___x_2842_ = lean_io_mono_nanos_now();
v_mainModuleName_2843_ = lean_ctor_get(v_a_2838_, 0);
lean_inc(v_mainModuleName_2843_);
v_package_x3f_2844_ = lean_ctor_get(v_a_2838_, 1);
lean_inc(v_package_x3f_2844_);
v_isModule_2845_ = lean_ctor_get_uint8(v_a_2838_, sizeof(void*)*6 + 4);
v_imports_2846_ = lean_ctor_get(v_a_2838_, 2);
lean_inc_ref(v_imports_2846_);
v_opts_2847_ = lean_ctor_get(v_a_2838_, 3);
lean_inc_ref(v_opts_2847_);
v_trustLevel_2848_ = lean_ctor_get_uint32(v_a_2838_, sizeof(void*)*6);
v_importArts_2849_ = lean_ctor_get(v_a_2838_, 4);
lean_inc(v_importArts_2849_);
v_plugins_2850_ = lean_ctor_get(v_a_2838_, 5);
lean_inc_ref(v_plugins_2850_);
lean_dec(v_a_2838_);
v___x_2851_ = l_Lean_Elab_HeaderSyntax_startPos(v_stx_2816_);
v___x_2852_ = l_Lean_MessageLog_empty;
v___x_2853_ = 1;
lean_inc(v_stx_2816_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v_stx_2816_);
v___x_2855_ = v___x_2840_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_stx_2816_);
v___x_2855_ = v_reuseFailAlloc_3040_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_origStx_2817_);
lean_inc_ref(v___x_2855_);
lean_inc_ref(v_opts_2847_);
v___x_2857_ = l_Lean_Elab_processHeaderCore(v___x_2851_, v_imports_2846_, v_isModule_2845_, v_opts_2847_, v___x_2852_, v_toProcessingContext_2818_, v_trustLevel_2848_, v_plugins_2850_, v___x_2853_, v_mainModuleName_2843_, v_package_x3f_2844_, v_importArts_2849_, v___x_2855_, v___x_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_3031_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_3031_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_3031_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_3030_; 
v_fst_2862_ = lean_ctor_get(v_a_2858_, 0);
v_snd_2863_ = lean_ctor_get(v_a_2858_, 1);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_a_2858_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_2865_ = v_a_2858_;
v_isShared_2866_ = v_isSharedCheck_3030_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_snd_2863_);
lean_inc(v_fst_2862_);
lean_dec(v_a_2858_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_3030_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v_traceState_2885_; 
v___x_2867_ = lean_io_mono_nanos_now();
lean_inc(v_snd_2863_);
v___x_2868_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2863_);
v___x_2869_ = l_Lean_MessageLog_hasErrors(v_snd_2863_);
if (v___x_2869_ == 0)
{
double v___x_2978_; double v___x_2979_; double v___x_2980_; double v___x_2981_; double v___x_2982_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_del_object(v___x_2832_);
lean_dec_ref(v___x_2825_);
v___x_2978_ = lean_float_of_nat(v___x_2842_);
v___x_2979_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2980_ = lean_float_div(v___x_2978_, v___x_2979_);
v___x_2981_ = lean_float_of_nat(v___x_2867_);
v___x_2982_ = lean_float_div(v___x_2981_, v___x_2979_);
v___x_2999_ = l_Lean_trace_profiler_output;
v___x_3000_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2847_, v___x_2999_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = l_Lean_trace_profiler_serve;
v___x_3002_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2847_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2885_ = v___x_3003_;
goto v___jp_2884_;
}
else
{
goto v___jp_2983_;
}
}
else
{
lean_dec_ref_known(v___x_3000_, 1);
goto v___jp_2983_;
}
v___jp_2983_:
{
uint64_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2984_ = 0ULL;
v___x_2985_ = lean_box(0);
v___x_2986_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2987_ = lean_box(0);
v___x_2988_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2989_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2989_, 0, v___x_2986_);
lean_ctor_set(v___x_2989_, 1, v___x_2987_);
lean_ctor_set(v___x_2989_, 2, v___x_2988_);
lean_ctor_set_float(v___x_2989_, sizeof(void*)*3, v___x_2980_);
lean_ctor_set_float(v___x_2989_, sizeof(void*)*3 + 8, v___x_2982_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*3 + 16, v___x_2853_);
v___x_2990_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_2991_ = lean_mk_empty_array_with_capacity(v___x_2819_);
v___x_2992_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2989_);
lean_ctor_set(v___x_2992_, 1, v___x_2990_);
lean_ctor_set(v___x_2992_, 2, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2985_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_mk_empty_array_with_capacity(v___x_2994_);
v___x_2996_ = lean_array_push(v___x_2995_, v___x_2993_);
v___x_2997_ = l_Lean_Array_toPArray_x27___redArg(v___x_2996_);
lean_dec_ref(v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set_uint64(v___x_2998_, sizeof(void*)*1, v___x_2984_);
v_traceState_2885_ = v___x_2998_;
goto v___jp_2884_;
}
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint64_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
lean_dec(v___x_2867_);
lean_del_object(v___x_2865_);
lean_dec(v_snd_2863_);
lean_dec(v_fst_2862_);
lean_del_object(v___x_2860_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v_opts_2847_);
lean_dec(v___x_2842_);
lean_dec(v___x_2823_);
lean_dec_ref(v_parserState_2821_);
lean_dec_ref(v_fileMap_2820_);
lean_dec(v_stx_2816_);
v___x_3004_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3005_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3006_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2819_, 2);
v___x_3007_ = l_Lean_Name_num___override(v___x_3006_, v___x_2819_);
v___x_3008_ = l_Lean_Name_str___override(v___x_3007_, v___x_3004_);
v___x_3009_ = l_Lean_Name_str___override(v___x_3008_, v___x_3005_);
v___x_3010_ = l_Lean_Name_str___override(v___x_3009_, v___x_3004_);
v___x_3011_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3012_ = l_Lean_Name_str___override(v___x_3010_, v___x_3011_);
v___x_3013_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3014_ = l_Lean_Name_str___override(v___x_3012_, v___x_3013_);
v___x_3015_ = l_Lean_Name_toString(v___x_3014_, v___x_2853_);
v___x_3016_ = lean_box(0);
v___x_3017_ = 0ULL;
v___x_3018_ = lean_unsigned_to_nat(32u);
v___x_3019_ = lean_mk_empty_array_with_capacity(v___x_3018_);
v___x_3020_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3021_ = ((size_t)5ULL);
v___x_3022_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3019_);
lean_ctor_set(v___x_3022_, 2, v___x_2819_);
lean_ctor_set(v___x_3022_, 3, v___x_2819_);
lean_ctor_set_usize(v___x_3022_, 4, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set_uint64(v___x_3023_, sizeof(void*)*1, v___x_3017_);
v___x_3024_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3024_, 0, v___x_3015_);
lean_ctor_set(v___x_3024_, 1, v___x_2868_);
lean_ctor_set(v___x_3024_, 2, v___x_3016_);
lean_ctor_set(v___x_3024_, 3, v___x_3023_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*4, v___x_2869_);
v___x_3025_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2825_);
v___x_3026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
lean_ctor_set(v___x_3026_, 2, v___x_3016_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_3026_);
v___x_3028_ = v___x_2832_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
v___jp_2870_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___y_2876_);
v___x_2878_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2878_, 0, v___y_2875_);
lean_ctor_set(v___x_2878_, 1, v___x_2868_);
lean_ctor_set(v___x_2878_, 2, v___x_2877_);
lean_ctor_set(v___x_2878_, 3, v___y_2873_);
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*4, v___x_2869_);
v___x_2879_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2872_, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2880_, 0, v___y_2871_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
lean_ctor_set(v___x_2880_, 2, v___y_2874_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2880_);
v___x_2882_ = v___x_2860_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
v___jp_2884_:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_Language_Lean_reparseOptions(v_opts_2847_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v_env_2893_; lean_object* v_messages_2894_; lean_object* v_scopes_2895_; lean_object* v_usedQuotCtxts_2896_; lean_object* v_nextMacroScope_2897_; lean_object* v_maxRecDepth_2898_; lean_object* v_ngen_2899_; lean_object* v_auxDeclNGen_2900_; lean_object* v_snapshotTasks_2901_; lean_object* v_prevLinterStates_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2967_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2888_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg___closed__1);
lean_inc_n(v___x_2819_, 4);
v___x_2889_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2819_);
lean_ctor_set(v___x_2889_, 1, v___x_2819_);
lean_ctor_set(v___x_2889_, 2, v___x_2819_);
lean_ctor_set(v___x_2889_, 3, v___x_2819_);
lean_ctor_set(v___x_2889_, 4, v___x_2888_);
lean_ctor_set(v___x_2889_, 5, v___x_2888_);
lean_ctor_set(v___x_2889_, 6, v___x_2888_);
lean_ctor_set(v___x_2889_, 7, v___x_2888_);
lean_ctor_set(v___x_2889_, 8, v___x_2888_);
lean_ctor_set(v___x_2889_, 9, v___x_2888_);
lean_ctor_set(v___x_2889_, 10, v___x_2888_);
v___x_2890_ = lean_io_promise_new();
v___x_2891_ = l_IO_CancelToken_new();
lean_inc(v_fst_2862_);
v___x_2892_ = l_Lean_Elab_Command_mkState(v_fst_2862_, v_snd_2863_, v_a_2887_);
v_env_2893_ = lean_ctor_get(v___x_2892_, 0);
v_messages_2894_ = lean_ctor_get(v___x_2892_, 1);
v_scopes_2895_ = lean_ctor_get(v___x_2892_, 2);
v_usedQuotCtxts_2896_ = lean_ctor_get(v___x_2892_, 3);
v_nextMacroScope_2897_ = lean_ctor_get(v___x_2892_, 4);
v_maxRecDepth_2898_ = lean_ctor_get(v___x_2892_, 5);
v_ngen_2899_ = lean_ctor_get(v___x_2892_, 6);
v_auxDeclNGen_2900_ = lean_ctor_get(v___x_2892_, 7);
v_snapshotTasks_2901_ = lean_ctor_get(v___x_2892_, 10);
v_prevLinterStates_2902_ = lean_ctor_get(v___x_2892_, 11);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; lean_object* v_unused_2969_; 
v_unused_2968_ = lean_ctor_get(v___x_2892_, 9);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v___x_2892_, 8);
lean_dec(v_unused_2969_);
v___x_2904_ = v___x_2892_;
v_isShared_2905_ = v_isSharedCheck_2967_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_prevLinterStates_2902_);
lean_inc(v_snapshotTasks_2901_);
lean_inc(v_auxDeclNGen_2900_);
lean_inc(v_ngen_2899_);
lean_inc(v_maxRecDepth_2898_);
lean_inc(v_nextMacroScope_2897_);
lean_inc(v_usedQuotCtxts_2896_);
lean_inc(v_scopes_2895_);
lean_inc(v_messages_2894_);
lean_inc(v_env_2893_);
lean_dec(v___x_2892_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2967_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2906_ = lean_box(0);
v___x_2907_ = l_Lean_Options_empty;
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_unsigned_to_nat(1u);
v___x_2911_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2912_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2912_, 0, v_fst_2862_);
lean_ctor_set(v___x_2912_, 1, v___x_2906_);
lean_ctor_set(v___x_2912_, 2, v_fileMap_2820_);
lean_ctor_set(v___x_2912_, 3, v___x_2889_);
lean_ctor_set(v___x_2912_, 4, v___x_2907_);
lean_ctor_set(v___x_2912_, 5, v___x_2908_);
lean_ctor_set(v___x_2912_, 6, v___x_2909_);
lean_ctor_set(v___x_2912_, 7, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
v___x_2914_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2816_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_stx_2816_);
lean_ctor_set(v___x_2865_, 0, v___x_2914_);
v___x_2916_ = v___x_2865_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_stx_2816_);
v___x_2916_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
v___x_2918_ = lean_unsigned_to_nat(2u);
v___x_2919_ = l_Lean_Syntax_getArg(v_stx_2816_, v___x_2918_);
lean_dec(v_stx_2816_);
v___x_2920_ = l_Lean_Syntax_getArgs(v___x_2919_);
lean_dec(v___x_2919_);
v___x_2921_ = lean_array_to_list(v___x_2920_);
v___x_2922_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2921_, v___x_2909_);
v___x_2923_ = l_Lean_List_toPArray_x27___redArg(v___x_2922_);
v___x_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2917_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2913_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_mk_empty_array_with_capacity(v___x_2910_);
v___x_2927_ = lean_array_push(v___x_2926_, v___x_2925_);
v___x_2928_ = l_Lean_Array_toPArray_x27___redArg(v___x_2927_);
lean_dec_ref(v___x_2927_);
lean_inc_ref(v___x_2928_);
v___x_2929_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2929_, 0, v___x_2888_);
lean_ctor_set(v___x_2929_, 1, v___x_2888_);
lean_ctor_set(v___x_2929_, 2, v___x_2928_);
lean_ctor_set_uint8(v___x_2929_, sizeof(void*)*3, v___x_2853_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 9, v_traceState_2885_);
lean_ctor_set(v___x_2904_, 8, v___x_2929_);
v___x_2931_ = v___x_2904_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_env_2893_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_messages_2894_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_scopes_2895_);
lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_usedQuotCtxts_2896_);
lean_ctor_set(v_reuseFailAlloc_2965_, 4, v_nextMacroScope_2897_);
lean_ctor_set(v_reuseFailAlloc_2965_, 5, v_maxRecDepth_2898_);
lean_ctor_set(v_reuseFailAlloc_2965_, 6, v_ngen_2899_);
lean_ctor_set(v_reuseFailAlloc_2965_, 7, v_auxDeclNGen_2900_);
lean_ctor_set(v_reuseFailAlloc_2965_, 8, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_2965_, 9, v_traceState_2885_);
lean_ctor_set(v_reuseFailAlloc_2965_, 10, v_snapshotTasks_2901_);
lean_ctor_set(v_reuseFailAlloc_2965_, 11, v_prevLinterStates_2902_);
v___x_2931_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; size_t v___x_2941_; lean_object* v___x_2942_; lean_object* v_size_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint64_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2932_ = lean_mk_empty_array_with_capacity(v___x_2819_);
lean_inc_ref(v___x_2891_);
lean_inc(v___x_2890_);
lean_inc_ref(v___x_2931_);
v___x_2933_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2906_, v_parserState_2821_, v___x_2931_, v___x_2890_, v___x_2853_, v___x_2891_, v___x_2932_, v_a_2822_);
v___x_2934_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2935_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2936_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2819_, 3);
v___x_2937_ = l_Lean_Name_num___override(v___x_2936_, v___x_2819_);
v___x_2938_ = lean_unsigned_to_nat(32u);
v___x_2939_ = lean_mk_empty_array_with_capacity(v___x_2938_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2941_ = ((size_t)5ULL);
v___x_2942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2939_);
lean_ctor_set(v___x_2942_, 2, v___x_2819_);
lean_ctor_set(v___x_2942_, 3, v___x_2819_);
lean_ctor_set_usize(v___x_2942_, 4, v___x_2941_);
v_size_2943_ = lean_ctor_get(v___x_2928_, 2);
lean_inc(v_size_2943_);
v___x_2944_ = l_Lean_Name_str___override(v___x_2937_, v___x_2934_);
v___x_2945_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2823_);
v___x_2946_ = l_Lean_Name_str___override(v___x_2944_, v___x_2935_);
v___x_2947_ = l_Lean_Name_str___override(v___x_2946_, v___x_2934_);
v___x_2948_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2949_ = l_Lean_Name_str___override(v___x_2947_, v___x_2948_);
v___x_2950_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2951_ = l_Lean_Name_str___override(v___x_2949_, v___x_2950_);
v___x_2952_ = l_Lean_Name_toString(v___x_2951_, v___x_2853_);
v___x_2953_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2954_ = 0ULL;
v___x_2955_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2955_, 0, v___x_2942_);
lean_ctor_set_uint64(v___x_2955_, sizeof(void*)*1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2891_);
v___x_2957_ = l_IO_Promise_result_x21___redArg(v___x_2890_);
lean_dec(v___x_2890_);
v___x_2958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2823_);
lean_ctor_set(v___x_2958_, 1, v___x_2945_);
lean_ctor_set(v___x_2958_, 2, v___x_2956_);
lean_ctor_set(v___x_2958_, 3, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2931_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_inc_ref(v___x_2955_);
lean_inc_ref(v___x_2952_);
v___x_2961_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2961_, 0, v___x_2952_);
lean_ctor_set(v___x_2961_, 1, v___x_2953_);
lean_ctor_set(v___x_2961_, 2, v___x_2906_);
lean_ctor_set(v___x_2961_, 3, v___x_2955_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*4, v___x_2869_);
v___x_2962_ = lean_nat_dec_lt(v___x_2819_, v_size_2943_);
lean_dec(v_size_2943_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; 
lean_dec_ref(v___x_2928_);
lean_dec(v___x_2819_);
v___x_2963_ = l_outOfBounds___redArg(v___x_2824_);
v___y_2871_ = v___x_2961_;
v___y_2872_ = v___x_2855_;
v___y_2873_ = v___x_2955_;
v___y_2874_ = v___x_2960_;
v___y_2875_ = v___x_2952_;
v___y_2876_ = v___x_2963_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2824_, v___x_2928_, v___x_2819_);
lean_dec(v___x_2819_);
lean_dec_ref(v___x_2928_);
v___y_2871_ = v___x_2961_;
v___y_2872_ = v___x_2855_;
v___y_2873_ = v___x_2955_;
v___y_2874_ = v___x_2960_;
v___y_2875_ = v___x_2952_;
v___y_2876_ = v___x_2964_;
goto v___jp_2870_;
}
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_traceState_2885_);
lean_dec_ref(v___x_2868_);
lean_del_object(v___x_2865_);
lean_dec(v_snd_2863_);
lean_dec(v_fst_2862_);
lean_del_object(v___x_2860_);
lean_dec_ref(v___x_2855_);
lean_dec(v___x_2823_);
lean_dec_ref(v_parserState_2821_);
lean_dec_ref(v_fileMap_2820_);
lean_dec(v___x_2819_);
lean_dec(v_stx_2816_);
v_a_2970_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2886_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2886_);
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
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v___x_2855_);
lean_dec_ref(v_opts_2847_);
lean_dec(v___x_2842_);
lean_del_object(v___x_2832_);
lean_dec_ref(v___x_2825_);
lean_dec(v___x_2823_);
lean_dec_ref(v_parserState_2821_);
lean_dec_ref(v_fileMap_2820_);
lean_dec(v___x_2819_);
lean_dec(v_stx_2816_);
v_a_3032_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2857_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2857_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
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
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v___x_2825_);
lean_dec(v___x_2823_);
lean_dec_ref(v_parserState_2821_);
lean_dec_ref(v_fileMap_2820_);
lean_dec(v___x_2819_);
lean_dec_ref(v_toProcessingContext_2818_);
lean_dec(v_origStx_2817_);
lean_dec(v_stx_2816_);
v_a_3043_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2829_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2829_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3051_, lean_object* v_stx_3052_, lean_object* v_origStx_3053_, lean_object* v_toProcessingContext_3054_, lean_object* v___x_3055_, lean_object* v_fileMap_3056_, lean_object* v_parserState_3057_, lean_object* v_a_3058_, lean_object* v___x_3059_, lean_object* v___x_3060_, lean_object* v___x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3051_, v_stx_3052_, v_origStx_3053_, v_toProcessingContext_3054_, v___x_3055_, v_fileMap_3056_, v_parserState_3057_, v_a_3058_, v___x_3059_, v___x_3060_, v___x_3061_, v___y_3062_);
lean_dec_ref(v___y_3062_);
lean_dec_ref(v___x_3060_);
lean_dec_ref(v_a_3058_);
return v_res_3064_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___f_3066_; 
v___x_3065_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3066_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3066_, 0, v___x_3065_);
return v___f_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3067_, lean_object* v_stx_3068_, lean_object* v_origStx_3069_, lean_object* v_parserState_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v_toProcessingContext_3073_; lean_object* v_fileMap_3074_; lean_object* v_endPos_3075_; lean_object* v___x_3076_; lean_object* v___f_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_toProcessingContext_3073_ = lean_ctor_get(v_a_3071_, 0);
v_fileMap_3074_ = lean_ctor_get(v_toProcessingContext_3073_, 2);
v_endPos_3075_ = lean_ctor_get(v_toProcessingContext_3073_, 3);
v___x_3076_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3077_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3078_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3071_, 2);
lean_inc_ref(v_fileMap_3074_);
lean_inc_ref(v_toProcessingContext_3073_);
v___f_3081_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3081_, 0, v_setupImports_3067_);
lean_closure_set(v___f_3081_, 1, v_stx_3068_);
lean_closure_set(v___f_3081_, 2, v_origStx_3069_);
lean_closure_set(v___f_3081_, 3, v_toProcessingContext_3073_);
lean_closure_set(v___f_3081_, 4, v___x_3080_);
lean_closure_set(v___f_3081_, 5, v_fileMap_3074_);
lean_closure_set(v___f_3081_, 6, v_parserState_3070_);
lean_closure_set(v___f_3081_, 7, v_a_3071_);
lean_closure_set(v___f_3081_, 8, v___x_3079_);
lean_closure_set(v___f_3081_, 9, v___x_3078_);
lean_closure_set(v___f_3081_, 10, v___x_3076_);
lean_inc(v_endPos_3075_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v_endPos_3075_);
v___x_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
v___x_3084_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3084_, 0, lean_box(0));
lean_closure_set(v___x_3084_, 1, v___f_3077_);
lean_closure_set(v___x_3084_, 2, v___f_3081_);
lean_closure_set(v___x_3084_, 3, v_a_3071_);
v___x_3085_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3079_, v___x_3079_, v___x_3083_, v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3086_, lean_object* v_stx_3087_, lean_object* v_origStx_3088_, lean_object* v_parserState_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3086_, v_stx_3087_, v_origStx_3088_, v_parserState_3089_, v_a_3090_);
lean_dec_ref(v_a_3090_);
return v_res_3092_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_box(0);
v___x_3096_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3095_);
return v___x_3096_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = 1;
v___x_3102_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3103_ = l_Lean_Name_toString(v___x_3102_, v___x_3101_);
return v___x_3103_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3104_ = 0;
v___x_3105_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3106_ = lean_box(0);
v___x_3107_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3108_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3109_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v___x_3107_);
lean_ctor_set(v___x_3109_, 2, v___x_3106_);
lean_ctor_set(v___x_3109_, 3, v___x_3105_);
lean_ctor_set_uint8(v___x_3109_, sizeof(void*)*4, v___x_3104_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3110_, lean_object* v_cmdState_3111_, lean_object* v_a_3112_, lean_object* v_toSnapshot_3113_, lean_object* v_newStx_3114_, lean_object* v_oldCmd_3115_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v_diagnostics_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3145_; 
v___x_3117_ = lean_io_promise_new();
v___x_3118_ = l_IO_CancelToken_new();
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_oldCmd_3115_);
v___x_3120_ = 1;
v___x_3121_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3118_);
lean_inc(v___x_3117_);
lean_inc_ref(v_cmdState_3111_);
v___x_3122_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3119_, v_newParserState_3110_, v_cmdState_3111_, v___x_3117_, v___x_3120_, v___x_3118_, v___x_3121_, v_a_3112_);
v_diagnostics_3123_ = lean_ctor_get(v_toSnapshot_3113_, 1);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_toSnapshot_3113_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; 
v_unused_3146_ = lean_ctor_get(v_toSnapshot_3113_, 3);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_toSnapshot_3113_, 2);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_toSnapshot_3113_, 0);
lean_dec(v_unused_3148_);
v___x_3125_ = v_toSnapshot_3113_;
v_isShared_3126_ = v_isSharedCheck_3145_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_diagnostics_3123_);
lean_dec(v_toSnapshot_3113_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3145_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3129_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3130_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3118_);
v___x_3132_ = l_IO_Promise_result_x21___redArg(v___x_3117_);
lean_dec(v___x_3117_);
v___x_3133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3127_);
lean_ctor_set(v___x_3133_, 1, v___x_3128_);
lean_ctor_set(v___x_3133_, 2, v___x_3131_);
lean_ctor_set(v___x_3133_, 3, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_cmdState_3111_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
v___x_3136_ = 0;
v___x_3137_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_newStx_3114_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 3, v___x_3130_);
lean_ctor_set(v___x_3125_, 2, v___x_3127_);
lean_ctor_set(v___x_3125_, 0, v___x_3129_);
v___x_3140_ = v___x_3125_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_diagnostics_3123_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v___x_3130_);
v___x_3140_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_ctor_set_uint8(v___x_3140_, sizeof(void*)*4, v___x_3136_);
v___x_3141_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3138_, v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3137_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
lean_ctor_set(v___x_3142_, 2, v___x_3135_);
v___x_3143_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3127_, v___x_3142_);
return v___x_3143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3149_, lean_object* v_cmdState_3150_, lean_object* v_a_3151_, lean_object* v_toSnapshot_3152_, lean_object* v_newStx_3153_, lean_object* v_oldCmd_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3149_, v_cmdState_3150_, v_a_3151_, v_toSnapshot_3152_, v_newStx_3153_, v_oldCmd_3154_);
lean_dec_ref(v_a_3151_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3157_, lean_object* v_a_3158_, lean_object* v_newStx_3159_, lean_object* v___x_3160_, lean_object* v_oldProcessed_3161_){
_start:
{
lean_object* v_result_x3f_3163_; 
v_result_x3f_3163_ = lean_ctor_get(v_oldProcessed_3161_, 2);
if (lean_obj_tag(v_result_x3f_3163_) == 1)
{
lean_object* v_val_3164_; lean_object* v_firstCmdSnap_3165_; lean_object* v_toSnapshot_3166_; lean_object* v_cmdState_3167_; lean_object* v_stx_x3f_3168_; lean_object* v___f_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; 
v_val_3164_ = lean_ctor_get(v_result_x3f_3163_, 0);
lean_inc(v_val_3164_);
v_firstCmdSnap_3165_ = lean_ctor_get(v_val_3164_, 1);
lean_inc_ref(v_firstCmdSnap_3165_);
v_toSnapshot_3166_ = lean_ctor_get(v_oldProcessed_3161_, 0);
lean_inc_ref(v_toSnapshot_3166_);
lean_dec_ref(v_oldProcessed_3161_);
v_cmdState_3167_ = lean_ctor_get(v_val_3164_, 0);
lean_inc_ref(v_cmdState_3167_);
lean_dec(v_val_3164_);
v_stx_x3f_3168_ = lean_ctor_get(v_firstCmdSnap_3165_, 0);
lean_inc(v_stx_x3f_3168_);
lean_inc_ref(v_a_3158_);
v___f_3169_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3169_, 0, v_newParserState_3157_);
lean_closure_set(v___f_3169_, 1, v_cmdState_3167_);
lean_closure_set(v___f_3169_, 2, v_a_3158_);
lean_closure_set(v___f_3169_, 3, v_toSnapshot_3166_);
lean_closure_set(v___f_3169_, 4, v_newStx_3159_);
v___x_3170_ = lean_box(0);
v___x_3171_ = 1;
v___x_3172_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3165_, v___f_3169_, v_stx_x3f_3168_, v___x_3160_, v___x_3170_, v___x_3171_);
return v___x_3172_;
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v___x_3160_);
lean_dec_ref(v_newParserState_3157_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_newStx_3159_);
v___x_3174_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3173_, v_oldProcessed_3161_);
return v___x_3174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3175_, lean_object* v_a_3176_, lean_object* v_newStx_3177_, lean_object* v___x_3178_, lean_object* v_oldProcessed_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3175_, v_a_3176_, v_newStx_3177_, v___x_3178_, v_oldProcessed_3179_);
lean_dec_ref(v_a_3176_);
return v_res_3181_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3182_ = 0;
v___x_3183_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3184_ = lean_box(0);
v___x_3185_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3186_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3187_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3185_);
lean_ctor_set(v___x_3187_, 2, v___x_3184_);
lean_ctor_set(v___x_3187_, 3, v___x_3183_);
lean_ctor_set_uint8(v___x_3187_, sizeof(void*)*4, v___x_3182_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3188_, lean_object* v_a_3189_, lean_object* v_old_3190_, lean_object* v_newStx_3191_, lean_object* v_newParserState_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_result_x3f_3195_; 
v_result_x3f_3195_ = lean_ctor_get(v_old_3190_, 4);
lean_inc(v_result_x3f_3195_);
if (lean_obj_tag(v_result_x3f_3195_) == 1)
{
lean_object* v_val_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3250_; 
v_val_3196_ = lean_ctor_get(v_result_x3f_3195_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_result_x3f_3195_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3198_ = v_result_x3f_3195_;
v_isShared_3199_ = v_isSharedCheck_3250_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_val_3196_);
lean_dec(v_result_x3f_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3250_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v_processedSnap_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3248_; 
v_processedSnap_3200_ = lean_ctor_get(v_val_3196_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_val_3196_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; 
v_unused_3249_ = lean_ctor_get(v_val_3196_, 0);
lean_dec(v_unused_3249_);
v___x_3202_ = v_val_3196_;
v_isShared_3203_ = v_isSharedCheck_3248_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_processedSnap_3200_);
lean_dec(v_val_3196_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3248_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_toSnapshot_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3243_; 
v_toSnapshot_3204_ = lean_ctor_get(v_old_3190_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_old_3190_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; lean_object* v_unused_3245_; lean_object* v_unused_3246_; lean_object* v_unused_3247_; 
v_unused_3244_ = lean_ctor_get(v_old_3190_, 4);
lean_dec(v_unused_3244_);
v_unused_3245_ = lean_ctor_get(v_old_3190_, 3);
lean_dec(v_unused_3245_);
v_unused_3246_ = lean_ctor_get(v_old_3190_, 2);
lean_dec(v_unused_3246_);
v_unused_3247_ = lean_ctor_get(v_old_3190_, 1);
lean_dec(v_unused_3247_);
v___x_3206_ = v_old_3190_;
v_isShared_3207_ = v_isSharedCheck_3243_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_toSnapshot_3204_);
lean_dec(v_old_3190_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3243_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v_pos_3208_; lean_object* v_endPos_3209_; lean_object* v_stx_x3f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___f_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v_diagnostics_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3239_; 
v_pos_3208_ = lean_ctor_get(v_newParserState_3192_, 0);
v_endPos_3209_ = lean_ctor_get(v_toProcessingContext_3188_, 3);
v_stx_x3f_3210_ = lean_ctor_get(v_processedSnap_3200_, 0);
lean_inc(v_stx_x3f_3210_);
lean_inc(v_endPos_3209_);
lean_inc(v_pos_3208_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_pos_3208_);
lean_ctor_set(v___x_3211_, 1, v_endPos_3209_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_inc_ref(v___x_3212_);
lean_inc(v_newStx_3191_);
lean_inc_ref(v_a_3189_);
lean_inc_ref(v_newParserState_3192_);
v___f_3213_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3213_, 0, v_newParserState_3192_);
lean_closure_set(v___f_3213_, 1, v_a_3189_);
lean_closure_set(v___f_3213_, 2, v_newStx_3191_);
lean_closure_set(v___f_3213_, 3, v___x_3212_);
v___x_3214_ = lean_box(0);
v___x_3215_ = 1;
v___x_3216_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3200_, v___f_3213_, v_stx_x3f_3210_, v___x_3212_, v___x_3214_, v___x_3215_);
v_diagnostics_3217_ = lean_ctor_get(v_toSnapshot_3204_, 1);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_toSnapshot_3204_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; lean_object* v_unused_3241_; lean_object* v_unused_3242_; 
v_unused_3240_ = lean_ctor_get(v_toSnapshot_3204_, 3);
lean_dec(v_unused_3240_);
v_unused_3241_ = lean_ctor_get(v_toSnapshot_3204_, 2);
lean_dec(v_unused_3241_);
v_unused_3242_ = lean_ctor_get(v_toSnapshot_3204_, 0);
lean_dec(v_unused_3242_);
v___x_3219_ = v_toSnapshot_3204_;
v_isShared_3220_ = v_isSharedCheck_3239_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_diagnostics_3217_);
lean_dec(v_toSnapshot_3204_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3239_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3221_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3222_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___x_3216_);
lean_ctor_set(v___x_3202_, 0, v_newParserState_3192_);
v___x_3224_ = v___x_3202_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_newParserState_3192_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v___x_3216_);
v___x_3224_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3224_);
v___x_3226_ = v___x_3198_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
uint8_t v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3227_ = 0;
v___x_3228_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3191_);
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_newStx_3191_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 3, v___x_3222_);
lean_ctor_set(v___x_3219_, 2, v___x_3214_);
lean_ctor_set(v___x_3219_, 0, v___x_3221_);
v___x_3231_ = v___x_3219_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_diagnostics_3217_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v___x_3222_);
v___x_3231_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3234_; 
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*4, v___x_3227_);
v___x_3232_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3229_, v___x_3231_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 4, v___x_3226_);
lean_ctor_set(v___x_3206_, 3, v_newStx_3191_);
lean_ctor_set(v___x_3206_, 2, v_toProcessingContext_3188_);
lean_ctor_set(v___x_3206_, 1, v___x_3232_);
lean_ctor_set(v___x_3206_, 0, v___x_3228_);
v___x_3234_ = v___x_3206_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_toProcessingContext_3188_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v_newStx_3191_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v___x_3226_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
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
lean_dec(v_result_x3f_3195_);
lean_dec_ref(v_newParserState_3192_);
lean_dec(v_newStx_3191_);
lean_dec_ref(v_toProcessingContext_3188_);
return v_old_3190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3251_, lean_object* v_a_3252_, lean_object* v_old_3253_, lean_object* v_newStx_3254_, lean_object* v_newParserState_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3251_, v_a_3252_, v_old_3253_, v_newStx_3254_, v_newParserState_3255_, v___y_3256_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v_a_3252_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3259_, lean_object* v_setupImports_3260_, lean_object* v_old_x3f_3261_, lean_object* v___x_3262_, lean_object* v___f_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; 
lean_inc_ref(v_toProcessingContext_3259_);
v___x_3266_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3259_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3335_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3335_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3335_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v_snd_3271_; lean_object* v_fst_3272_; lean_object* v_fst_3273_; lean_object* v_snd_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3334_; 
v_snd_3271_ = lean_ctor_get(v_a_3267_, 1);
lean_inc(v_snd_3271_);
v_fst_3272_ = lean_ctor_get(v_a_3267_, 0);
lean_inc(v_fst_3272_);
lean_dec(v_a_3267_);
v_fst_3273_ = lean_ctor_get(v_snd_3271_, 0);
v_snd_3274_ = lean_ctor_get(v_snd_3271_, 1);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_snd_3271_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3276_ = v_snd_3271_;
v_isShared_3277_ = v_isSharedCheck_3334_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_snd_3274_);
lean_inc(v_fst_3273_);
lean_dec(v_snd_3271_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3334_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
uint8_t v___x_3278_; 
v___x_3278_ = l_Lean_MessageLog_hasErrors(v_snd_3274_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___y_3281_; 
lean_inc(v_fst_3272_);
v___x_3279_ = l_Lean_Syntax_unsetTrailing(v_fst_3272_);
if (lean_obj_tag(v_old_x3f_3261_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3317_; 
v_val_3302_ = lean_ctor_get(v_old_x3f_3261_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_old_x3f_3261_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3304_ = v_old_x3f_3261_;
v_isShared_3305_ = v_isSharedCheck_3317_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_val_3302_);
lean_dec(v_old_x3f_3261_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3317_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_stx_3306_; lean_object* v_result_x3f_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v_stx_3306_ = lean_ctor_get(v_val_3302_, 3);
v_result_x3f_3307_ = lean_ctor_get(v_val_3302_, 4);
lean_inc(v_stx_3306_);
v___x_3308_ = l_Lean_Syntax_unsetTrailing(v_stx_3306_);
lean_inc(v___x_3279_);
v___x_3309_ = l_Lean_Syntax_eqWithInfo(v___x_3279_, v___x_3308_);
if (v___x_3309_ == 0)
{
lean_inc(v_result_x3f_3307_);
lean_del_object(v___x_3304_);
lean_dec(v_val_3302_);
lean_dec_ref(v___f_3263_);
if (lean_obj_tag(v_result_x3f_3307_) == 0)
{
lean_dec_ref(v___x_3262_);
v___y_3281_ = v___y_3264_;
goto v___jp_3280_;
}
else
{
lean_object* v_val_3310_; lean_object* v_processedSnap_3311_; lean_object* v___x_3312_; 
v_val_3310_ = lean_ctor_get(v_result_x3f_3307_, 0);
lean_inc(v_val_3310_);
lean_dec_ref_known(v_result_x3f_3307_, 1);
v_processedSnap_3311_ = lean_ctor_get(v_val_3310_, 1);
lean_inc_ref(v_processedSnap_3311_);
lean_dec(v_val_3310_);
v___x_3312_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3262_, v_processedSnap_3311_);
v___y_3281_ = v___y_3264_;
goto v___jp_3280_;
}
}
else
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
lean_dec(v___x_3279_);
lean_del_object(v___x_3276_);
lean_dec(v_snd_3274_);
lean_del_object(v___x_3269_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_setupImports_3260_);
lean_dec_ref(v_toProcessingContext_3259_);
lean_inc_ref(v___y_3264_);
v___x_3313_ = lean_apply_5(v___f_3263_, v_val_3302_, v_fst_3272_, v_fst_3273_, v___y_3264_, lean_box(0));
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3313_);
v___x_3315_ = v___x_3304_;
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
else
{
lean_dec_ref(v___f_3263_);
lean_dec_ref(v___x_3262_);
lean_dec(v_old_x3f_3261_);
v___y_3281_ = v___y_3264_;
goto v___jp_3280_;
}
v___jp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3282_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3274_);
lean_inc(v_fst_3273_);
lean_inc(v_fst_3272_);
v___x_3283_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3260_, v___x_3279_, v_fst_3272_, v_fst_3273_, v___y_3281_);
v___x_3284_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3285_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_unsigned_to_nat(32u);
v___x_3288_ = lean_mk_empty_array_with_capacity(v___x_3287_);
lean_dec_ref(v___x_3288_);
v___x_3289_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 1, v___x_3283_);
v___x_3291_ = v___x_3276_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_fst_3273_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3283_);
v___x_3291_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3293_, 0, v___x_3284_);
lean_ctor_set(v___x_3293_, 1, v___x_3285_);
lean_ctor_set(v___x_3293_, 2, v___x_3286_);
lean_ctor_set(v___x_3293_, 3, v___x_3289_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*4, v___x_3278_);
lean_inc(v_fst_3272_);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v_fst_3272_);
v___x_3295_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3295_, 0, v___x_3284_);
lean_ctor_set(v___x_3295_, 1, v___x_3282_);
lean_ctor_set(v___x_3295_, 2, v___x_3286_);
lean_ctor_set(v___x_3295_, 3, v___x_3289_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*4, v___x_3278_);
v___x_3296_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3294_, v___x_3295_);
v___x_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3293_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
lean_ctor_set(v___x_3297_, 2, v_toProcessingContext_3259_);
lean_ctor_set(v___x_3297_, 3, v_fst_3272_);
lean_ctor_set(v___x_3297_, 4, v___x_3292_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3297_);
v___x_3299_ = v___x_3269_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
lean_del_object(v___x_3276_);
lean_dec(v_fst_3273_);
lean_dec_ref(v___f_3263_);
lean_dec_ref(v___x_3262_);
lean_dec(v_old_x3f_3261_);
lean_dec_ref(v_setupImports_3260_);
v___x_3318_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3274_);
v___x_3319_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3320_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3321_ = lean_box(0);
v___x_3322_ = lean_unsigned_to_nat(32u);
v___x_3323_ = lean_mk_empty_array_with_capacity(v___x_3322_);
lean_dec_ref(v___x_3323_);
v___x_3324_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3325_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3325_, 0, v___x_3319_);
lean_ctor_set(v___x_3325_, 1, v___x_3320_);
lean_ctor_set(v___x_3325_, 2, v___x_3321_);
lean_ctor_set(v___x_3325_, 3, v___x_3324_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*4, v___x_3278_);
lean_inc(v_fst_3272_);
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_fst_3272_);
v___x_3327_ = 0;
v___x_3328_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3328_, 0, v___x_3319_);
lean_ctor_set(v___x_3328_, 1, v___x_3318_);
lean_ctor_set(v___x_3328_, 2, v___x_3321_);
lean_ctor_set(v___x_3328_, 3, v___x_3324_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*4, v___x_3327_);
v___x_3329_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3326_, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3325_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
lean_ctor_set(v___x_3330_, 2, v_toProcessingContext_3259_);
lean_ctor_set(v___x_3330_, 3, v_fst_3272_);
lean_ctor_set(v___x_3330_, 4, v___x_3321_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3330_);
v___x_3332_ = v___x_3269_;
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
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___f_3263_);
lean_dec_ref(v___x_3262_);
lean_dec(v_old_x3f_3261_);
lean_dec_ref(v_setupImports_3260_);
lean_dec_ref(v_toProcessingContext_3259_);
v_a_3336_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3266_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3266_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3344_, lean_object* v_setupImports_3345_, lean_object* v_old_x3f_3346_, lean_object* v___x_3347_, lean_object* v___f_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3344_, v_setupImports_3345_, v_old_x3f_3346_, v___x_3347_, v___f_3348_, v___y_3349_);
lean_dec_ref(v___y_3349_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3352_, lean_object* v_toProcessingContext_3353_, lean_object* v_x_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3355_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3352_);
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3358_, 0, v_x_3354_);
lean_ctor_set(v___x_3358_, 1, v___x_3355_);
lean_ctor_set(v___x_3358_, 2, v_toProcessingContext_3353_);
lean_ctor_set(v___x_3358_, 3, v___x_3356_);
lean_ctor_set(v___x_3358_, 4, v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3359_, lean_object* v_old_x3f_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_toProcessingContext_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___f_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; 
v_toProcessingContext_3363_ = lean_ctor_get(v_a_3361_, 0);
v___x_3364_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___x_3365_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
lean_inc_ref(v_a_3361_);
lean_inc_ref_n(v_toProcessingContext_3363_, 3);
v___f_3366_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3366_, 0, v_toProcessingContext_3363_);
lean_closure_set(v___f_3366_, 1, v_a_3361_);
lean_inc(v_old_x3f_3360_);
v___f_3367_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 7, 5);
lean_closure_set(v___f_3367_, 0, v_toProcessingContext_3363_);
lean_closure_set(v___f_3367_, 1, v_setupImports_3359_);
lean_closure_set(v___f_3367_, 2, v_old_x3f_3360_);
lean_closure_set(v___f_3367_, 3, v___x_3365_);
lean_closure_set(v___f_3367_, 4, v___f_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3368_, 0, v___x_3364_);
lean_closure_set(v___f_3368_, 1, v_toProcessingContext_3363_);
if (lean_obj_tag(v_old_x3f_3360_) == 1)
{
lean_object* v_val_3369_; lean_object* v_result_x3f_3370_; 
v_val_3369_ = lean_ctor_get(v_old_x3f_3360_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v_old_x3f_3360_, 1);
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
v___x_3381_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
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
v___x_3387_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3386_, v_a_3361_);
lean_dec(v_pos_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3388_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
return v___x_3388_;
}
else
{
lean_object* v_parserState_3389_; lean_object* v___x_3390_; 
lean_dec_ref(v___f_3368_);
lean_dec_ref(v___f_3367_);
v_parserState_3389_ = lean_ctor_get(v_val_3372_, 0);
lean_inc_ref(v_parserState_3389_);
lean_inc_ref(v_toProcessingContext_3363_);
v___x_3390_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3363_, v_a_3361_, v_val_3369_, v_stx_3371_, v_parserState_3389_, v_a_3361_);
return v___x_3390_;
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v___x_3383_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3391_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
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
v___x_3392_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
return v___x_3392_;
}
}
else
{
lean_object* v___x_3393_; 
lean_dec(v_val_3375_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3393_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
return v___x_3393_;
}
}
else
{
lean_object* v___x_3394_; 
lean_dec(v___x_3374_);
lean_dec(v_stx_3371_);
lean_dec(v_val_3369_);
v___x_3394_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
return v___x_3394_;
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v_val_3369_);
v___x_3395_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3396_; 
lean_dec(v_old_x3f_3360_);
v___x_3396_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3368_, v___f_3367_, v_a_3361_);
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
v___x_3537_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3);
v___x_3538_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3534_, v_resultSnap_3536_);
v___x_3539_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3540_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4);
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
